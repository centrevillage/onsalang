//! `onsa fmt` (`docs/onsa-tools.md` §3, S-07, T1-9): prints the AST back in the single
//! canonical form. Line structure the author chose (one-line vs multi-line
//! blocks, line breaks inside lists and chains, blank lines up to one) is
//! kept; everything else (spacing, indentation, trailing commas, alignment
//! of `=` in `let` runs and of trailing comments) is normalized.

use onsa_diag::Span;

use crate::ast::*;
use crate::parser::Parsed;
use crate::token::{Token, TokenKind};

/// Format a parsed file. Returns `None` if the lexer or the parser reported a
/// diagnostic (`Parsed::syntax_errors()`, R-146, S-214); the diagnostics of later
/// stages (E0320 of the names stage) do not block formatting (§18.2, S-120).
pub fn format(parsed: &Parsed, text: &str) -> Option<String> {
    if parsed.syntax_errors() {
        return None;
    }
    let comments: Vec<Token> = parsed
        .cst
        .tokens()
        .iter()
        .copied()
        .filter(|t| matches!(t.kind, TokenKind::Comment | TokenKind::DocComment))
        .collect();
    let mut line_starts = vec![0u32];
    for (i, b) in text.bytes().enumerate() {
        if b == b'\n' {
            line_starts.push(i as u32 + 1);
        }
    }
    let mut f = Fmt {
        ast: &parsed.ast,
        text,
        line_starts,
        comments,
        next_comment: 0,
        out: String::new(),
        indent: 0,
        line_idx: 0,
        let_marks: Vec::new(),
        comment_marks: Vec::new(),
    };
    f.file();
    Some(f.finish())
}

/// One element of a delimited list: its source span and how to print it.
type Elem<'b, 'a> = (Span, Box<dyn Fn(&mut Fmt<'a>) + 'b>);

struct Fmt<'a> {
    ast: &'a Ast,
    text: &'a str,
    line_starts: Vec<u32>,
    comments: Vec<Token>,
    next_comment: usize,
    out: String,
    indent: usize,
    /// Number of `\n` written so far (index of the current output line).
    line_idx: usize,
    /// `(line, column of ` = `)` for single-line `let` / `var` without annotation (S-07).
    let_marks: Vec<(usize, usize)>,
    /// `(line, comment text, author's column)` for trailing comments (S-07).
    comment_marks: Vec<(usize, String, usize)>,
}

impl<'a> Fmt<'a> {
    // ------------------------------------------------------------ source geometry

    fn line_of(&self, offset: u32) -> usize {
        match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        }
    }

    fn col_of(&self, offset: u32) -> usize {
        let start = self.line_starts[self.line_of(offset)] as usize;
        self.text[start..offset as usize].chars().count()
    }

    fn src(&self, span: Span) -> &'a str {
        &self.text[span.start as usize..span.end as usize]
    }

    /// Offset of the next `ch` at or after `from` (skipping only whitespace and comments is
    /// not needed: callers know the character comes before any other token).
    fn find_char(&self, from: u32, ch: char) -> u32 {
        let rel = self.text[from as usize..].find(ch).unwrap_or(0);
        from + rel as u32
    }

    /// Number of blank lines (0 or 1) the author left between two offsets.
    fn blank_between(&self, a: u32, b: u32) -> usize {
        if b <= a {
            return 0;
        }
        let n = self.text[a as usize..b as usize].bytes().filter(|&c| c == b'\n').count();
        usize::from(n >= 2)
    }

    // ------------------------------------------------------------ output

    fn cur_col(&self) -> usize {
        match self.out.rfind('\n') {
            Some(i) => self.out[i + 1..].chars().count(),
            None => self.out.chars().count(),
        }
    }

    fn push(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn newline(&mut self) {
        // Drop trailing spaces of the line being closed.
        while self.out.ends_with(' ') {
            self.out.pop();
        }
        self.out.push('\n');
        self.line_idx += 1;
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    fn blank_line(&mut self) {
        while self.out.ends_with(' ') {
            self.out.pop();
        }
        self.out.push('\n');
        self.line_idx += 1;
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    /// Pad the current line to `col` (at least one space).
    fn pad_to(&mut self, col: usize) {
        let cur = self.cur_col();
        let n = if col > cur { col - cur } else { 1 };
        for _ in 0..n {
            self.out.push(' ');
        }
    }

    // ------------------------------------------------------------ comments

    /// Emit full-line comments that start before `pos`. `prev_end` is where the
    /// previous code or comment ended; `first` suppresses a blank line before
    /// the first line of a container.
    fn leading_comments(&mut self, pos: u32, prev_end: &mut u32, first: &mut bool) {
        while self.next_comment < self.comments.len() && self.comments[self.next_comment].span.start < pos {
            let c = self.comments[self.next_comment];
            self.next_comment += 1;
            if !*first && self.blank_between(*prev_end, c.span.start) == 1 {
                self.blank_line();
            }
            if !*first {
                // continue on the current (fresh) line
            }
            let text = self.src(c.span).trim_end().to_string();
            self.push(&text);
            self.newline();
            *prev_end = c.span.end;
            *first = false;
        }
    }

    /// Emit a trailing comment on the current line if one follows `end` on the same source line.
    fn trailing_comment(&mut self, end: u32) {
        if self.next_comment >= self.comments.len() {
            return;
        }
        let c = self.comments[self.next_comment];
        if c.span.start < end {
            // A comment inside the node that no line point consumed: keep it as a trailer.
        } else if self.text[end as usize..c.span.start as usize].contains('\n') {
            return;
        }
        self.next_comment += 1;
        let text = self.src(c.span).trim_end().to_string();
        let author_col = self.col_of(c.span.start);
        let line = self.line_idx;
        self.push(" ");
        self.push(&text);
        self.comment_marks.push((line, text, author_col));
    }

    /// Emit every comment left before `pos` (end of a container), each on its own line.
    fn flush_comments_before(&mut self, pos: u32, prev_end: &mut u32, first: &mut bool) {
        self.leading_comments(pos, prev_end, first);
    }

    // ------------------------------------------------------------ file and containers

    fn file(&mut self) {
        let mut prev_end = 0u32;
        let mut first = true;
        for &id in &self.ast.root {
            let span = self.ast.item(id).span;
            self.leading_comments(span.start, &mut prev_end, &mut first);
            if !first && self.blank_between(prev_end, span.start) == 1 {
                self.blank_line();
            }
            self.item(id);
            self.trailing_comment(span.end);
            self.newline();
            prev_end = span.end;
            first = false;
        }
        let end = self.text.len() as u32;
        self.flush_comments_before(end + 1, &mut prev_end, &mut first);
    }

    /// `{ items }` of impl / trait / effect / handler / extern / inline handler.
    /// `open` is the offset of `{`, `close` the offset of `}`.
    fn item_container(&mut self, items: &[ItemId], open: u32, close: u32) {
        if items.is_empty() {
            self.push("{}");
            return;
        }
        if self.line_of(open) == self.line_of(close) && items.len() == 1 {
            self.push("{ ");
            self.item(items[0]);
            self.push(" }");
            return;
        }
        self.push("{");
        self.indent += 1;
        self.newline();
        let mut prev_end = open + 1;
        let mut first = true;
        for &id in items {
            let span = self.ast.item(id).span;
            self.leading_comments(span.start, &mut prev_end, &mut first);
            if !first && self.blank_between(prev_end, span.start) == 1 {
                self.blank_line();
            }
            self.item(id);
            self.trailing_comment(span.end);
            self.newline();
            prev_end = span.end;
            first = false;
        }
        self.flush_comments_before(close, &mut prev_end, &mut first);
        self.indent -= 1;
        self.trim_line();
        self.push("}");
    }

    /// Remove the indentation written by the last `newline` so `}` goes at the outer indent.
    fn trim_line(&mut self) {
        while self.out.ends_with(' ') {
            self.out.pop();
        }
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    // ------------------------------------------------------------ items

    fn vis(&mut self, v: Vis) {
        match v {
            Vis::Private => {}
            Vis::Pkg => self.push("pub(pkg) "),
            Vis::Pub => self.push("pub "),
        }
    }

    fn item(&mut self, id: ItemId) {
        let item = self.ast.item(id);
        for a in &item.attrs {
            self.attr(a);
            self.newline();
        }
        self.vis(item.vis);
        self.item_kind(&item.kind, item.span);
    }

    fn item_kind(&mut self, kind: &ItemKind, span: Span) {
        match kind {
            ItemKind::Fn(f) => self.fn_decl(f),
            ItemKind::Flow(f) => {
                self.push("flow ");
                self.push(&f.name.name);
                self.params(&f.params, f.name.span.end);
                self.push(" -> ");
                self.ty(f.ret);
                self.push(" ");
                self.block(f.body, false);
            }
            ItemKind::Struct(s) => {
                self.push("struct ");
                self.push(&s.name.name);
                self.generics(&s.generics);
                match &s.kind {
                    StructKind::Named(fields) => {
                        self.push(" ");
                        let open = self.find_char(s.name.span.end, '{');
                        let items: Vec<Elem<'_, 'a>> = fields
                            .iter()
                            .map(|f| {
                                (
                                    f.span,
                                    Box::new(move |p: &mut Self| {
                                        p.vis(f.vis);
                                        p.push(&f.name.name);
                                        p.push(": ");
                                        p.ty(f.ty);
                                    }) as Box<dyn Fn(&mut Self)>,
                                )
                            })
                            .collect();
                        self.list("{", "}", open, span.end - 1, &items, true);
                    }
                    StructKind::Tuple(t) => {
                        self.push("(");
                        self.ty(*t);
                        self.push(")");
                    }
                }
            }
            ItemKind::Enum(e) => {
                self.push("enum ");
                self.push(&e.name.name);
                self.generics(&e.generics);
                self.push(" ");
                let open = self.find_char(e.name.span.end, '{');
                let items: Vec<Elem<'_, 'a>> = e
                    .variants
                    .iter()
                    .map(|v| {
                        (
                            v.span,
                            Box::new(move |p: &mut Self| {
                                p.push(&v.name.name);
                                if !v.fields.is_empty() {
                                    p.push("(");
                                    for (i, &t) in v.fields.iter().enumerate() {
                                        if i > 0 {
                                            p.push(", ");
                                        }
                                        p.ty(t);
                                    }
                                    p.push(")");
                                }
                            }) as Box<dyn Fn(&mut Self)>,
                        )
                    })
                    .collect();
                self.list("{", "}", open, span.end - 1, &items, true);
            }
            ItemKind::TypeAlias { name, ty } => {
                self.push("type ");
                self.push(&name.name);
                self.push(" = ");
                self.ty(*ty);
            }
            ItemKind::OpaqueType { name } => {
                self.push("type ");
                self.push(&name.name);
            }
            ItemKind::Trait(t) => {
                self.push("trait ");
                self.push(&t.name.name);
                self.generics(&t.generics);
                self.push(" ");
                let open = self.find_char(t.name.span.end, '{');
                self.item_container(&t.items, open, span.end - 1);
            }
            ItemKind::Impl(i) => {
                self.push("impl");
                self.generics(&i.generics);
                self.push(" ");
                let mut after = self.ast.ty(i.self_ty).span.end;
                if let Some(tr) = &i.trait_ {
                    self.path(tr);
                    self.push(" for ");
                    after = after.max(tr.span.end);
                }
                self.ty(i.self_ty);
                self.push(" ");
                let open = self.find_char(after, '{');
                self.item_container(&i.items, open, span.end - 1);
            }
            ItemKind::Effect(e) => {
                if e.blocking {
                    self.push("blocking ");
                }
                self.push("effect ");
                self.push(&e.name.name);
                self.push(" ");
                let open = self.find_char(e.name.span.end, '{');
                self.item_container(&e.ops, open, span.end - 1);
            }
            ItemKind::Handler(h) => {
                self.push("handler ");
                self.push(&h.name.name);
                if !h.params.is_empty() {
                    self.params(&h.params, h.name.span.end);
                }
                self.push(": ");
                self.path(&h.effect);
                self.push(" ");
                let open = self.find_char(h.effect.span.end, '{');
                self.item_container(&h.items, open, span.end - 1);
            }
            ItemKind::Const(c) => {
                self.push("const ");
                self.push(&c.name.name);
                self.push(": ");
                self.ty(c.ty);
                if let Some(v) = c.value {
                    self.push(" = ");
                    self.expr(v);
                }
            }
            ItemKind::Use(u) => {
                self.push("use ");
                self.path(&u.path);
                if let Some(names) = &u.names {
                    self.push(".{");
                    for (i, n) in names.iter().enumerate() {
                        if i > 0 {
                            self.push(", ");
                        }
                        self.push(&n.name);
                    }
                    self.push("}");
                }
            }
            ItemKind::Extern(e) => {
                self.push("extern ");
                self.push(self.src(e.abi.span));
                self.push(" lib ");
                self.push(self.src(e.lib.span));
                self.push(" ");
                let open = self.find_char(e.lib.span.end, '{');
                self.item_container(&e.items, open, span.end - 1);
            }
            ItemKind::Target(inner) => {
                self.push("target ");
                self.item_kind(inner, span);
            }
            ItemKind::Test { name, body } => {
                self.push("test ");
                self.push(self.src(name.span));
                self.push(" ");
                self.block(*body, false);
            }
        }
    }

    fn fn_decl(&mut self, f: &FnDecl) {
        if f.rt {
            self.push("rt ");
        }
        self.push("fn ");
        self.push(&f.name.name);
        self.generics(&f.generics);
        self.params(&f.params, f.name.span.end);
        if let Some(r) = f.ret {
            self.push(" -> ");
            self.ty(r);
        }
        if let Some(e) = &f.effects {
            self.effect_row(e);
        }
        if let Some(b) = f.body {
            self.push(" ");
            self.block(b, true);
        }
    }

    fn attr(&mut self, a: &Attr) {
        self.push("@");
        self.push(&a.name.name);
        if !a.args.is_empty() {
            self.push("(");
            for (i, arg) in a.args.iter().enumerate() {
                if i > 0 {
                    self.push(", ");
                }
                match arg {
                    AttrArg::Named { key, value } => {
                        self.push(&key.name);
                        self.push(": ");
                        self.expr(*value);
                    }
                    AttrArg::Path(p) => self.path(p),
                    AttrArg::Str(s) => self.push(self.src(s.span)),
                }
            }
            self.push(")");
        }
    }

    fn generics(&mut self, gs: &[GenericParam]) {
        if gs.is_empty() {
            return;
        }
        self.push("[");
        for (i, g) in gs.iter().enumerate() {
            if i > 0 {
                self.push(", ");
            }
            match g {
                GenericParam::Type { name, bounds } => {
                    self.push(&name.name);
                    if !bounds.is_empty() {
                        self.push(": ");
                        for (j, b) in bounds.iter().enumerate() {
                            if j > 0 {
                                self.push(" + ");
                            }
                            if b.relaxed {
                                self.push("?");
                            }
                            self.path(&b.path);
                        }
                    }
                }
                GenericParam::Const { name, ty } => {
                    self.push("const ");
                    self.push(&name.name);
                    self.push(": ");
                    self.ty(*ty);
                }
                GenericParam::Effect { name } => self.push(&name.name),
            }
        }
        self.push("]");
    }

    /// `(params)`; `after` is an offset before the `(`.
    fn params(&mut self, params: &[Param], after: u32) {
        let open = self.find_char(after, '(');
        let close =
            if let Some(last) = params.last() { self.find_char(last.span.end, ')') } else { self.find_char(open, ')') };
        let items: Vec<Elem<'_, 'a>> = params
            .iter()
            .map(|p| (p.span, Box::new(move |f: &mut Self| f.param(p)) as Box<dyn Fn(&mut Self)>))
            .collect();
        self.list("(", ")", open, close, &items, true);
    }

    fn param(&mut self, p: &Param) {
        for a in &p.attrs {
            self.attr(a);
            // In a block-style list the attribute goes on its own line (§17.4); inline otherwise.
            if self.line_of(a.span.end) < self.line_of(p.span.end) {
                self.newline();
            } else {
                self.push(" ");
            }
        }
        self.mode(p.mode);
        match &p.name {
            ParamName::Ident(id) => self.push(&id.name),
            ParamName::Wild(_) => self.push("_"),
            ParamName::SelfParam(_) => self.push("self"),
        }
        if let Some(t) = p.ty {
            self.push(": ");
            self.ty(t);
        }
    }

    fn mode(&mut self, m: Mode) {
        match m {
            Mode::Borrow => {}
            Mode::Inout => self.push("inout "),
            Mode::Move => self.push("move "),
        }
    }

    fn effect_row(&mut self, e: &EffectRow) {
        self.push(" uses {");
        for (i, p) in e.effects.iter().enumerate() {
            if i > 0 {
                self.push(", ");
            }
            self.path(p);
        }
        self.push("}");
    }

    fn path(&mut self, p: &Path) {
        self.path_with_args(p, &[]);
    }

    /// A path with the `::[…]` written after its names (a struct literal).
    fn path_with_args(&mut self, p: &Path, lists: &[(usize, TypeArgList)]) {
        for (i, s) in p.segments.iter().enumerate() {
            if i > 0 {
                self.push(".");
            }
            self.push(&s.name);
            for (_, l) in lists.iter().filter(|(at, _)| *at == i) {
                self.type_arg_list(l);
            }
        }
    }

    /// `::[A, B]` (§4.5, docs/onsa-tools.md §3.2): no space around `::[`, the
    /// elements as in a type's list.
    fn type_arg_list(&mut self, l: &TypeArgList) {
        self.push("::[");
        for (i, &a) in l.args.iter().enumerate() {
            if i > 0 {
                self.push(", ");
            }
            self.ty(a);
        }
        self.push("]");
    }

    // ------------------------------------------------------------ types

    fn ty(&mut self, id: TypeId) {
        let t = self.ast.ty(id);
        match &t.kind {
            TypeKind::Error => onsa_diag::internal::bug(Some(t.span), "fmt met a type a syntax error left unread"),
            TypeKind::Path { path, args } => {
                self.path(path);
                if !args.is_empty() {
                    self.push("[");
                    for (i, &a) in args.iter().enumerate() {
                        if i > 0 {
                            self.push(", ");
                        }
                        self.ty(a);
                    }
                    self.push("]");
                }
            }
            TypeKind::Array { elem, len } => {
                self.push("[");
                self.ty(*elem);
                self.push("; ");
                self.expr(*len);
                self.push("]");
            }
            TypeKind::ConstArg(e) => self.expr(*e),
            TypeKind::Unit => self.push("()"),
            TypeKind::Tuple(ts) => {
                self.push("(");
                for (i, &a) in ts.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.ty(a);
                }
                self.push(")");
            }
            TypeKind::Fn { rt, params, ret, effects } => {
                if *rt {
                    self.push("rt ");
                }
                self.push("fn(");
                for (i, (m, t)) in params.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.mode(*m);
                    self.ty(*t);
                }
                self.push(")");
                if let Some(r) = ret {
                    self.push(" -> ");
                    self.ty(*r);
                }
                if let Some(e) = effects {
                    self.effect_row(e);
                }
            }
        }
    }

    // ------------------------------------------------------------ lists

    /// Print a delimited list keeping the author's layout (T1-9):
    /// inline when every element starts on the opener's line; block style (one
    /// indent level, trailing comma, closer on its own line) when the opener is
    /// followed by a line break; visual style (continuation lines aligned under
    /// the first element, no trailing comma) otherwise.
    fn list(
        &mut self,
        open_s: &str,
        close_s: &str,
        open: u32,
        _close: u32,
        items: &[Elem<'_, 'a>],
        spaced_braces: bool,
    ) {
        let brace = open_s == "{";
        if items.is_empty() {
            self.push(open_s);
            self.push(close_s);
            return;
        }
        let open_line = self.line_of(open);
        let first_line = self.line_of(items[0].0.start);
        if first_line > open_line {
            // Block style.
            self.push(open_s);
            self.indent += 1;
            self.newline();
            let mut prev_end_line = first_line;
            for (i, (span, print)) in items.iter().enumerate() {
                let line = self.line_of(span.start);
                if i > 0 {
                    if line > prev_end_line {
                        self.push(",");
                        self.newline();
                    } else {
                        self.push(", ");
                    }
                }
                print(self);
                prev_end_line = self.line_of(span.end);
            }
            self.push(",");
            self.indent -= 1;
            self.newline();
            self.push(close_s);
            return;
        }
        let multi = items.iter().any(|(s, _)| self.line_of(s.start) > open_line);
        self.push(open_s);
        if brace && spaced_braces {
            self.push(" ");
        }
        let col = self.cur_col();
        let mut prev_end_line = open_line;
        for (i, (span, print)) in items.iter().enumerate() {
            let line = self.line_of(span.start);
            if i > 0 {
                if multi && line > prev_end_line {
                    self.push(",");
                    self.newline();
                    self.trim_line();
                    self.pad_to(col);
                } else {
                    self.push(", ");
                }
            }
            print(self);
            prev_end_line = self.line_of(span.end);
        }
        if brace && spaced_braces {
            self.push(" ");
        }
        self.push(close_s);
    }

    // ------------------------------------------------------------ blocks and statements

    /// `{ ... }`. One-line if the author wrote it on one line (`docs/onsa-tools.md` §3.2).
    /// `fn_top` enables trailing-`return` removal (§6.1).
    fn block(&mut self, id: ExprId, fn_top: bool) {
        let e = self.ast.expr(id);
        let ExprKind::Block(b) = &e.kind else {
            self.expr(id);
            return;
        };
        let open = e.span.start;
        let close = e.span.end - 1;
        let mut stmts = b.stmts.clone();
        let mut tail = b.tail;
        if fn_top && tail.is_none() {
            if let Some(&last) = stmts.last() {
                if let StmtKind::Return(Some(v)) = self.ast.stmt(last).kind {
                    stmts.pop();
                    tail = Some(v);
                }
            }
        }
        if stmts.is_empty() && tail.is_none() {
            self.push("{}");
            return;
        }
        if self.line_of(open) == self.line_of(close) {
            self.push("{ ");
            for &s in &stmts {
                self.stmt(s);
                self.push(" ");
            }
            if let Some(t) = tail {
                self.expr(t);
                self.push(" ");
            }
            self.trim_line_end();
            self.push(" }");
            return;
        }
        self.push("{");
        self.indent += 1;
        self.newline();
        let mut prev_end = open + 1;
        let mut first = true;
        for &s in &stmts {
            let span = self.ast.stmt(s).span;
            self.leading_comments(span.start, &mut prev_end, &mut first);
            if !first && self.blank_between(prev_end, span.start) == 1 {
                self.blank_line();
            }
            self.stmt(s);
            self.trailing_comment(span.end);
            self.newline();
            prev_end = span.end;
            first = false;
        }
        if let Some(t) = tail {
            let span = self.ast.expr(t).span;
            self.leading_comments(span.start, &mut prev_end, &mut first);
            if !first && self.blank_between(prev_end, span.start) == 1 {
                self.blank_line();
            }
            self.expr(t);
            self.trailing_comment(span.end);
            self.newline();
            prev_end = span.end;
            first = false;
        }
        self.flush_comments_before(close, &mut prev_end, &mut first);
        self.indent -= 1;
        self.trim_line();
        self.push("}");
    }

    fn trim_line_end(&mut self) {
        while self.out.ends_with(' ') {
            self.out.pop();
        }
    }

    fn stmt(&mut self, id: StmtId) {
        let s = self.ast.stmt(id);
        match &s.kind {
            StmtKind::Let { pat, ty, init } => {
                let line = self.line_idx;
                self.push("let ");
                self.pat(*pat);
                if let Some(t) = ty {
                    self.push(": ");
                    self.ty(*t);
                }
                let col = self.cur_col();
                self.push(" = ");
                self.expr(*init);
                if ty.is_none() && self.line_idx == line {
                    self.let_marks.push((line, col));
                }
            }
            StmtKind::Var { name, ty, init } => {
                let line = self.line_idx;
                self.push("var ");
                self.push(&name.name);
                if let Some(t) = ty {
                    self.push(": ");
                    self.ty(*t);
                }
                let col = self.cur_col();
                self.push(" = ");
                self.expr(*init);
                if ty.is_none() && self.line_idx == line {
                    self.let_marks.push((line, col));
                }
            }
            StmtKind::Assign { target, value } => {
                self.expr(*target);
                self.push(" = ");
                self.expr(*value);
            }
            StmtKind::For { pat, moved, iter, body } => {
                self.push("for ");
                self.pat(*pat);
                self.push(" in ");
                if *moved {
                    self.push("move ");
                }
                self.expr(*iter);
                self.push(" ");
                self.block(*body, false);
            }
            StmtKind::While { cond, body } => {
                self.push("while ");
                self.expr(*cond);
                self.push(" ");
                self.block(*body, false);
            }
            StmtKind::Break => self.push("break"),
            StmtKind::Continue => self.push("continue"),
            StmtKind::Return(v) => {
                self.push("return");
                if let Some(v) = v {
                    self.push(" ");
                    self.expr(*v);
                }
            }
            StmtKind::Assert(e) => {
                self.push("assert ");
                self.expr(*e);
            }
            StmtKind::Expr(e) => self.expr(*e),
        }
    }

    // ------------------------------------------------------------ expressions

    fn expr(&mut self, id: ExprId) {
        let e = self.ast.expr(id);
        match &e.kind {
            ExprKind::Lit(l) => match l {
                Lit::Int { text, .. } | Lit::Float { text } => self.push(text),
                Lit::Bool(b) => self.push(if *b { "true" } else { "false" }),
                Lit::Char(_) => self.push(self.src(e.span)),
                Lit::Str(s) => self.push(self.src(s.span)),
            },
            ExprKind::Path(p) => self.path(p),
            ExprKind::Hole => self.push("_"),
            ExprKind::Error => onsa_diag::internal::bug(Some(e.span), "fmt met a body a syntax error left unread"),
            ExprKind::Paren(inner) => {
                self.push("(");
                self.expr(*inner);
                self.push(")");
            }
            ExprKind::Move(inner) => {
                self.push("move ");
                self.expr(*inner);
            }
            ExprKind::Tuple(items) => {
                let items: Vec<Elem<'_, 'a>> = items
                    .iter()
                    .map(|&x| {
                        (self.ast.expr(x).span, Box::new(move |f: &mut Self| f.expr(x)) as Box<dyn Fn(&mut Self)>)
                    })
                    .collect();
                self.list("(", ")", e.span.start, e.span.end - 1, &items, false);
            }
            ExprKind::Array(items) => {
                let items: Vec<Elem<'_, 'a>> = items
                    .iter()
                    .map(|&x| {
                        (self.ast.expr(x).span, Box::new(move |f: &mut Self| f.expr(x)) as Box<dyn Fn(&mut Self)>)
                    })
                    .collect();
                self.list("[", "]", e.span.start, e.span.end - 1, &items, false);
            }
            ExprKind::Repeat { elem, len } => {
                self.push("[");
                self.expr(*elem);
                self.push("; ");
                self.expr(*len);
                self.push("]");
            }
            ExprKind::Struct { path, type_args, fields } => {
                self.path_with_args(path, type_args);
                self.push(" ");
                let open = self.find_char(path.span.end, '{');
                let items: Vec<Elem<'_, 'a>> = fields
                    .iter()
                    .map(|(name, x)| {
                        let span = name.span.to(self.ast.expr(*x).span);
                        (
                            span,
                            Box::new(move |f: &mut Self| {
                                f.push(&name.name);
                                f.push(": ");
                                f.expr(*x);
                            }) as Box<dyn Fn(&mut Self)>,
                        )
                    })
                    .collect();
                self.list("{", "}", open, e.span.end - 1, &items, true);
            }
            ExprKind::Block(_) => self.block(id, false),
            ExprKind::If { cond, then, else_ } => {
                self.push("if ");
                self.expr(*cond);
                self.push(" ");
                self.block(*then, false);
                if let Some(el) = else_ {
                    self.push(" else ");
                    let el_e = self.ast.expr(*el);
                    if matches!(el_e.kind, ExprKind::If { .. }) {
                        self.expr(*el);
                    } else {
                        self.block(*el, false);
                    }
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.push("match ");
                self.expr(*scrutinee);
                self.push(" ");
                let open = self.find_char(self.ast.expr(*scrutinee).span.end, '{');
                let items: Vec<Elem<'_, 'a>> = arms
                    .iter()
                    .map(|arm| {
                        (
                            arm.span,
                            Box::new(move |f: &mut Self| {
                                f.pat(arm.pat);
                                if let Some(g) = arm.guard {
                                    f.push(" if ");
                                    f.expr(g);
                                }
                                f.push(" => ");
                                f.expr(arm.body);
                            }) as Box<dyn Fn(&mut Self)>,
                        )
                    })
                    .collect();
                self.list("{", "}", open, e.span.end - 1, &items, true);
            }
            ExprKind::Closure { params, ret, effects, body } => {
                self.push("fn");
                self.params(params, e.span.start + 2);
                if let Some(r) = ret {
                    self.push(" -> ");
                    self.ty(*r);
                }
                if let Some(ef) = effects {
                    self.effect_row(ef);
                }
                self.push(" ");
                self.block(*body, false);
            }
            ExprKind::Handle { body, with } => {
                self.push("handle ");
                self.block(*body, false);
                self.push(" with ");
                match with {
                    HandlerRef::Named { path, args } => {
                        self.path(path);
                        if !args.is_empty() {
                            self.args(args, path.span.end);
                        }
                    }
                    HandlerRef::Inline { effect, items } => {
                        self.path(effect);
                        self.push(" ");
                        let open = self.find_char(effect.span.end, '{');
                        self.item_container(items, open, e.span.end - 1);
                    }
                }
            }
            ExprKind::Unsafe(b) => {
                self.push("unsafe ");
                self.block(*b, false);
            }
            ExprKind::Par { var, range, body } => {
                self.push("par ");
                self.push(&var.name);
                self.push(" in ");
                self.range(range);
                self.push(" ");
                self.block(*body, false);
            }
            ExprKind::Binary { operands, ops } => {
                self.expr(operands[0]);
                for (i, (op, op_span)) in ops.iter().enumerate() {
                    self.push(" ");
                    self.push(op.symbol());
                    let rhs = operands[i + 1];
                    let rhs_span = self.ast.expr(rhs).span;
                    if self.line_of(rhs_span.start) > self.line_of(op_span.end) {
                        // Author's break after the operator (§2.5): one extra level.
                        self.indent += 1;
                        self.newline();
                        self.indent -= 1;
                    } else {
                        self.push(" ");
                    }
                    self.expr(rhs);
                }
            }
            ExprKind::Cast { expr, ty } => {
                self.expr(*expr);
                self.push(" as ");
                self.ty(*ty);
            }
            ExprKind::Unary { op, expr } => {
                self.push(match op {
                    UnOp::Neg => "-",
                    UnOp::Not => "!",
                });
                self.expr(*expr);
            }
            ExprKind::Call { callee, kind, args } => {
                self.expr(*callee);
                let callee_end = self.ast.expr(*callee).span.end;
                match kind {
                    CallKind::Plain => {}
                    CallKind::Flow => self.push("~"),
                    CallKind::Bang => self.push("!"),
                }
                self.args(args, callee_end);
            }
            ExprKind::Field { base, name } => {
                self.expr(*base);
                self.dot_break(*base, name.span.start);
                self.push(".");
                self.push(&name.name);
            }
            ExprKind::TypeArgs { base, args } => {
                self.expr(*base);
                self.type_arg_list(args);
            }
            ExprKind::TupleIndex { base, index, index_span } => {
                self.expr(*base);
                self.dot_break(*base, index_span.start);
                self.push(".");
                self.push(&index.to_string());
            }
            ExprKind::Index { base, index } => {
                self.expr(*base);
                self.push("[");
                self.expr(*index);
                self.push("]");
            }
            ExprKind::Try(inner) => {
                self.expr(*inner);
                self.push("?");
            }
            ExprKind::Range(r) => self.range(r),
        }
    }

    /// A range: the canonical form of the spec's examples, with no space
    /// around the symbol (`0..<n + 1`, §3.1).
    // SPEC-GAP(S-334): the spec and onsa-tools.md §3.2 do not say the spaces
    // around the symbol, nor a break after it.
    fn range(&mut self, r: &RangeHead) {
        self.expr(r.lo);
        self.push(r.end.symbol());
        self.expr(r.hi);
    }

    /// A method chain continued on the next line with a leading `.` (§2.5).
    fn dot_break(&mut self, base: ExprId, name_start: u32) {
        let base_end = self.ast.expr(base).span.end;
        if self.line_of(name_start) > self.line_of(base_end) {
            self.indent += 1;
            self.newline();
            self.indent -= 1;
        }
    }

    fn args(&mut self, args: &[Arg], after: u32) {
        let open = self.find_char(after, '(');
        let close = if let Some(last) = args.last() { self.find_char(last.span.end, ')') } else { open + 1 };
        let items: Vec<Elem<'_, 'a>> = args
            .iter()
            .map(|a| {
                (
                    a.span,
                    Box::new(move |f: &mut Self| {
                        f.mode(a.mode);
                        f.expr(a.expr);
                    }) as Box<dyn Fn(&mut Self)>,
                )
            })
            .collect();
        self.list("(", ")", open, close, &items, false);
    }

    // ------------------------------------------------------------ patterns

    fn pat(&mut self, id: PatId) {
        let p = self.ast.pat(id);
        match &p.kind {
            PatKind::Wild => self.push("_"),
            PatKind::Bind(id) => self.push(&id.name),
            PatKind::Lit(_) => self.push(self.src(p.span)),
            // `-1`, `-(1)`: the parentheses are kept and the spaces between the tokens dropped,
            // as for the same expression (S-185). A comment inside is emitted once by the
            // comment points, like a comment inside the expression `-( // c` `1)`.
            PatKind::Neg(_) => {
                let packed = code_only(self.src(p.span));
                self.push(&packed);
            }
            PatKind::Path(path) => self.path(path),
            PatKind::TupleStruct { path, elems } => {
                self.path(path);
                self.push("(");
                for (i, &e) in elems.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.pat(e);
                }
                self.push(")");
            }
            PatKind::Tuple(elems) => {
                self.push("(");
                for (i, &e) in elems.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.pat(e);
                }
                self.push(")");
            }
            PatKind::Struct { path, fields } => {
                self.path(path);
                self.push(" { ");
                for (i, (name, f)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.push(", ");
                    }
                    self.push(&name.name);
                    self.push(": ");
                    self.pat(*f);
                }
                self.push(" }");
            }
            PatKind::Or(alts) => {
                for (i, &a) in alts.iter().enumerate() {
                    if i > 0 {
                        self.push(" | ");
                    }
                    self.pat(a);
                }
            }
        }
    }

    // ------------------------------------------------------------ alignment (S-07)

    fn finish(mut self) -> String {
        while self.out.ends_with(' ') || self.out.ends_with('\n') {
            self.out.pop();
        }
        let mut lines: Vec<String> = self.out.split('\n').map(|l| l.trim_end().to_string()).collect();

        // Align ` = ` in runs of consecutive single-line `let` / `var`.
        self.let_marks.sort();
        let mut i = 0;
        while i < self.let_marks.len() {
            let mut j = i;
            while j + 1 < self.let_marks.len() && self.let_marks[j + 1].0 == self.let_marks[j].0 + 1 {
                j += 1;
            }
            // Every run is aligned (gofmt style, S-07): the canonical form does not depend
            // on what the author wrote.
            let max = self.let_marks[i..=j].iter().map(|m| m.1).max().unwrap_or(0);
            for &(line, col) in &self.let_marks[i..=j] {
                if col < max {
                    let l = &lines[line];
                    let byte = l.char_indices().nth(col).map(|(b, _)| b).unwrap_or(l.len());
                    let mut s = l[..byte].to_string();
                    s.extend(std::iter::repeat_n(' ', max - col));
                    s.push_str(&l[byte..]);
                    lines[line] = s;
                }
            }
            i = j + 1;
        }

        // Align trailing comments in runs of consecutive lines: exactly one space after the
        // longest code of the run (gofmt style, S-07).
        self.comment_marks.sort_by_key(|m| m.0);
        let mut i = 0;
        while i < self.comment_marks.len() {
            let mut j = i;
            while j + 1 < self.comment_marks.len() && self.comment_marks[j + 1].0 == self.comment_marks[j].0 + 1 {
                j += 1;
            }
            let run = &self.comment_marks[i..=j];
            let code_of = |lines: &[String], m: &(usize, String, usize)| -> String {
                let l = &lines[m.0];
                l[..l.len() - m.1.len()].trim_end().to_string()
            };
            let longest = run.iter().map(|m| code_of(&lines, m).chars().count()).max().unwrap_or(0);
            let col = longest + 1;
            for m in run {
                let code = code_of(&lines, m);
                let width = code.chars().count();
                let mut s = code;
                s.extend(std::iter::repeat_n(' ', col - width));
                s.push_str(&m.1);
                lines[m.0] = s;
            }
            i = j + 1;
        }

        let mut out = lines.join("\n");
        if out.is_empty() {
            return out;
        }
        out.push('\n');
        out
    }
}

/// The tokens of a short code text without its whitespace and comments
/// (the text has no string or character literal: a negative literal pattern).
fn code_only(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if rest.starts_with("//") {
            rest = rest.find('\n').map_or("", |i| &rest[i..]);
        } else if rest.starts_with("/*") {
            rest = rest.find("*/").map_or("", |i| &rest[i + 2..]);
        } else {
            if !c.is_whitespace() {
                out.push(c);
            }
            rest = &rest[c.len_utf8()..];
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use onsa_diag::FileId;

    #[test]
    fn move_expressions_round_trip() {
        let src = "fn f(move b: Buf[F32]) {\n  let y = move b\n  let s = Box { b: move y }\n  match move b {\n    _ => 1,\n  }\n}\n";
        assert_eq!(fmt(src), src);
        assert_eq!(fmt("fn f(move b: U32) {\n  let y =   move   b\n}\n"), "fn f(move b: U32) {\n  let y = move b\n}\n");
    }

    #[test]
    fn const_type_arguments_round_trip() {
        let src = "pub fn f(r: Ring[F32, 4]) -> Ring[F32, TABLE_SIZE] {\n  r\n}\n";
        assert_eq!(fmt(src), src);
    }

    fn fmt(src: &str) -> String {
        let parsed = crate::parse(FileId(0), src);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let out = crate::format(&parsed, src).unwrap();
        let again = crate::parse(FileId(0), &out);
        let out2 = crate::format(&again, &out).unwrap();
        assert_eq!(out, out2, "not idempotent");
        out
    }

    #[test]
    fn negative_literal_patterns_keep_their_comments_once() {
        // The parentheses stay, the spaces go (S-185); a comment inside is kept once, and
        // the output parses again (W2-06/b: the comment was printed twice, `) = // c`).
        for src in [
            "fn p(x: I32) -> I32 {\n  match x {\n    -( // c\n      5\n    ) => 5,\n    _ => 0,\n  }\n}\n",
            "fn p(x: I32) -> I32 {\n  match x {\n    -(6 // c\n    ) | -7 => 6,\n    _ => 0,\n  }\n}\n",
            "fn p(x: I32) -> I32 {\n  match x {\n    - ( ( 2 ) ) => 2,\n    _ => 0,\n  }\n}\n",
        ] {
            let out = fmt(src);
            assert_eq!(out.matches("// c").count(), src.matches("// c").count(), "{out}");
            assert!(out.contains("-(5) =>") || out.contains("-(6) |") || out.contains("-((2)) =>"), "{out}");
            assert!(crate::parse(FileId(0), &out).diagnostics.is_empty(), "{out}");
        }
    }

    #[test]
    fn whitespace_is_normalized() {
        assert_eq!(
            fmt("fn f(x:F32)->F32{\nlet a=x+(y*z)\na\n}"),
            "fn f(x: F32) -> F32 {\n  let a = x + (y * z)\n  a\n}\n"
        );
        assert_eq!(fmt("fn f( a : I32 , b:I32 ) { g( a,b ) }"), "fn f(a: I32, b: I32) { g(a, b) }\n");
        assert_eq!(fmt("fn f(x: F32) -> F32 { - x.abs() }"), "fn f(x: F32) -> F32 { -x.abs() }\n");
        assert_eq!(fmt("fn f(x: I32) -> F64 { ( x as F64 ) }"), "fn f(x: I32) -> F64 { (x as F64) }\n");
        assert_eq!(fmt("fn f() uses { Alloc , Fs } {}"), "fn f() uses {Alloc, Fs} {}\n");
        assert_eq!(fmt("use std.math.{ exp ,cos }"), "use std.math.{exp, cos}\n");
    }

    #[test]
    fn call_marks_are_tight() {
        assert_eq!(
            fmt("flow v(f0: Ctl[F32]) -> Sig[F32] { saw~(f0) }"),
            "flow v(f0: Ctl[F32]) -> Sig[F32] { saw~(f0) }\n"
        );
        assert_eq!(
            fmt("fn f(inout out: Span[F32]) { out.fill!( 0.0 ) }"),
            "fn f(inout out: Span[F32]) { out.fill!(0.0) }\n"
        );
    }

    #[test]
    fn trailing_commas_follow_layout() {
        // Block style gets a trailing comma; inline has none; visual style has none.
        assert_eq!(fmt("struct P {\n  x: F32,\n  y: F32\n}"), "struct P {\n  x: F32,\n  y: F32,\n}\n");
        assert_eq!(fmt("fn f() { g(1, 2,) }"), "fn f() { g(1, 2) }\n");
        assert_eq!(fmt("fn f() {\n  g(1,\n      2,\n     3)\n}"), "fn f() {\n  g(1,\n    2,\n    3)\n}\n");
        assert_eq!(fmt("fn f() {\n  g(\n    1, 2,\n    3\n  )\n}"), "fn f() {\n  g(\n    1, 2,\n    3,\n  )\n}\n");
    }

    #[test]
    fn blank_lines_collapse() {
        assert_eq!(fmt("fn a() {}\n\n\n\nfn b() {}\n"), "fn a() {}\n\nfn b() {}\n");
        assert_eq!(fmt("fn a() {}\nfn b() {}\n"), "fn a() {}\nfn b() {}\n");
        assert_eq!(fmt("fn f() {\n\n  let a = 1\n\n\n  let b = 2\n\n}\n"), "fn f() {\n  let a = 1\n\n  let b = 2\n}\n");
        assert_eq!(fmt("fn a() {}\n\n\n"), "fn a() {}\n");
        assert_eq!(fmt(""), "");
    }

    #[test]
    fn trailing_return_is_removed() {
        assert_eq!(
            fmt("fn f(x: I32) -> I32 {\n  let y = x\n  return y\n}\n"),
            "fn f(x: I32) -> I32 {\n  let y = x\n  y\n}\n"
        );
        // Only at the end of the function body: an early return stays.
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n"),
            "fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n"
        );
    }

    #[test]
    fn one_line_and_multi_line_blocks_are_kept() {
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 { if c { 1 } else { 2 } }"),
            "fn f(c: Bool) -> I32 { if c { 1 } else { 2 } }\n"
        );
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}"),
            "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}\n"
        );
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  match c {\n    true => 1,\n    false => 2\n  }\n}"),
            "fn f(c: Bool) -> I32 {\n  match c {\n    true => 1,\n    false => 2,\n  }\n}\n"
        );
    }

    #[test]
    fn continuation_lines_are_kept() {
        assert_eq!(
            fmt("fn f(x: F32) -> F32 {\n  let y = x +\n        1.0\n  y\n}"),
            "fn f(x: F32) -> F32 {\n  let y = x +\n    1.0\n  y\n}\n"
        );
        assert_eq!(fmt("fn f(x: F32) -> F32 {\n  x\n      .abs()\n}"), "fn f(x: F32) -> F32 {\n  x\n    .abs()\n}\n");
    }

    #[test]
    fn let_runs_are_always_aligned() {
        assert_eq!(
            fmt("fn f() {\n  let r  = 1\n  let y1 = 2\n  let y = 3\n}"),
            "fn f() {\n  let r  = 1\n  let y1 = 2\n  let y  = 3\n}\n"
        );
        // Canonical regardless of the author's spacing (S-07).
        assert_eq!(fmt("fn f() {\n  let st = 1\n  let t = 2\n}"), "fn f() {\n  let st = 1\n  let t  = 2\n}\n");
        // Annotated bindings and other statements break a run.
        assert_eq!(
            fmt("fn f() {\n  let r  = 1\n  let x: I32 = 2\n  let y1 = 3\n}"),
            "fn f() {\n  let r = 1\n  let x: I32 = 2\n  let y1 = 3\n}\n"
        );
    }

    #[test]
    fn comments_are_preserved_and_aligned() {
        let src = "// head\n/// doc\nfn f() {\n  // inside\n  let a = 1 // one\n  let bb = 2    // two\n\n  // before tail\n  a\n}\n";
        let want = "// head\n/// doc\nfn f() {\n  // inside\n  let a  = 1 // one\n  let bb = 2 // two\n\n  // before tail\n  a\n}\n";
        assert_eq!(fmt(src), want);
        // Exactly one space after the longest code of the run, whatever the author wrote.
        assert_eq!(fmt("fn f() {\n  let a = 1        // c\n}\n"), "fn f() {\n  let a = 1 // c\n}\n");
        // Comments before `}` and at end of file survive.
        assert_eq!(
            fmt("fn f() {\n  let a = 1\n  // last\n}\n// eof\n"),
            "fn f() {\n  let a = 1\n  // last\n}\n// eof\n"
        );
    }

    #[test]
    fn refuses_files_with_syntax_errors() {
        let src = "fn f() {\n  let a = x + y * z\n}\n";
        let parsed = crate::parse(FileId(0), src);
        assert!(crate::format(&parsed, src).is_none());
        // Naming errors do not block formatting.
        let src = "fn Bad() {}\n";
        let parsed = crate::parse(FileId(0), src);
        assert_eq!(crate::format(&parsed, src), Some("fn Bad() {}\n".to_string()));
    }
}
