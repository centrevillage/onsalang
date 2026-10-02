//! Hand-written recursive-descent parser (D-01) over the token list from the
//! lexer. Produces the arena AST of [`crate::ast`].
//!
//! Newlines (spec §2.5): inside a block a `Newline` token ends a statement
//! unless the line ends with a binary operator, `=`, `->` or `=>`, or the next
//! line starts with `.`. Inside parentheses, brackets, struct literals, match
//! arm lists, generic lists and `uses { }` rows, newlines are whitespace. The
//! parser keeps a stack of "newline significant" flags; `peek` skips newlines
//! whenever the top of the stack says they are insignificant.
//!
//! Errors: at most one diagnostic per top-level item is kept (P-01, §18.1).
//! Parse errors are fatal for the item; the parser then skips to the next
//! item start and continues.

use onsa_diag::{Code, Diagnostic, FileId, Fix, Span};

use crate::ast::*;
use crate::token::{Token, TokenKind};

/// Result of [`crate::parse`].
#[derive(Debug)]
pub struct Parsed {
    pub ast: Ast,
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Marker for "a diagnostic was reported; abandon this item".
#[derive(Debug, Clone, Copy)]
pub(crate) struct ParseError;

pub(crate) type PResult<T> = Result<T, ParseError>;

/// What kind of declaration list we are inside; decides whether `fn` bodies
/// are required / allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ItemCtx {
    Top,
    Trait,
    Impl,
    Effect,
    Handler,
    Extern,
    InlineHandler,
}

const BUILTIN_TYPE_FIXES: &[(&str, &str)] = &[
    ("i8", "I8"),
    ("i16", "I16"),
    ("i32", "I32"),
    ("i64", "I64"),
    ("u8", "U8"),
    ("u16", "U16"),
    ("u32", "U32"),
    ("u64", "U64"),
    ("f32", "F32"),
    ("f64", "F64"),
    ("bool", "Bool"),
    ("usize", "U32"),
    ("isize", "I32"),
];

pub(crate) struct Parser<'a> {
    file: FileId,
    text: &'a str,
    tokens: Vec<Token>,
    /// Index of the next raw token.
    pos: usize,
    /// End offset of the last consumed token.
    last_end: u32,
    /// Stack of "newlines are significant" flags.
    nl: Vec<bool>,
    /// S-08: no struct literal in the head expression of `if` / `while` / ...
    no_struct_lit: bool,
    /// Brace depth of the cursor (for recovery).
    depth: i32,
    ast: Ast,
    diagnostics: Vec<Diagnostic>,
    /// Spans of every top-level item attempt (successful or not), for P-01.
    item_ranges: Vec<Span>,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(file: FileId, text: &'a str, tokens: Vec<Token>, diagnostics: Vec<Diagnostic>) -> Parser<'a> {
        Parser {
            file,
            text,
            tokens,
            pos: 0,
            last_end: 0,
            nl: vec![true],
            no_struct_lit: false,
            depth: 0,
            ast: Ast::default(),
            diagnostics,
            item_ranges: Vec::new(),
        }
    }

    // ------------------------------------------------------------ cursor

    fn significant(&self) -> bool {
        *self.nl.last().unwrap()
    }

    fn with_nl<T>(&mut self, significant: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        self.nl.push(significant);
        let r = f(self);
        self.nl.pop();
        r
    }

    /// Index of the next token that is not trivia under the current context.
    fn peek_index(&self) -> usize {
        let mut i = self.pos;
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment => i += 1,
                TokenKind::Newline if !self.significant() => i += 1,
                _ => return i,
            }
        }
    }

    fn peek(&self) -> Token {
        self.tokens[self.peek_index()]
    }

    fn peek_kind(&self) -> TokenKind {
        self.peek().kind
    }

    /// The token after `peek()` (same skipping rules).
    fn peek2(&self) -> Token {
        let mut i = self.peek_index();
        if self.tokens[i].kind != TokenKind::Eof {
            i += 1;
        }
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment => i += 1,
                TokenKind::Newline if !self.significant() => i += 1,
                _ => return t,
            }
        }
    }

    /// The next token ignoring newlines regardless of context.
    fn peek_past_newlines(&self) -> Token {
        let mut i = self.pos;
        loop {
            let t = self.tokens[i];
            match t.kind {
                TokenKind::Comment | TokenKind::DocComment | TokenKind::Newline => i += 1,
                _ => return t,
            }
        }
    }

    fn bump(&mut self) -> Token {
        let i = self.peek_index();
        let t = self.tokens[i];
        if t.kind != TokenKind::Eof {
            self.pos = i + 1;
            self.last_end = t.span.end;
            match t.kind {
                TokenKind::LBrace => self.depth += 1,
                TokenKind::RBrace => self.depth -= 1,
                _ => {}
            }
        } else {
            self.pos = i;
        }
        t
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.peek_kind() == kind
    }

    fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.at(kind) { Some(self.bump()) } else { None }
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.bump();
        }
    }

    fn token_text(&self, t: Token) -> &'a str {
        &self.text[t.span.start as usize..t.span.end as usize]
    }

    fn is_ident(&self, t: Token, text: &str) -> bool {
        t.kind == TokenKind::Ident && self.token_text(t) == text
    }

    fn span_from(&self, start: u32) -> Span {
        Span::new(self.file, start, self.last_end.max(start))
    }

    fn src(&self, span: Span) -> &'a str {
        &self.text[span.start as usize..span.end as usize]
    }

    // ------------------------------------------------------------ diagnostics

    fn report(&mut self, d: Diagnostic) {
        self.diagnostics.push(d);
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) -> ParseError {
        let found = self.src(span).to_string();
        let mut d = Diagnostic::new(code, span, message);
        if !found.is_empty() && !found.contains('\n') {
            d = d.with_found(found);
        }
        self.report(d);
        ParseError
    }

    fn unexpected(&mut self, expected: &str) -> ParseError {
        let t = self.peek();
        let msg = format!("expected {expected}, found {}", t.kind.describe());
        self.error(Code::E0002, t.span, msg)
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(kind) { Ok(self.bump()) } else { Err(self.unexpected(kind.describe())) }
    }

    /// E0020 with a replacement, non-fatal (§18.1).
    fn foreign(&mut self, span: Span, message: &str, replace: &str) {
        let found = self.src(span).to_string();
        let d = Diagnostic::new(Code::E0020, span, message)
            .with_found(found)
            .with_fix(Fix::Replace { replace: replace.to_string() });
        self.report(d);
    }

    // ------------------------------------------------------------ file

    pub(crate) fn parse_file(mut self) -> Parsed {
        loop {
            let doc = self.collect_docs();
            if self.at(TokenKind::Eof) {
                break; // trailing doc comments without a declaration are dropped
            }
            if self.at(TokenKind::Semi) {
                let t = self.bump();
                self.foreign(t.span, "`;` is not used in Onsa; statements end at the newline", "");
                continue;
            }
            let start = self.peek().span.start;
            match self.parse_item(ItemCtx::Top, doc) {
                Ok(id) => {
                    self.ast.root.push(id);
                    self.item_ranges.push(self.ast.item(id).span);
                    // Terminator: newline, `;` (E0020), or end of file.
                    match self.peek_kind() {
                        TokenKind::Newline | TokenKind::Eof => {}
                        TokenKind::Semi => {
                            let t = self.bump();
                            self.foreign(t.span, "`;` is not used in Onsa; statements end at the newline", "");
                        }
                        _ => {
                            let _ = self.unexpected("newline after the declaration");
                            self.recover(start);
                        }
                    }
                }
                Err(ParseError) => self.recover(start),
            }
        }
        crate::groups::check(&self.ast, self.text, &mut self.diagnostics);
        crate::naming::check(&self.ast, &mut self.diagnostics);
        let diagnostics = first_per_item(&self.item_ranges, std::mem::take(&mut self.diagnostics));
        Parsed { ast: self.ast, tokens: self.tokens, diagnostics }
    }

    /// Skip to the next item start at the beginning of a line, outside braces
    /// (T1-7). Records the skipped range for P-01 grouping.
    fn recover(&mut self, item_start: u32) {
        let mut depth = self.depth;
        let mut i = self.peek_index();
        while self.tokens[i].kind != TokenKind::Eof {
            let t = self.tokens[i];
            let line_start = i == 0 || self.tokens[i - 1].kind == TokenKind::Newline;
            if i > self.pos && depth <= 0 && line_start && is_item_start(t.kind) {
                break;
            }
            match t.kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        let end = if i > 0 { self.tokens[i - 1].span.end } else { item_start };
        self.pos = i;
        self.last_end = end.max(self.last_end);
        self.depth = 0;
        self.nl.truncate(1);
        self.no_struct_lit = false;
        self.item_ranges.push(Span::new(self.file, item_start, end.max(item_start)));
    }

    // ------------------------------------------------------------ items

    /// Doc comments directly before an item (skipping blank lines and plain comments).
    fn collect_docs(&mut self) -> Vec<Span> {
        let mut docs = Vec::new();
        loop {
            let t = self.tokens[self.pos];
            match t.kind {
                TokenKind::Newline | TokenKind::Comment => self.pos += 1,
                TokenKind::DocComment => {
                    docs.push(t.span);
                    self.pos += 1;
                }
                _ => break,
            }
        }
        docs
    }

    fn parse_attrs(&mut self) -> PResult<Vec<Attr>> {
        let mut attrs = Vec::new();
        loop {
            self.skip_newlines_if_followed_by(|k| matches!(k, TokenKind::At | TokenKind::Hash));
            if self.at(TokenKind::At) {
                attrs.push(self.parse_attr()?);
            } else if self.at(TokenKind::Hash) && self.peek2().kind == TokenKind::LBracket {
                // `#[derive(...)]` → `@derive(...)`
                let hash = self.bump();
                self.bump(); // `[`
                let inner_start = self.peek().span.start;
                let attr = self.with_nl(false, |p| p.parse_attr_body(hash.span.start))?;
                let inner_end = self.last_end;
                self.expect(TokenKind::RBracket)?;
                let span = self.span_from(hash.span.start);
                let fix = format!("@{}", &self.text[inner_start as usize..inner_end as usize]);
                self.foreign(span, "attributes are written `@name(...)`", &fix);
                attrs.push(attr);
            } else {
                break;
            }
        }
        Ok(attrs)
    }

    /// In a significant context, skip newlines only when the next real token satisfies `f`.
    fn skip_newlines_if_followed_by(&mut self, f: impl Fn(TokenKind) -> bool) {
        if self.at(TokenKind::Newline) && f(self.peek_past_newlines().kind) {
            self.skip_newlines();
        }
    }

    fn parse_attr(&mut self) -> PResult<Attr> {
        let at = self.expect(TokenKind::At)?;
        self.parse_attr_body(at.span.start)
    }

    fn parse_attr_body(&mut self, start: u32) -> PResult<Attr> {
        let name = self.parse_ident("attribute name")?;
        let mut args = Vec::new();
        if self.at(TokenKind::LParen) && !self.peek().space_before {
            self.bump();
            self.with_nl(false, |p| {
                while !p.at(TokenKind::RParen) {
                    let arg = if p.at(TokenKind::Ident) && p.peek2().kind == TokenKind::Colon {
                        let key = p.parse_ident("key")?;
                        p.bump();
                        let value = p.parse_expr()?;
                        AttrArg::Named { key, value }
                    } else if p.at(TokenKind::Str) {
                        AttrArg::Str(p.parse_str_lit()?)
                    } else {
                        AttrArg::Path(p.parse_path("attribute argument")?)
                    };
                    args.push(arg);
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.expect(TokenKind::RParen)
            })?;
        }
        Ok(Attr { name, args, span: self.span_from(start) })
    }

    fn parse_vis(&mut self) -> PResult<Vis> {
        if self.eat(TokenKind::KwPub).is_none() {
            return Ok(Vis::Private);
        }
        if self.at(TokenKind::LParen) && !self.peek().space_before {
            self.bump();
            let t = self.peek();
            if self.is_ident(t, "pkg") {
                self.bump();
            } else if self.is_ident(t, "crate") {
                self.bump();
                self.foreign(t.span, "package-wide visibility is written `pub(pkg)`", "pkg");
            } else {
                return Err(self.unexpected("`pkg`"));
            }
            self.expect(TokenKind::RParen)?;
            return Ok(Vis::Pkg);
        }
        Ok(Vis::Pub)
    }

    fn parse_item(&mut self, ctx: ItemCtx, doc: Vec<Span>) -> PResult<ItemId> {
        let start = self.peek().span.start;
        let attrs = self.parse_attrs()?;
        if !attrs.is_empty() {
            self.skip_newlines();
        }
        let vis = self.parse_vis()?;
        let t = self.peek();
        let kind = match t.kind {
            TokenKind::KwFn | TokenKind::KwRt => ItemKind::Fn(self.parse_fn(ctx)?),
            TokenKind::KwFlow => ItemKind::Flow(self.parse_flow()?),
            TokenKind::Ident if self.token_text(t) == "proc" && self.peek2().kind == TokenKind::Ident => {
                self.bump();
                self.foreign(t.span, "a signal-processing node is declared with `flow`", "flow");
                ItemKind::Flow(self.parse_flow_after_keyword()?)
            }
            TokenKind::KwStruct => ItemKind::Struct(self.parse_struct()?),
            TokenKind::KwEnum => ItemKind::Enum(self.parse_enum()?),
            TokenKind::KwType => self.parse_type_item(ctx)?,
            TokenKind::KwTrait => ItemKind::Trait(self.parse_trait()?),
            TokenKind::KwImpl => ItemKind::Impl(self.parse_impl()?),
            TokenKind::KwEffect | TokenKind::KwBlocking => ItemKind::Effect(self.parse_effect()?),
            TokenKind::KwHandler => ItemKind::Handler(self.parse_handler()?),
            TokenKind::KwConst => ItemKind::Const(self.parse_const(ctx)?),
            TokenKind::KwUse => ItemKind::Use(self.parse_use()?),
            TokenKind::KwExtern => ItemKind::Extern(self.parse_extern()?),
            TokenKind::KwTarget => self.parse_target()?,
            TokenKind::KwTest => self.parse_test()?,
            _ => return Err(self.unexpected("a declaration")),
        };
        let span = self.span_from(start);
        Ok(self.ast.add_item(Item { span, doc, attrs, vis, kind }))
    }

    /// `[rt] fn name[generics](params) [-> T] [uses {..}] [body]`
    fn parse_fn(&mut self, ctx: ItemCtx) -> PResult<FnDecl> {
        let rt = self.eat(TokenKind::KwRt).is_some();
        self.expect(TokenKind::KwFn)?;
        let name = self.parse_ident("function name")?;
        let generics = self.parse_generics_opt()?;
        let params = self.parse_params(true)?;
        let ret = if self.eat(TokenKind::Arrow).is_some() { Some(self.parse_type()?) } else { None };
        let effects = self.parse_effect_row_opt()?;
        let body = match ctx {
            ItemCtx::Effect | ItemCtx::Extern => {
                if self.at(TokenKind::LBrace) {
                    let t = self.peek();
                    return Err(self.error(Code::E0002, t.span, "this declaration is a signature and takes no body"));
                }
                None
            }
            ItemCtx::Trait => {
                if self.at(TokenKind::LBrace) {
                    Some(self.parse_block_expr()?)
                } else {
                    None
                }
            }
            _ => {
                if !self.at(TokenKind::LBrace) {
                    return Err(self.unexpected("`{` (a function body)"));
                }
                Some(self.parse_block_expr()?)
            }
        };
        Ok(FnDecl { rt, name, generics, params, ret, effects, body })
    }

    fn parse_flow(&mut self) -> PResult<FlowDecl> {
        self.expect(TokenKind::KwFlow)?;
        self.parse_flow_after_keyword()
    }

    fn parse_flow_after_keyword(&mut self) -> PResult<FlowDecl> {
        let name = self.parse_ident("flow name")?;
        let params = self.parse_params(true)?;
        self.expect(TokenKind::Arrow)?;
        let ret = self.parse_type()?;
        let body = self.parse_block_expr()?;
        Ok(FlowDecl { name, params, ret, body })
    }

    fn parse_struct(&mut self) -> PResult<StructDecl> {
        self.expect(TokenKind::KwStruct)?;
        let name = self.parse_ident("struct name")?;
        let generics = self.parse_generics_opt()?;
        let kind = if self.at(TokenKind::LParen) {
            self.bump();
            let ty = self.with_nl(false, |p| {
                let ty = p.parse_type()?;
                p.expect(TokenKind::RParen)?;
                Ok(ty)
            })?;
            StructKind::Tuple(ty)
        } else {
            self.expect(TokenKind::LBrace)?;
            let fields = self.with_nl(false, |p| {
                let mut fields = Vec::new();
                while !p.at(TokenKind::RBrace) {
                    let start = p.peek().span.start;
                    let vis = p.parse_vis()?;
                    let name = p.parse_ident("field name")?;
                    p.expect(TokenKind::Colon)?;
                    let ty = p.parse_type()?;
                    fields.push(Field { vis, name, ty, span: p.span_from(start) });
                    if p.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
                p.expect(TokenKind::RBrace)?;
                Ok(fields)
            })?;
            StructKind::Named(fields)
        };
        Ok(StructDecl { name, generics, kind })
    }

    fn parse_enum(&mut self) -> PResult<EnumDecl> {
        self.expect(TokenKind::KwEnum)?;
        let name = self.parse_ident("enum name")?;
        let generics = self.parse_generics_opt()?;
        self.expect(TokenKind::LBrace)?;
        let variants = self.with_nl(false, |p| {
            let mut variants = Vec::new();
            while !p.at(TokenKind::RBrace) {
                let start = p.peek().span.start;
                let name = p.parse_ident("variant name")?;
                let mut fields = Vec::new();
                if p.eat(TokenKind::LParen).is_some() {
                    while !p.at(TokenKind::RParen) {
                        fields.push(p.parse_type()?);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                } else if p.at(TokenKind::LBrace) {
                    let t = p.peek();
                    return Err(p.error(
                        Code::E0002,
                        t.span,
                        "enum variants are tuple-like or unit; wrap named fields in a struct (§4.4)",
                    ));
                }
                variants.push(Variant { name, fields, span: p.span_from(start) });
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(variants)
        })?;
        Ok(EnumDecl { name, generics, variants })
    }

    /// `type Name = T` (alias) or `type Name` (opaque, in `extern` / `target`).
    fn parse_type_item(&mut self, ctx: ItemCtx) -> PResult<ItemKind> {
        self.expect(TokenKind::KwType)?;
        let name = self.parse_ident("type name")?;
        if self.eat(TokenKind::Eq).is_some() {
            if ctx == ItemCtx::Extern {
                return Err(self.error(Code::E0002, name.span, "an opaque type in `extern` has no definition"));
            }
            let ty = self.parse_type()?;
            Ok(ItemKind::TypeAlias { name, ty })
        } else if ctx == ItemCtx::Extern {
            Ok(ItemKind::OpaqueType { name })
        } else {
            Err(self.unexpected("`=` (a type alias needs a definition)"))
        }
    }

    fn parse_trait(&mut self) -> PResult<TraitDecl> {
        self.expect(TokenKind::KwTrait)?;
        let name = self.parse_ident("trait name")?;
        let generics = self.parse_generics_opt()?;
        let items = self.parse_item_body(ItemCtx::Trait)?;
        Ok(TraitDecl { name, generics, items })
    }

    fn parse_impl(&mut self) -> PResult<ImplDecl> {
        self.expect(TokenKind::KwImpl)?;
        let generics = self.parse_generics_opt()?;
        let first = self.parse_type()?;
        let (trait_, self_ty) = if self.eat(TokenKind::KwFor).is_some() {
            let path = match &self.ast.ty(first).kind {
                TypeKind::Path { path, args } if args.is_empty() => path.clone(),
                _ => {
                    let span = self.ast.ty(first).span;
                    return Err(self.error(Code::E0002, span, "expected a trait name before `for`"));
                }
            };
            (Some(path), self.parse_type()?)
        } else {
            (None, first)
        };
        let items = self.parse_item_body(ItemCtx::Impl)?;
        Ok(ImplDecl { generics, trait_, self_ty, items })
    }

    fn parse_effect(&mut self) -> PResult<EffectDecl> {
        let blocking = self.eat(TokenKind::KwBlocking).is_some();
        self.expect(TokenKind::KwEffect)?;
        let name = self.parse_ident("effect name")?;
        let ops = self.parse_item_body(ItemCtx::Effect)?;
        Ok(EffectDecl { blocking, name, ops })
    }

    fn parse_handler(&mut self) -> PResult<HandlerDecl> {
        self.expect(TokenKind::KwHandler)?;
        let name = self.parse_ident("handler name")?;
        let params = if self.at(TokenKind::LParen) { self.parse_params(true)? } else { Vec::new() };
        self.expect(TokenKind::Colon)?;
        let effect = self.parse_path("effect name")?;
        let items = self.parse_item_body(ItemCtx::Handler)?;
        Ok(HandlerDecl { name, params, effect, items })
    }

    fn parse_const(&mut self, ctx: ItemCtx) -> PResult<ConstDecl> {
        self.expect(TokenKind::KwConst)?;
        let name = self.parse_ident("constant name")?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let value = if self.eat(TokenKind::Eq).is_some() {
            self.skip_newlines();
            Some(self.parse_expr()?)
        } else if ctx == ItemCtx::Trait {
            None
        } else {
            return Err(self.unexpected("`=` (a constant needs a value)"));
        };
        Ok(ConstDecl { name, ty, value })
    }

    fn parse_use(&mut self) -> PResult<UseDecl> {
        self.expect(TokenKind::KwUse)?;
        let start = self.peek().span.start;
        let mut segments = vec![self.parse_ident("module path")?];
        let mut names = None;
        loop {
            if self.at(TokenKind::ColonColon) {
                let t = self.bump();
                self.foreign(t.span, "paths are separated with `.`", ".");
            } else if self.eat(TokenKind::Dot).is_none() {
                break;
            }
            if self.at(TokenKind::LBrace) {
                self.bump();
                let list = self.with_nl(false, |p| {
                    let mut list = Vec::new();
                    while !p.at(TokenKind::RBrace) {
                        list.push(p.parse_ident("imported name")?);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RBrace)?;
                    Ok(list)
                })?;
                names = Some(list);
                break;
            }
            if self.at(TokenKind::Star) {
                let t = self.peek();
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "there is no glob import; list the names in `{ }` (§15.1)",
                ));
            }
            segments.push(self.parse_name_after_dot("module path")?);
        }
        let path = Path { segments, span: self.span_from(start) };
        Ok(UseDecl { path, names })
    }

    fn parse_extern(&mut self) -> PResult<ExternDecl> {
        self.expect(TokenKind::KwExtern)?;
        let abi = self.parse_str_lit()?;
        let t = self.peek();
        if !self.is_ident(t, "lib") {
            return Err(self.unexpected("`lib`"));
        }
        self.bump();
        let lib = self.parse_str_lit()?;
        let items = self.parse_item_body(ItemCtx::Extern)?;
        Ok(ExternDecl { abi, lib, items })
    }

    fn parse_target(&mut self) -> PResult<ItemKind> {
        self.expect(TokenKind::KwTarget)?;
        let inner = match self.peek_kind() {
            TokenKind::KwType => {
                self.bump();
                let name = self.parse_ident("type name")?;
                ItemKind::OpaqueType { name }
            }
            TokenKind::KwFn | TokenKind::KwRt => ItemKind::Fn(self.parse_fn(ItemCtx::Extern)?),
            _ => return Err(self.unexpected("`fn` or `type` after `target`")),
        };
        Ok(ItemKind::Target(Box::new(inner)))
    }

    fn parse_test(&mut self) -> PResult<ItemKind> {
        self.expect(TokenKind::KwTest)?;
        let name = self.parse_str_lit()?;
        let body = self.parse_block_expr()?;
        Ok(ItemKind::Test { name, body })
    }

    /// `{ item NL item NL ... }` for trait / impl / effect / handler / extern bodies.
    fn parse_item_body(&mut self, ctx: ItemCtx) -> PResult<Vec<ItemId>> {
        self.expect(TokenKind::LBrace)?;
        self.with_nl(true, |p| {
            let mut items = Vec::new();
            loop {
                let doc = p.collect_docs();
                if p.at(TokenKind::RBrace) {
                    break;
                }
                if p.at(TokenKind::Eof) {
                    return Err(p.unexpected("`}`"));
                }
                items.push(p.parse_item(ctx, doc)?);
                match p.peek_kind() {
                    TokenKind::Newline | TokenKind::RBrace => {}
                    TokenKind::Semi => {
                        let t = p.bump();
                        p.foreign(t.span, "`;` is not used in Onsa; declarations end at the newline", "");
                    }
                    _ => return Err(p.unexpected("newline or `}`")),
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(items)
        })
    }

    // ------------------------------------------------------------ signatures

    fn parse_ident(&mut self, what: &str) -> PResult<Ident> {
        let t = self.peek();
        if t.kind == TokenKind::Ident {
            self.bump();
            Ok(Ident { name: self.token_text(t).to_string(), span: t.span })
        } else {
            Err(self.unexpected(what))
        }
    }

    /// `a.b.c` (also accepts `Self` as a segment). `::` is E0020.
    fn parse_path(&mut self, what: &str) -> PResult<Path> {
        let start = self.peek().span.start;
        let mut segments = vec![self.parse_path_segment(what)?];
        loop {
            if self.at(TokenKind::ColonColon) {
                let t = self.bump();
                self.foreign(t.span, "paths are separated with `.`", ".");
            } else if self.at(TokenKind::Dot)
                && (self.peek2().kind == TokenKind::Ident || self.peek2().kind.is_keyword())
            {
                self.bump();
            } else {
                break;
            }
            segments.push(self.parse_name_after_dot(what)?);
        }
        Ok(Path { segments, span: self.span_from(start) })
    }

    /// After `.`, a keyword is an ordinary name (`std.test`, `x.type`).
    fn parse_name_after_dot(&mut self, what: &str) -> PResult<Ident> {
        let t = self.peek();
        if t.kind == TokenKind::Ident || t.kind.is_keyword() {
            self.bump();
            Ok(Ident { name: self.token_text(t).to_string(), span: t.span })
        } else {
            Err(self.unexpected(what))
        }
    }

    fn parse_path_segment(&mut self, what: &str) -> PResult<Ident> {
        let t = self.peek();
        match t.kind {
            TokenKind::Ident | TokenKind::KwSelfType => {
                self.bump();
                Ok(Ident { name: self.token_text(t).to_string(), span: t.span })
            }
            _ => Err(self.unexpected(what)),
        }
    }

    fn parse_generics_opt(&mut self) -> PResult<Vec<GenericParam>> {
        if self.at(TokenKind::Lt) && !self.peek().space_before {
            // `fn f<T>` → `[T]`
            let lt = self.bump();
            let params = self.with_nl(false, |p| p.parse_generic_list(TokenKind::Gt))?;
            let span = self.span_from(lt.span.start);
            let inner = &self.text[lt.span.end as usize..self.last_end as usize - 1];
            let fix = format!("[{inner}]");
            self.foreign(span, "generic parameters are written in `[ ]`", &fix);
            return Ok(params);
        }
        if !self.at(TokenKind::LBracket) || self.peek().space_before {
            return Ok(Vec::new());
        }
        self.bump();
        self.with_nl(false, |p| p.parse_generic_list(TokenKind::RBracket))
    }

    fn parse_generic_list(&mut self, close: TokenKind) -> PResult<Vec<GenericParam>> {
        let mut params = Vec::new();
        while !self.at(close) {
            let param = if self.eat(TokenKind::KwConst).is_some() {
                let name = self.parse_ident("const parameter name")?;
                self.expect(TokenKind::Colon)?;
                let ty = self.parse_type()?;
                GenericParam::Const { name, ty }
            } else {
                let name = self.parse_ident("type parameter")?;
                if name.name.starts_with(|c: char| c.is_ascii_lowercase()) {
                    GenericParam::Effect { name }
                } else {
                    let mut bounds = Vec::new();
                    if self.eat(TokenKind::Colon).is_some() {
                        loop {
                            let relaxed = self.eat(TokenKind::Question).is_some();
                            let path = self.parse_path("trait bound")?;
                            bounds.push(Bound { relaxed, path });
                            if self.eat(TokenKind::Plus).is_none() {
                                break;
                            }
                        }
                    }
                    GenericParam::Type { name, bounds }
                }
            };
            params.push(param);
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(close)?;
        Ok(params)
    }

    /// `(params)`; `require_types` is false for anonymous functions (§6.1).
    fn parse_params(&mut self, require_types: bool) -> PResult<Vec<Param>> {
        self.expect(TokenKind::LParen)?;
        self.with_nl(false, |p| {
            let mut params = Vec::new();
            while !p.at(TokenKind::RParen) {
                let start = p.peek().span.start;
                let attrs = p.parse_attrs()?;
                let mode = p.parse_mode();
                let t = p.peek();
                // `mut self` → `inout self`
                let mode = if p.is_ident(t, "mut") && p.peek2().kind == TokenKind::KwSelf {
                    p.bump();
                    let span = p.span_from(t.span.start).to(p.peek().span);
                    p.foreign(span, "a receiver that changes is written `inout self`", "inout self");
                    Mode::Inout
                } else {
                    mode
                };
                let t = p.peek();
                let name = match t.kind {
                    TokenKind::KwSelf => {
                        p.bump();
                        ParamName::SelfParam(t.span)
                    }
                    TokenKind::Underscore => {
                        p.bump();
                        ParamName::Wild(t.span)
                    }
                    TokenKind::Ident => ParamName::Ident(p.parse_ident("parameter name")?),
                    TokenKind::Amp => return Err(p.borrow_param_error()),
                    _ => return Err(p.unexpected("a parameter name")),
                };
                let is_self = matches!(name, ParamName::SelfParam(_));
                let ty = if p.eat(TokenKind::Colon).is_some() {
                    Some(p.parse_type()?)
                } else if require_types && !is_self {
                    return Err(p.unexpected("`:` (parameter types are always written, P1)"));
                } else {
                    None
                };
                params.push(Param { attrs, mode, name, ty, span: p.span_from(start) });
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RParen)?;
            Ok(params)
        })
    }

    /// `&mut x` / `&x` from Rust (E0020): the mode goes before the name (§5.2).
    fn borrow_param_error(&mut self) -> ParseError {
        let t = self.peek();
        let is_mut = self.tokens.get(self.peek_index() + 1).is_some_and(|n| {
            n.kind == TokenKind::Ident && &self.text[n.span.start as usize..n.span.end as usize] == "mut"
        });
        let (span, msg) = if is_mut {
            let end = self.tokens[self.peek_index() + 1].span.end;
            (
                Span::new(t.span.file, t.span.start, end),
                "`&mut T` is written as `inout name: T`; the mode comes before the name (§5.2)",
            )
        } else {
            (t.span, "`&T` is the default borrow; write `name: T` (§5.2)")
        };
        let found = self.text[span.start as usize..span.end as usize].to_string();
        let d =
            Diagnostic::new(Code::E0020, span, msg).with_found(found).with_fix(Fix::Replace { replace: String::new() });
        self.diagnostics.push(d);
        ParseError
    }

    fn parse_mode(&mut self) -> Mode {
        if self.eat(TokenKind::KwInout).is_some() {
            Mode::Inout
        } else if self.eat(TokenKind::KwMove).is_some() {
            Mode::Move
        } else {
            Mode::Borrow
        }
    }

    fn parse_effect_row_opt(&mut self) -> PResult<Option<EffectRow>> {
        if self.eat(TokenKind::KwUses).is_none() {
            return Ok(None);
        }
        let start = self.peek().span.start;
        self.expect(TokenKind::LBrace)?;
        let effects = self.with_nl(false, |p| {
            let mut effects = Vec::new();
            while !p.at(TokenKind::RBrace) {
                effects.push(p.parse_path("effect name")?);
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.expect(TokenKind::RBrace)?;
            Ok(effects)
        })?;
        Ok(Some(EffectRow { effects, span: self.span_from(start) }))
    }

    // ------------------------------------------------------------ types

    fn parse_type(&mut self) -> PResult<TypeId> {
        let start = self.peek().span.start;
        let kind = match self.peek_kind() {
            TokenKind::LParen => {
                self.bump();
                self.with_nl(false, |p| {
                    if p.eat(TokenKind::RParen).is_some() {
                        return Ok(TypeKind::Unit);
                    }
                    let first = p.parse_type()?;
                    if p.eat(TokenKind::Comma).is_none() {
                        p.expect(TokenKind::RParen)?;
                        return Err(p.error(
                            Code::E0002,
                            p.ast.ty(first).span,
                            "a parenthesized type is not a tuple; tuples have two or more elements",
                        ));
                    }
                    let mut elems = vec![first];
                    while !p.at(TokenKind::RParen) {
                        elems.push(p.parse_type()?);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(TypeKind::Tuple(elems))
                })?
            }
            TokenKind::LBracket => {
                self.bump();
                self.with_nl(false, |p| {
                    let elem = p.parse_type()?;
                    p.expect(TokenKind::Semi)?;
                    let len = p.parse_expr()?;
                    p.expect(TokenKind::RBracket)?;
                    Ok(TypeKind::Array { elem, len })
                })?
            }
            TokenKind::KwRt | TokenKind::KwFn => {
                let rt = self.eat(TokenKind::KwRt).is_some();
                self.expect(TokenKind::KwFn)?;
                self.expect(TokenKind::LParen)?;
                let params = self.with_nl(false, |p| {
                    let mut params = Vec::new();
                    while !p.at(TokenKind::RParen) {
                        let mode = p.parse_mode();
                        params.push((mode, p.parse_type()?));
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(params)
                })?;
                let ret = if self.eat(TokenKind::Arrow).is_some() { Some(self.parse_type()?) } else { None };
                let effects = self.parse_effect_row_opt()?;
                TypeKind::Fn { rt, params, ret, effects }
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let path = self.parse_path("a type")?;
                if let [seg] = path.segments.as_slice()
                    && let Some((_, fix)) = BUILTIN_TYPE_FIXES.iter().find(|(from, _)| *from == seg.name)
                {
                    self.foreign(seg.span, "built-in types are written in UpperCamel (`I32`, `F32`, `Bool`)", fix);
                }
                let mut args = Vec::new();
                if self.at(TokenKind::LBracket) && !self.peek().space_before {
                    self.bump();
                    args = self.with_nl(false, |p| p.parse_type_args(TokenKind::RBracket))?;
                } else if self.at(TokenKind::Lt) && !self.peek().space_before {
                    let lt = self.bump();
                    args = self.with_nl(false, |p| p.parse_type_args(TokenKind::Gt))?;
                    let span = self.span_from(lt.span.start);
                    let inner = &self.text[lt.span.end as usize..self.last_end as usize - 1];
                    let fix = format!("[{inner}]");
                    self.foreign(span, "type arguments are written in `[ ]`", &fix);
                }
                TypeKind::Path { path, args }
            }
            TokenKind::Amp => return Err(self.borrow_param_error()),
            _ => return Err(self.unexpected("a type")),
        };
        Ok(self.ast.add_type(TypeExpr { span: self.span_from(start), kind }))
    }

    fn parse_type_args(&mut self, close: TokenKind) -> PResult<Vec<TypeId>> {
        let mut args = Vec::new();
        while !self.at(close) {
            args.push(self.parse_type_arg()?);
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(close)?;
        Ok(args)
    }

    /// A type argument: a type, or a const argument written as an integer
    /// literal, optionally negated (`Ring[F32, 4]`, S-24 / spec §4.5).
    fn parse_type_arg(&mut self) -> PResult<TypeId> {
        if !matches!(self.peek_kind(), TokenKind::Int | TokenKind::Minus) {
            return self.parse_type();
        }
        let start = self.peek().span.start;
        let neg = self.eat(TokenKind::Minus);
        let tok = self.expect(TokenKind::Int)?;
        let lit = self.int_lit(tok);
        let mut expr = self.ast.add_expr(Expr { span: tok.span, kind: ExprKind::Lit(lit) });
        if neg.is_some() {
            let span = self.span_from(start);
            expr = self.ast.add_expr(Expr { span, kind: ExprKind::Unary { op: UnOp::Neg, expr } });
        }
        Ok(self.ast.add_type(TypeExpr { span: self.span_from(start), kind: TypeKind::ConstArg(expr) }))
    }

    // ------------------------------------------------------------ blocks and statements

    /// `{ stmts }` as an expression (newlines significant inside).
    fn parse_block_expr(&mut self) -> PResult<ExprId> {
        let lbrace = self.expect(TokenKind::LBrace)?;
        let saved = std::mem::replace(&mut self.no_struct_lit, false);
        let block = self.with_nl(true, |p| p.parse_block_body());
        self.no_struct_lit = saved;
        let block = block?;
        let span = self.span_from(lbrace.span.start);
        Ok(self.ast.add_expr(Expr { span, kind: ExprKind::Block(block) }))
    }

    fn parse_block_body(&mut self) -> PResult<Block> {
        let mut stmts: Vec<(StmtKind, Span)> = Vec::new();
        loop {
            self.skip_newlines();
            if self.at(TokenKind::RBrace) {
                break;
            }
            if self.at(TokenKind::Eof) {
                return Err(self.unexpected("`}`"));
            }
            let start = self.peek().span.start;
            let kind = self.parse_stmt()?;
            stmts.push((kind, self.span_from(start)));
            match self.peek_kind() {
                TokenKind::Newline | TokenKind::RBrace => {}
                TokenKind::Semi => {
                    let t = self.bump();
                    self.foreign(t.span, "`;` is not used in Onsa; statements end at the newline", "");
                }
                TokenKind::DotDot | TokenKind::DotDotEq => {
                    let t = self.peek();
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "ranges are only allowed in `for` and `par` heads (§7)",
                    ));
                }
                _ => return Err(self.unexpected("newline or `}`")),
            }
        }
        self.expect(TokenKind::RBrace)?;
        // The block value is the last statement when it is an expression (§6.1).
        let tail = match stmts.last() {
            Some((StmtKind::Expr(_), _)) => match stmts.pop() {
                Some((StmtKind::Expr(e), _)) => Some(e),
                _ => unreachable!(),
            },
            _ => None,
        };
        let stmts = stmts.into_iter().map(|(kind, span)| self.ast.add_stmt(Stmt { span, kind })).collect();
        Ok(Block { stmts, tail })
    }

    fn parse_stmt(&mut self) -> PResult<StmtKind> {
        let t = self.peek();
        match t.kind {
            TokenKind::KwLet => {
                self.bump();
                let m = self.peek();
                if self.is_ident(m, "mut") {
                    self.bump();
                    let span = t.span.to(m.span);
                    self.foreign(span, "a mutable local is declared with `var`", "var");
                    return self.parse_var_rest();
                }
                let pat = self.parse_pattern()?;
                let ty = if self.eat(TokenKind::Colon).is_some() { Some(self.parse_type()?) } else { None };
                self.expect(TokenKind::Eq)?;
                self.skip_newlines();
                let init = self.parse_consumed()?;
                Ok(StmtKind::Let { pat, ty, init })
            }
            TokenKind::KwVar => {
                self.bump();
                self.parse_var_rest()
            }
            TokenKind::KwFor => {
                self.bump();
                let pat = self.parse_pattern()?;
                self.expect(TokenKind::KwIn)?;
                let moved = self.eat(TokenKind::KwMove).is_some();
                let iter = self.parse_head_expr(true)?;
                let body = self.parse_block_expr()?;
                Ok(StmtKind::For { pat, moved, iter, body })
            }
            TokenKind::KwWhile => {
                self.bump();
                let cond = self.parse_head_expr(false)?;
                let body = self.parse_block_expr()?;
                Ok(StmtKind::While { cond, body })
            }
            TokenKind::Ident if self.token_text(t) == "loop" && self.peek2().kind == TokenKind::LBrace => {
                self.bump();
                self.foreign(t.span, "there is no `loop`; write `while true`", "while true");
                let cond = self.ast.add_expr(Expr { span: t.span, kind: ExprKind::Lit(Lit::Bool(true)) });
                let body = self.parse_block_expr()?;
                Ok(StmtKind::While { cond, body })
            }
            TokenKind::KwBreak => {
                self.bump();
                Ok(StmtKind::Break)
            }
            TokenKind::KwContinue => {
                self.bump();
                Ok(StmtKind::Continue)
            }
            TokenKind::KwReturn => {
                self.bump();
                if matches!(self.peek_kind(), TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof | TokenKind::Semi)
                {
                    Ok(StmtKind::Return(None))
                } else {
                    Ok(StmtKind::Return(Some(self.parse_expr()?)))
                }
            }
            TokenKind::KwAssert => {
                self.bump();
                Ok(StmtKind::Assert(self.parse_expr()?))
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.at(TokenKind::Eq) {
                    self.bump();
                    self.skip_newlines();
                    let value = self.parse_consumed()?;
                    return Ok(StmtKind::Assign { target: expr, value });
                }
                Ok(StmtKind::Expr(expr))
            }
        }
    }

    fn parse_var_rest(&mut self) -> PResult<StmtKind> {
        let name = self.parse_ident("variable name")?;
        let ty = if self.eat(TokenKind::Colon).is_some() { Some(self.parse_type()?) } else { None };
        self.expect(TokenKind::Eq)?;
        self.skip_newlines();
        let init = self.parse_consumed()?;
        Ok(StmtKind::Var { name, ty, init })
    }

    /// An expression in a consuming position (§5.2, S-21): `move <place>` or a
    /// plain expression. The `move` operand is a postfix expression (a place).
    fn parse_consumed(&mut self) -> PResult<ExprId> {
        if !self.at(TokenKind::KwMove) {
            return self.parse_expr();
        }
        let start = self.bump().span.start;
        let inner = self.parse_postfix()?;
        let span = self.span_from(start);
        Ok(self.ast.add_expr(Expr { span, kind: ExprKind::Move(inner) }))
    }

    /// Head expression of `if` / `while` / `match` / `for` / `par`: no struct
    /// literal (S-08); ranges allowed only when `allow_range`.
    fn parse_head_expr(&mut self, allow_range: bool) -> PResult<ExprId> {
        let saved = std::mem::replace(&mut self.no_struct_lit, true);
        let r = self.parse_expr_inner(allow_range);
        self.no_struct_lit = saved;
        r
    }

    // ------------------------------------------------------------ expressions

    pub(crate) fn parse_expr(&mut self) -> PResult<ExprId> {
        self.parse_expr_inner(false)
    }

    /// Binary chain, kept flat (§3.1; groups are checked in `groups.rs`).
    fn parse_expr_inner(&mut self, allow_range: bool) -> PResult<ExprId> {
        let start = self.peek().span.start;
        let first = self.parse_cast()?;
        let mut operands = vec![first];
        let mut ops = Vec::new();
        while let Some(op) = binop(self.peek_kind()) {
            let t = self.bump();
            ops.push((op, t.span));
            self.skip_newlines(); // operator at the end of the line continues it (§2.5)
            operands.push(self.parse_cast()?);
        }
        let expr = if ops.is_empty() {
            first
        } else {
            self.ast.add_expr(Expr { span: self.span_from(start), kind: ExprKind::Binary { operands, ops } })
        };
        if matches!(self.peek_kind(), TokenKind::DotDot | TokenKind::DotDotEq) {
            let t = self.peek();
            if !allow_range {
                return Err(self.error(Code::E0002, t.span, "ranges are only allowed in `for` and `par` heads (§7)"));
            }
            self.bump();
            if t.kind == TokenKind::DotDotEq {
                let d =
                    Diagnostic::new(Code::E0020, t.span, "there is no inclusive range; use `..` with an adjusted end")
                        .with_found("..=");
                self.report(d);
            }
            let hi = self.parse_expr_inner(false)?;
            let span = self.span_from(start);
            return Ok(self.ast.add_expr(Expr { span, kind: ExprKind::Range { lo: expr, hi } }));
        }
        Ok(expr)
    }

    /// `prefix [as Type]*` — prefix binds tighter than `as` (§3.1).
    fn parse_cast(&mut self) -> PResult<ExprId> {
        let start = self.peek().span.start;
        let mut expr = self.parse_prefix()?;
        while self.eat(TokenKind::KwAs).is_some() {
            let ty = self.parse_type()?;
            let span = self.span_from(start);
            expr = self.ast.add_expr(Expr { span, kind: ExprKind::Cast { expr, ty } });
        }
        Ok(expr)
    }

    fn parse_prefix(&mut self) -> PResult<ExprId> {
        let t = self.peek();
        let op = match t.kind {
            TokenKind::Minus => Some(UnOp::Neg),
            TokenKind::Bang => Some(UnOp::Not),
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            let inner = self.parse_prefix()?;
            let span = self.span_from(t.span.start);
            return Ok(self.ast.add_expr(Expr { span, kind: ExprKind::Unary { op, expr: inner } }));
        }
        if t.kind == TokenKind::Amp {
            // `&mut x` / `&x` in argument position → `inout x` / `x`
            self.bump();
            let m = self.peek();
            let is_mut = self.is_ident(m, "mut");
            if is_mut {
                self.bump();
            }
            let inner = self.parse_prefix()?;
            let span = self.span_from(t.span.start);
            let inner_src = self.src(self.ast.expr(inner).span);
            let fix = if is_mut { format!("inout {inner_src}") } else { inner_src.to_string() };
            self.foreign(
                span,
                "there are no references; arguments are borrowed by default and changed with `inout`",
                &fix,
            );
            return Ok(inner);
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> PResult<ExprId> {
        let start = self.peek().span.start;
        let mut expr = self.parse_primary()?;
        loop {
            // `.` on the next line continues the expression (§2.5).
            if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::Dot {
                self.skip_newlines();
            }
            let t = self.peek();
            match t.kind {
                TokenKind::LParen => {
                    self.bump();
                    let args = self.parse_args()?;
                    let span = self.span_from(start);
                    expr = self
                        .ast
                        .add_expr(Expr { span, kind: ExprKind::Call { callee: expr, kind: CallKind::Plain, args } });
                }
                TokenKind::Tilde | TokenKind::Bang
                    if !t.space_before
                        && self.peek2().kind == TokenKind::LParen
                        && !self.peek2().space_before
                        && is_name_expr(self.ast.expr(expr)) =>
                {
                    self.bump();
                    self.bump(); // `(`
                    let args = self.parse_args()?;
                    let kind = if t.kind == TokenKind::Tilde { CallKind::Flow } else { CallKind::Bang };
                    let span = self.span_from(start);
                    expr = self.ast.add_expr(Expr { span, kind: ExprKind::Call { callee: expr, kind, args } });
                }
                TokenKind::Tilde => {
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "`~` is only the flow-call mark `name~(args)`, written without spaces (§2.6)",
                    ));
                }
                TokenKind::ColonColon => {
                    self.bump();
                    self.foreign(t.span, "paths are separated with `.`", ".");
                    let name = self.parse_ident("a name after `::`")?;
                    let span = self.span_from(start);
                    expr = self.ast.add_expr(Expr { span, kind: ExprKind::Field { base: expr, name } });
                }
                TokenKind::Dot => {
                    self.bump();
                    let n = self.peek();
                    match n.kind {
                        k if k == TokenKind::Ident || k.is_keyword() => {
                            let name = self.parse_name_after_dot("a field name")?;
                            let span = self.span_from(start);
                            expr = self.ast.add_expr(Expr { span, kind: ExprKind::Field { base: expr, name } });
                        }
                        TokenKind::Int => {
                            self.bump();
                            let text = self.token_text(n);
                            let index = text
                                .parse::<u32>()
                                .map_err(|_| self.error(Code::E0408, n.span, "tuple index is too large"))?;
                            let span = self.span_from(start);
                            expr = self.ast.add_expr(Expr {
                                span,
                                kind: ExprKind::TupleIndex { base: expr, index, index_span: n.span },
                            });
                        }
                        _ => return Err(self.unexpected("a field name or tuple index after `.`")),
                    }
                }
                TokenKind::LBracket if !t.space_before => {
                    self.bump();
                    let index = self.with_nl(false, |p| {
                        let e = p.parse_expr()?;
                        p.expect(TokenKind::RBracket)?;
                        Ok(e)
                    })?;
                    let span = self.span_from(start);
                    expr = self.ast.add_expr(Expr { span, kind: ExprKind::Index { base: expr, index } });
                }
                TokenKind::Question => {
                    self.bump();
                    let span = self.span_from(start);
                    expr = self.ast.add_expr(Expr { span, kind: ExprKind::Try(expr) });
                }
                TokenKind::LBrace if !self.no_struct_lit && struct_lit_path(&self.ast, expr).is_some() => {
                    let path = struct_lit_path(&self.ast, expr).unwrap();
                    self.bump();
                    let fields = self.with_nl(false, |p| {
                        let mut fields = Vec::new();
                        while !p.at(TokenKind::RBrace) {
                            let name = p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            let value = p.parse_consumed()?;
                            fields.push((name, value));
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RBrace)?;
                        Ok(fields)
                    })?;
                    let span = self.span_from(start);
                    expr = self.ast.add_expr(Expr { span, kind: ExprKind::Struct { path, fields } });
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    /// Arguments after `(` has been consumed, up to and including `)`.
    fn parse_args(&mut self) -> PResult<Vec<Arg>> {
        self.with_nl(false, |p| {
            let saved = std::mem::replace(&mut p.no_struct_lit, false);
            let mut args = Vec::new();
            while !p.at(TokenKind::RParen) {
                let start = p.peek().span.start;
                let mode = p.parse_mode();
                let expr = p.parse_expr()?;
                args.push(Arg { mode, expr, span: p.span_from(start) });
                if p.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
            p.no_struct_lit = saved;
            p.expect(TokenKind::RParen)?;
            Ok(args)
        })
    }

    fn parse_primary(&mut self) -> PResult<ExprId> {
        let t = self.peek();
        let start = t.span.start;
        let kind = match t.kind {
            TokenKind::KwMove => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "`move` is written only where a value is consumed: let/var initializers, assignment, literal elements, `match move x`, and call arguments (§5.2)",
                ));
            }
            TokenKind::Int => {
                self.bump();
                ExprKind::Lit(self.int_lit(t))
            }
            TokenKind::Float => {
                self.bump();
                ExprKind::Lit(Lit::Float { text: self.token_text(t).to_string() })
            }
            TokenKind::Char => {
                self.bump();
                ExprKind::Lit(Lit::Char(self.char_lit(t)))
            }
            TokenKind::Str => ExprKind::Lit(Lit::Str(self.parse_str_lit()?)),
            TokenKind::KwTrue => {
                self.bump();
                ExprKind::Lit(Lit::Bool(true))
            }
            TokenKind::KwFalse => {
                self.bump();
                ExprKind::Lit(Lit::Bool(false))
            }
            TokenKind::Underscore => {
                self.bump();
                ExprKind::Hole
            }
            TokenKind::Ident | TokenKind::KwSelf | TokenKind::KwSelfType => {
                self.bump();
                let ident = Ident { name: self.token_text(t).to_string(), span: t.span };
                ExprKind::Path(Path { segments: vec![ident], span: t.span })
            }
            TokenKind::LParen => {
                self.bump();
                self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_paren_rest();
                    p.no_struct_lit = saved;
                    r
                })?
            }
            TokenKind::LBracket => {
                self.bump();
                self.with_nl(false, |p| {
                    let saved = std::mem::replace(&mut p.no_struct_lit, false);
                    let r = p.parse_array_rest();
                    p.no_struct_lit = saved;
                    r
                })?
            }
            TokenKind::LBrace => return self.parse_block_expr(),
            TokenKind::KwIf => return self.parse_if(),
            TokenKind::KwMatch => {
                self.bump();
                let scrutinee = if self.at(TokenKind::KwMove) {
                    // `match move x` consumes the value (§7, S-21).
                    let mstart = self.bump().span.start;
                    let saved = std::mem::replace(&mut self.no_struct_lit, true);
                    let inner = self.parse_postfix();
                    self.no_struct_lit = saved;
                    let inner = inner?;
                    let span = self.span_from(mstart);
                    self.ast.add_expr(Expr { span, kind: ExprKind::Move(inner) })
                } else {
                    self.parse_head_expr(false)?
                };
                self.expect(TokenKind::LBrace)?;
                let arms = self.with_nl(false, |p| {
                    let mut arms = Vec::new();
                    while !p.at(TokenKind::RBrace) {
                        let start = p.peek().span.start;
                        let pat = p.parse_pattern()?;
                        let guard = if p.eat(TokenKind::KwIf).is_some() { Some(p.parse_expr()?) } else { None };
                        p.expect(TokenKind::FatArrow)?;
                        let body = p.parse_expr()?;
                        arms.push(MatchArm { pat, guard, body, span: p.span_from(start) });
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RBrace)?;
                    Ok(arms)
                })?;
                ExprKind::Match { scrutinee, arms }
            }
            TokenKind::KwFn | TokenKind::KwRt => {
                if t.kind == TokenKind::KwRt {
                    return Err(self.error(
                        Code::E0002,
                        t.span,
                        "an anonymous function cannot be `rt`; its `rt` comes from the expected type",
                    ));
                }
                self.bump();
                let params = self.parse_params(false)?;
                let ret = if self.eat(TokenKind::Arrow).is_some() { Some(self.parse_type()?) } else { None };
                let effects = self.parse_effect_row_opt()?;
                let body = self.parse_block_expr()?;
                ExprKind::Closure { params, ret, effects, body }
            }
            TokenKind::KwHandle => {
                self.bump();
                let body = self.parse_block_expr()?;
                self.expect(TokenKind::KwWith)?;
                let path = self.parse_path("a handler")?;
                let with = if self.at(TokenKind::LBrace) {
                    let items = self.parse_item_body(ItemCtx::InlineHandler)?;
                    HandlerRef::Inline { effect: path, items }
                } else if self.at(TokenKind::LParen) && !self.peek().space_before {
                    self.bump();
                    let args = self.parse_args()?;
                    HandlerRef::Named { path, args }
                } else {
                    HandlerRef::Named { path, args: Vec::new() }
                };
                ExprKind::Handle { body, with }
            }
            TokenKind::KwUnsafe => {
                self.bump();
                ExprKind::Unsafe(self.parse_block_expr()?)
            }
            TokenKind::KwPar => {
                self.bump();
                let var = self.parse_ident("replication index")?;
                self.expect(TokenKind::KwIn)?;
                let range = self.parse_head_expr(true)?;
                let (from, to) = match self.ast.expr(range).kind {
                    ExprKind::Range { lo, hi } => (lo, hi),
                    _ => {
                        let span = self.ast.expr(range).span;
                        return Err(self.error(Code::E0002, span, "`par` needs a range `a..b`"));
                    }
                };
                let body = self.parse_block_expr()?;
                ExprKind::Par { var, from, to, body }
            }
            TokenKind::Dot if self.peek2().kind == TokenKind::Int && !self.peek2().space_before => {
                // `.5` → `0.5`
                self.bump();
                let n = self.bump();
                let span = self.span_from(start);
                let fix = format!("0.{}", self.token_text(n));
                self.foreign(span, "a float literal needs digits on both sides of the point", &fix);
                ExprKind::Lit(Lit::Float { text: fix })
            }
            _ => return Err(self.unexpected("an expression")),
        };
        Ok(self.ast.add_expr(Expr { span: self.span_from(start), kind }))
    }

    /// After `(`: `()`, `(e)` or `(a, b, ...)`.
    fn parse_paren_rest(&mut self) -> PResult<ExprKind> {
        if self.eat(TokenKind::RParen).is_some() {
            return Ok(ExprKind::Tuple(Vec::new()));
        }
        let first = self.parse_consumed()?;
        if self.eat(TokenKind::Comma).is_none() {
            self.expect(TokenKind::RParen)?;
            return Ok(ExprKind::Paren(first));
        }
        let mut elems = vec![first];
        while !self.at(TokenKind::RParen) {
            elems.push(self.parse_consumed()?);
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        Ok(ExprKind::Tuple(elems))
    }

    /// After `[`: `[]`, `[a, b]` or `[e; N]`.
    fn parse_array_rest(&mut self) -> PResult<ExprKind> {
        if self.eat(TokenKind::RBracket).is_some() {
            return Ok(ExprKind::Array(Vec::new()));
        }
        let first = self.parse_consumed()?;
        if self.eat(TokenKind::Semi).is_some() {
            let len = self.parse_expr()?;
            self.expect(TokenKind::RBracket)?;
            return Ok(ExprKind::Repeat { elem: first, len });
        }
        let mut elems = vec![first];
        while self.eat(TokenKind::Comma).is_some() {
            if self.at(TokenKind::RBracket) {
                break;
            }
            elems.push(self.parse_consumed()?);
        }
        self.expect(TokenKind::RBracket)?;
        Ok(ExprKind::Array(elems))
    }

    fn parse_if(&mut self) -> PResult<ExprId> {
        let start = self.expect(TokenKind::KwIf)?.span.start;
        let cond = self.parse_head_expr(false)?;
        let then = self.parse_block_expr()?;
        let close_brace_end = self.last_end;
        // `else` must be on the same line as `}` (E0003).
        if self.at(TokenKind::Newline) && self.peek_past_newlines().kind == TokenKind::KwElse {
            let else_tok = self.peek_past_newlines();
            let span = Span::new(self.file, close_brace_end, else_tok.span.start);
            let d = Diagnostic::new(Code::E0003, span, "`else` must be on the same line as the closing `}`")
                .with_found("else")
                .with_fix(Fix::Replace { replace: " ".to_string() });
            self.report(d);
            self.skip_newlines();
        }
        let else_ = if self.eat(TokenKind::KwElse).is_some() {
            if self.at(TokenKind::KwIf) { Some(self.parse_if()?) } else { Some(self.parse_block_expr()?) }
        } else {
            None
        };
        let span = self.span_from(start);
        Ok(self.ast.add_expr(Expr { span, kind: ExprKind::If { cond, then, else_ } }))
    }

    // ------------------------------------------------------------ patterns

    fn parse_pattern(&mut self) -> PResult<PatId> {
        let start = self.peek().span.start;
        let first = self.parse_pattern_alt()?;
        if !self.at(TokenKind::Pipe) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(TokenKind::Pipe).is_some() {
            alts.push(self.parse_pattern_alt()?);
        }
        Ok(self.ast.add_pat(Pat { span: self.span_from(start), kind: PatKind::Or(alts) }))
    }

    fn parse_pattern_alt(&mut self) -> PResult<PatId> {
        let t = self.peek();
        let start = t.span.start;
        let kind = match t.kind {
            TokenKind::Underscore => {
                self.bump();
                PatKind::Wild
            }
            TokenKind::Minus if self.peek2().kind == TokenKind::Int => {
                self.bump();
                let n = self.bump();
                PatKind::Neg(self.int_lit(n))
            }
            TokenKind::Int => {
                self.bump();
                PatKind::Lit(self.int_lit(t))
            }
            TokenKind::Float | TokenKind::Minus => {
                return Err(self.error(
                    Code::E0002,
                    t.span,
                    "float literals cannot be patterns; compare in a guard (§7)",
                ));
            }
            TokenKind::Char => {
                self.bump();
                PatKind::Lit(Lit::Char(self.char_lit(t)))
            }
            TokenKind::Str => PatKind::Lit(Lit::Str(self.parse_str_lit()?)),
            TokenKind::KwTrue => {
                self.bump();
                PatKind::Lit(Lit::Bool(true))
            }
            TokenKind::KwFalse => {
                self.bump();
                PatKind::Lit(Lit::Bool(false))
            }
            TokenKind::LParen => {
                self.bump();
                self.with_nl(false, |p| {
                    let mut elems = Vec::new();
                    while !p.at(TokenKind::RParen) {
                        elems.push(p.parse_pattern()?);
                        if p.eat(TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                    p.expect(TokenKind::RParen)?;
                    Ok(PatKind::Tuple(elems))
                })?
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let path = self.parse_path("a pattern")?;
                if self.at(TokenKind::LParen) && !self.peek().space_before {
                    self.bump();
                    let elems = self.with_nl(false, |p| {
                        let mut elems = Vec::new();
                        while !p.at(TokenKind::RParen) {
                            elems.push(p.parse_pattern()?);
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RParen)?;
                        Ok(elems)
                    })?;
                    PatKind::TupleStruct { path, elems }
                } else if self.at(TokenKind::LBrace)
                    && path.segments.last().unwrap().name.starts_with(|c: char| c.is_ascii_uppercase())
                {
                    self.bump();
                    let fields = self.with_nl(false, |p| {
                        let mut fields = Vec::new();
                        while !p.at(TokenKind::RBrace) {
                            if p.at(TokenKind::DotDot) {
                                let t = p.peek();
                                return Err(p.error(
                                    Code::E0002,
                                    t.span,
                                    "struct patterns name every field; use `_` for the unused ones (§7)",
                                ));
                            }
                            let name = p.parse_ident("field name")?;
                            p.expect(TokenKind::Colon)?;
                            let pat = p.parse_pattern()?;
                            fields.push((name, pat));
                            if p.eat(TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                        p.expect(TokenKind::RBrace)?;
                        Ok(fields)
                    })?;
                    PatKind::Struct { path, fields }
                } else if path.segments.len() == 1
                    && path.segments[0].name.starts_with(|c: char| c.is_ascii_lowercase())
                {
                    PatKind::Bind(path.segments.into_iter().next().unwrap())
                } else {
                    PatKind::Path(path)
                }
            }
            _ => return Err(self.unexpected("a pattern")),
        };
        Ok(self.ast.add_pat(Pat { span: self.span_from(start), kind }))
    }

    // ------------------------------------------------------------ literals

    fn int_lit(&mut self, t: Token) -> Lit {
        let text = self.token_text(t);
        let digits: String = text.chars().filter(|&c| c != '_').collect();
        let parsed = if let Some(h) = digits.strip_prefix("0x") {
            u64::from_str_radix(h, 16)
        } else if let Some(b) = digits.strip_prefix("0b") {
            u64::from_str_radix(b, 2)
        } else {
            digits.parse::<u64>()
        };
        let value = match parsed {
            Ok(v) => v,
            Err(_) => {
                self.report(Diagnostic::new(
                    Code::E0408,
                    t.span,
                    "integer literal is larger than any integer type holds",
                ));
                u64::MAX
            }
        };
        Lit::Int { value, text: text.to_string() }
    }

    fn char_lit(&self, t: Token) -> char {
        let inner = &self.token_text(t)[1..];
        let inner = inner.strip_suffix('\'').unwrap_or(inner);
        let mut chars = inner.chars();
        match chars.next() {
            Some('\\') => unescape(&mut chars).unwrap_or('\u{FFFD}'),
            Some(c) => c,
            None => '\u{FFFD}',
        }
    }

    fn parse_str_lit(&mut self) -> PResult<StrLit> {
        let t = self.expect(TokenKind::Str)?;
        let raw = self.token_text(t);
        let inner = raw.strip_prefix('"').unwrap_or(raw);
        let inner = inner.strip_suffix('"').unwrap_or(inner);
        let base = t.span.start + 1;
        let mut segments = Vec::new();
        let mut text = String::new();
        let mut chars = inner.char_indices().peekable();
        while let Some((i, c)) = chars.next() {
            match c {
                '\\' => {
                    let mut rest = inner[i + 1..].chars();
                    if let Some(ch) = unescape(&mut rest) {
                        text.push(ch);
                        let consumed = inner[i + 1..].len() - rest.as_str().len();
                        for _ in inner[i + 1..i + 1 + consumed].chars() {
                            chars.next();
                        }
                    }
                }
                '{' if chars.peek().is_some_and(|&(_, n)| n == '{') => {
                    chars.next();
                    text.push('{');
                }
                '}' if chars.peek().is_some_and(|&(_, n)| n == '}') => {
                    chars.next();
                    text.push('}');
                }
                '{' => {
                    if !text.is_empty() {
                        segments.push(StrSeg::Text(std::mem::take(&mut text)));
                    }
                    let path_start = i + 1;
                    let mut path_end = path_start;
                    for (j, n) in chars.by_ref() {
                        if n == '}' {
                            path_end = j;
                            break;
                        }
                    }
                    let path_text = &inner[path_start..path_end];
                    let mut offset = base + path_start as u32;
                    let mut seg_spans = Vec::new();
                    for seg in path_text.split('.') {
                        let span = Span::new(self.file, offset, offset + seg.len() as u32);
                        seg_spans.push(Ident { name: seg.to_string(), span });
                        offset += seg.len() as u32 + 1;
                    }
                    let span = Span::new(self.file, base + path_start as u32, base + path_end as u32);
                    segments.push(StrSeg::Interp(Path { segments: seg_spans, span }));
                }
                _ => text.push(c),
            }
        }
        if !text.is_empty() || segments.is_empty() {
            segments.push(StrSeg::Text(text));
        }
        Ok(StrLit { segments, span: t.span })
    }
}

/// `\n` etc. after the backslash has been consumed (S-19).
fn unescape(chars: &mut std::str::Chars) -> Option<char> {
    match chars.next()? {
        'n' => Some('\n'),
        't' => Some('\t'),
        'r' => Some('\r'),
        '0' => Some('\0'),
        '\\' => Some('\\'),
        '"' => Some('"'),
        '\'' => Some('\''),
        'u' => {
            let rest = chars.as_str();
            let rest = rest.strip_prefix('{')?;
            let end = rest.find('}')?;
            let ch = u32::from_str_radix(&rest[..end], 16).ok().and_then(char::from_u32)?;
            for _ in 0..end + 2 {
                chars.next();
            }
            Some(ch)
        }
        _ => None,
    }
}

fn binop(kind: TokenKind) -> Option<BinOp> {
    use TokenKind::*;
    Some(match kind {
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Rem,
        PlusPercent => BinOp::WrapAdd,
        MinusPercent => BinOp::WrapSub,
        StarPercent => BinOp::WrapMul,
        PlusPipe => BinOp::SatAdd,
        MinusPipe => BinOp::SatSub,
        StarPipe => BinOp::SatMul,
        EqEq => BinOp::Eq,
        NotEq => BinOp::Ne,
        Lt => BinOp::Lt,
        LtEq => BinOp::Le,
        Gt => BinOp::Gt,
        GtEq => BinOp::Ge,
        AndAnd => BinOp::And,
        OrOr => BinOp::Or,
        Amp => BinOp::BitAnd,
        Pipe => BinOp::BitOr,
        Caret => BinOp::BitXor,
        Shl => BinOp::Shl,
        Shr => BinOp::Shr,
        _ => return None,
    })
}

fn is_item_start(kind: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        KwFn | KwRt
            | KwFlow
            | KwStruct
            | KwEnum
            | KwType
            | KwTrait
            | KwImpl
            | KwEffect
            | KwBlocking
            | KwHandler
            | KwConst
            | KwUse
            | KwExtern
            | KwTarget
            | KwTest
            | KwPub
            | At
            | DocComment
    )
}

/// A path or field chain (`f`, `a.b`, `self.x`): the only callee shapes for `~(` / `!(`.
fn is_name_expr(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Path(_) | ExprKind::Field { .. })
}

/// If `expr` is a dotted name chain whose last segment is UpperCamel, return it as a path.
fn struct_lit_path(ast: &Ast, expr: ExprId) -> Option<Path> {
    let mut segments = Vec::new();
    let mut cur = expr;
    loop {
        match &ast.expr(cur).kind {
            ExprKind::Field { base, name } => {
                segments.push(name.clone());
                cur = *base;
            }
            ExprKind::Path(p) if p.segments.len() == 1 => {
                segments.push(p.segments[0].clone());
                break;
            }
            _ => return None,
        }
    }
    segments.reverse();
    if !segments.last()?.name.starts_with(|c: char| c.is_ascii_uppercase()) {
        return None;
    }
    let span = ast.expr(expr).span;
    Some(Path { segments, span })
}

/// Keep only the earliest diagnostic of each top-level item (P-01). Diagnostics
/// outside every item are grouped together as one "item".
fn first_per_item(items: &[Span], mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics.sort_by_key(|d| (d.span.start, d.span.end));
    let mut seen: Vec<bool> = vec![false; items.len() + 1];
    let mut out = Vec::new();
    for d in diagnostics {
        let slot = items
            .iter()
            .position(|s| s.start <= d.span.start && d.span.start < s.end.max(s.start + 1))
            .unwrap_or(items.len());
        if !seen[slot] {
            seen[slot] = true;
            out.push(d);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId, Fix};

    #[test]
    fn const_type_arguments() {
        // S-24: integer literals (optionally negated) are const arguments; names stay types.
        let p = crate::parse(FileId(0), "fn f(r: Ring[F32, 4], s: Ring[F32, N], t: Ring[F32, -1]) {}\n");
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let d = crate::dump(&p.ast);
        assert!(d.contains("Ring[F32, 4]"), "{d}");
        assert!(d.contains("Ring[F32, N]"), "{d}");
        assert!(d.contains("Ring[F32, (neg 1)]"), "{d}");
    }

    use crate::dump;

    fn parse(src: &str) -> crate::Parsed {
        crate::parse(FileId(0), src)
    }

    fn codes(src: &str) -> Vec<Code> {
        parse(src).diagnostics.iter().map(|d| d.code).collect()
    }

    fn fixes(src: &str) -> Vec<String> {
        parse(src)
            .diagnostics
            .iter()
            .flat_map(|d| d.fixes.iter())
            .map(|f| match f {
                Fix::Replace { replace } => replace.clone(),
                _ => unreachable!(),
            })
            .collect()
    }

    /// Dump of the body of `fn f() { <src> }`.
    fn body(src: &str) -> String {
        let p = parse(&format!("fn f() {{\n{src}\n}}"));
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let d = dump(&p.ast);
        let d = d.trim_start_matches("(fn f()\n  ").trim_end_matches(")\n");
        let mut out = String::new();
        for (i, line) in d.lines().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            out.push_str(line.trim_start());
        }
        out
    }

    #[test]
    fn newline_continuation() {
        assert_eq!(body("let a = x +\n  y"), "(block (let a = (chain x + y)))");
        assert_eq!(body("let a = xs\n  .len()"), "(block (let a = (call (. xs len) ())))");
        assert_eq!(body("let a =\n  1"), "(block (let a = 1))");
        // Newlines are whitespace inside parentheses and brackets.
        assert_eq!(body("let a = f(1,\n  2)\nlet b = [1,\n 2]"), "(block (let a = (call f (1, 2))) (let b = [1, 2]))");
        // A newline without a continuation ends the statement.
        assert_eq!(body("let a = x\n-y"), "(block (let a = x) tail (neg y))");
    }

    #[test]
    fn tail_vs_statement() {
        assert_eq!(body("let a = 1\na"), "(block (let a = 1) tail a)");
        assert_eq!(body("f(1)\n"), "(block tail (call f (1)))");
        assert_eq!(body("return"), "(block (return))");
        assert_eq!(body("x = 2"), "(block (assign x 2))");
    }

    #[test]
    fn else_position() {
        assert!(codes("fn f() {\n  if c { a } else { b }\n}").is_empty());
        assert_eq!(codes("fn f() {\n  if c { a }\n  else { b }\n}"), vec![Code::E0003]);
        assert_eq!(
            body("if a { 1 } else if b { 2 } else { 3 }"),
            "(block tail (if a (block tail 1) else (if b (block tail 2) else (block tail 3))))"
        );
    }

    #[test]
    fn call_marks() {
        assert_eq!(body("saw~(f0)"), "(block tail (call~ saw (f0)))");
        assert_eq!(body("out.fill!(0.0)"), "(block tail (call! (. out fill) (0.0)))");
        assert_eq!(body("a.f!=b"), "(block tail (chain (. a f) != b))");
        assert_eq!(body("!(a && b)"), "(block tail (not ((chain a && b))))");
        assert_eq!(codes("fn f() {\n  saw ~(f0)\n}"), vec![Code::E0002]);
        assert_eq!(codes("fn f() {\n  saw~ (f0)\n}"), vec![Code::E0002]);
    }

    #[test]
    fn tuple_index_and_fields() {
        assert_eq!(body("t.0.1"), "(block tail (. (. t 0) 1))");
        assert_eq!(body("self.params[i].f0 = v"), "(block (assign (. (index (. self params) i) f0) v))");
    }

    #[test]
    fn struct_literals_and_heads() {
        assert_eq!(body("let p = Point { x: 1.0, y: 2.0 }"), "(block (let p = (struct Point x: 1.0 y: 2.0)))");
        assert_eq!(body("voice.Config {}"), "(block tail (struct voice.Config))");
        // S-08: no struct literal in a head expression.
        assert_eq!(
            body("if s == Shape.Circle { 1 } else { 2 }"),
            "(block tail (if (chain s == (. Shape Circle)) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(
            body("if f(Point { x: 1.0 }) { 1 } else { 2 }"),
            "(block tail (if (call f ((struct Point x: 1.0))) (block tail 1) else (block tail 2)))"
        );
        assert_eq!(body("while x { }"), "(block (while x (block)))");
    }

    #[test]
    fn ranges_only_in_heads() {
        assert_eq!(body("for i in 0..n { }"), "(block (for i in (range 0 n) (block)))");
        assert_eq!(
            body("let s = par i in 0..N { f~(i) }"),
            "(block (let s = (par i in 0..N (block tail (call~ f (i))))))"
        );
        assert_eq!(codes("fn f() {\n  let r = 0..n\n}"), vec![Code::E0002]);
        assert_eq!(codes("fn f() {\n  for i in 0..=n { }\n}"), vec![Code::E0020]);
    }

    #[test]
    fn precedence() {
        assert_eq!(body("-x.abs()"), "(block tail (neg (call (. x abs) ())))");
        assert_eq!(body("-x as F64"), "(block tail (as (neg x) F64))");
        assert_eq!(body("a + (x as F64)"), "(block tail (chain a + ((as x F64))))");
        assert_eq!(body("x?.y"), "(block tail (. (try x) y))");
    }

    #[test]
    fn patterns() {
        assert_eq!(body("let (a, b) = p"), "(block (let (tuple a b) = p))");
        assert_eq!(
            body("match v { Some(x) if x > 0 => x, None => 0, }"),
            "(block tail (match v Some(x) if (chain x > 0) => x None => 0))"
        );
        assert_eq!(
            body("match v { Point { x: px, y: _ } => px, _ => 0 }"),
            "(block tail (match v Point { x: px, y: _ } => px _ => 0))"
        );
        assert_eq!(
            body("match n { 1 | 2 => a, -1 => b, 'c' => d, _ => e }"),
            "(block tail (match n (1 | 2) => a -1 => b 'c' => d _ => e))"
        );
        assert_eq!(
            body("match s { Shape.Circle(r) => r, Shape.Rect(w, h) => w }"),
            "(block tail (match s Shape.Circle(r) => r Shape.Rect(w, h) => w))"
        );
    }

    #[test]
    fn items() {
        let src = "/// doc\n@derive(PartialEq, Eq)\npub struct Key[T: PartialOrd + Eq, const N: U32, e] {\n  id: U32,\n  xs: [T; N],\n}\n";
        assert_eq!(
            dump(&parse(src).ast),
            "(doc:1 @derive(PartialEq, Eq) pub struct Key[T: PartialOrd + Eq, const N: U32, effect e]\n  id: U32\n  xs: [T; N])\n"
        );
        let src = "pub fn map[T, U, e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e} { xs }";
        assert_eq!(
            dump(&parse(src).ast),
            "(pub fn map[T, U, effect e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e}\n  (block\n    tail xs))\n"
        );
        let src =
            "pub(pkg) type S = Buf[F32]\nconst X: (U32, F32) = (1, 2.0)\nuse a.b.{c, d}\ntest \"t\" { assert true }";
        let d = dump(&parse(src).ast);
        assert!(
            d.starts_with(
                "(pub(pkg) type S = Buf[F32])\n(const X: (U32, F32) = (tuple 1 2.0))\n(use a.b.{c, d})\n(test \"t\""
            ),
            "{d}"
        );
        let src = "pub trait Show {\n  fn show(self) -> Str uses {Alloc}\n  const ZERO: Self\n}\nimpl Show for Point {\n  fn show(self) -> Str uses {Alloc} { \"({self.x}, {self.y})\" }\n}";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        assert!(dump(&p.ast).contains("(block\n      tail \"({self.x}, {self.y})\"))"));
        let src = "handler arena(inout mem: Span[U8]): Alloc {\n  fn alloc(n: U32) -> U32 { n }\n}\nfn g() { handle { f() } with arena(inout scratch) }\nfn h() { handle { f() } with Fs { fn read(_: Path) -> Str { \"\" } } }";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
    }

    #[test]
    fn signatures_without_bodies() {
        assert!(codes("extern \"C\" lib \"x\" {\n  type Raw\n  rt fn f(h: Ptr[Raw]) uses {Alloc}\n}").is_empty());
        assert_eq!(codes("extern \"C\" lib \"x\" {\n  fn f() { }\n}"), vec![Code::E0002]);
        assert!(codes("target type Device\ntarget rt fn read(inout d: Device)").is_empty());
        assert_eq!(codes("fn f()\nfn g() { }"), vec![Code::E0002]);
        assert_eq!(codes("effect Log {\n  rt fn info(msg: Str)\n}"), vec![]);
    }

    #[test]
    fn foreign_forms() {
        assert_eq!(
            (codes("fn f() {\n  let x = 1;\n}"), fixes("fn f() {\n  let x = 1;\n}")),
            (vec![Code::E0020], vec!["".to_string()])
        );
        assert_eq!(fixes("fn f() {\n  std::math::exp(x)\n}"), vec![".".to_string()]);
        assert_eq!(fixes("fn f(x: Vec<T>) { }"), vec!["[T]".to_string()]);
        assert_eq!(fixes("fn f() {\n  g(&mut x)\n}"), vec!["inout x".to_string()]);
        assert_eq!(fixes("fn f() {\n  g(&x)\n}"), vec!["x".to_string()]);
        assert_eq!(fixes("fn f() {\n  let mut x = 1\n}"), vec!["var".to_string()]);
        assert!(dump(&parse("fn f() {\n  let mut x = 1\n}").ast).contains("(var x = 1)"));
        assert_eq!(fixes("fn f() {\n  loop { }\n}"), vec!["while true".to_string()]);
        assert_eq!(fixes("fn f(x: i32) -> usize { x }"), vec!["I32".to_string()]);
        assert_eq!(fixes("#[derive(PartialEq)]\nstruct A { }"), vec!["@derive(PartialEq)".to_string()]);
        assert_eq!(fixes("proc f(x: Sig[F32]) -> Sig[F32] { x }"), vec!["flow".to_string()]);
        assert_eq!(fixes("impl A {\n  fn f(mut self) { }\n}"), vec!["inout self".to_string()]);
        assert_eq!(fixes("fn f<T>(x: T) { }"), vec!["[T]".to_string()]);
        assert_eq!(fixes("fn f() {\n  let y = .5\n}"), vec!["0.5".to_string()]);
        assert_eq!(codes("fn f() {\n  for i in 0..=n { }\n}"), vec![Code::E0020]);
    }

    #[test]
    fn first_error_per_item_and_recovery() {
        let src = "fn a() {\n  let = 1\n  let = 2\n}\nfn b() { 1 }\nfn c() {\n  )\n}\n";
        let p = parse(src);
        let lines: Vec<(Code, u32)> = p.diagnostics.iter().map(|d| (d.code, d.span.start)).collect();
        assert_eq!(p.diagnostics.len(), 2, "{lines:?}");
        assert_eq!(p.ast.root.len(), 1); // only `b` survived
        assert!(dump(&p.ast).starts_with("(fn b()"));
        // An item with a lexer error and a parse error reports the earliest only.
        let p = parse("fn a() {\n  let s = \"abc\n  let = 1\n}");
        assert_eq!(p.diagnostics.len(), 1);
        assert_eq!(p.diagnostics[0].code, Code::E0001);
    }

    #[test]
    fn literals() {
        assert_eq!(body("let s = \"a\\nb {{x}} {p.q}\""), "(block (let s = \"a\\nb {{x}} {p.q}\"))");
        assert_eq!(body("let c = '\\u{1F600}'"), "(block (let c = '\\u{1f600}'))");
        assert_eq!(body("let n = 0xFF + 1_000"), "(block (let n = (chain 255 + 1000)))");
        assert_eq!(codes("fn f() {\n  let n = 99999999999999999999\n}"), vec![Code::E0408]);
        assert_eq!(body("Ok(())"), "(block tail (call Ok ((tuple))))");
    }

    #[test]
    fn closures_and_args() {
        assert_eq!(
            body("xs.map(fn(x) { x * 2.0 })"),
            "(block tail (call (. xs map) ((fn(x) (block tail (chain x * 2.0))))))"
        );
        assert_eq!(body("f(inout a, move b, inout [c, d])"), "(block tail (call f (inout a, move b, inout [c, d])))");
        assert_eq!(
            body("fn(move v: S) -> U64 uses {Sync} { v }"),
            "(block tail (fn(move v: S) -> U64 uses {Sync} (block tail v)))"
        );
    }

    #[test]
    fn move_in_consuming_positions() {
        // S-21 (§5.2): `move x` as an expression form.
        let src = "fn f(move b: Buf[F32]) {\n  let y = move b\n  var v = move y\n  v = move b\n  let t = (move v, 1)\n  let a = [move b, move v]\n  let s = Box { b: move b }\n  match move b {\n    _ => 1,\n  }\n  take(move b)\n}\n";
        assert!(codes(src).is_empty(), "{:?}", crate::parse(FileId(0), src).diagnostics);
        let d = crate::dump(&crate::parse(FileId(0), src).ast);
        assert!(d.contains("(let y = (move b))"), "{d}");
        assert!(d.contains("(match (move b)"), "{d}");
        // Elsewhere it is E0002.
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  return move b\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  move b\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: U32) -> U32 {\n  let y = 1 + move b\n  y\n}\n"), vec![Code::E0002]);
        assert_eq!(codes("fn f(move b: Bool) -> U32 {\n  if move b { 1 } else { 2 }\n}\n"), vec![Code::E0002]);
    }
}
