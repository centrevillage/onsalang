//! Compact S-expression printer of the AST, for tests and `onsa dump --ast`.

use std::fmt::Write;

use crate::ast::*;

pub fn dump(ast: &Ast) -> String {
    let mut d = Dumper { ast, out: String::new(), indent: 0 };
    for &item in &ast.root {
        d.item(item);
        d.out.push('\n');
    }
    d.out
}

/// One item, without a trailing newline (used by `diff --ast`).
pub fn dump_item(ast: &Ast, id: ItemId) -> String {
    let mut d = Dumper { ast, out: String::new(), indent: 0 };
    d.item(id);
    d.out
}

/// One statement (used by `diff --ast` to locate the first change in a body).
pub fn dump_stmt(ast: &Ast, id: StmtId) -> String {
    let mut d = Dumper { ast, out: String::new(), indent: 0 };
    d.stmt(id);
    d.out
}

/// One expression.
pub fn dump_expr(ast: &Ast, id: ExprId) -> String {
    let mut d = Dumper { ast, out: String::new(), indent: 0 };
    d.expr(id);
    d.out
}

/// One type.
pub fn dump_type(ast: &Ast, id: TypeId) -> String {
    let mut d = Dumper { ast, out: String::new(), indent: 0 };
    d.ty(id);
    d.out
}

struct Dumper<'a> {
    ast: &'a Ast,
    out: String,
    indent: usize,
}

impl Dumper<'_> {
    fn line(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    fn nested(&mut self, f: impl FnOnce(&mut Self)) {
        self.indent += 1;
        self.line();
        f(self);
        self.indent -= 1;
    }

    fn path(&mut self, p: &Path) {
        let names: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        self.out.push_str(&names.join("."));
    }

    fn vis(&mut self, v: Vis) {
        match v {
            Vis::Private => {}
            Vis::Pkg => self.out.push_str("pub(pkg) "),
            Vis::Pub => self.out.push_str("pub "),
        }
    }

    fn item(&mut self, id: ItemId) {
        let item = self.ast.item(id);
        self.out.push('(');
        if !item.doc.is_empty() {
            let _ = write!(self.out, "doc:{} ", item.doc.len());
        }
        for a in &item.attrs {
            self.attr(a);
            self.out.push(' ');
        }
        self.vis(item.vis);
        self.item_kind(&item.kind);
        self.out.push(')');
    }

    fn attr(&mut self, a: &Attr) {
        let _ = write!(self.out, "@{}", a.name.name);
        if !a.args.is_empty() {
            self.out.push('(');
            for (i, arg) in a.args.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                match arg {
                    AttrArg::Named { key, value } => {
                        let _ = write!(self.out, "{}: ", key.name);
                        self.expr(*value);
                    }
                    AttrArg::Path(p) => self.path(p),
                    AttrArg::Str(s) => self.str_lit(s),
                }
            }
            self.out.push(')');
        }
    }

    fn item_kind(&mut self, kind: &ItemKind) {
        match kind {
            ItemKind::Fn(f) => self.fn_decl(f),
            ItemKind::Flow(f) => {
                let _ = write!(self.out, "flow {}", f.name.name);
                self.params(&f.params);
                self.out.push_str(" -> ");
                self.ty(f.ret);
                self.nested(|d| d.expr(f.body));
            }
            ItemKind::Struct(s) => {
                let _ = write!(self.out, "struct {}", s.name.name);
                self.generics(&s.generics);
                match &s.kind {
                    StructKind::Named(fields) => {
                        for f in fields {
                            self.nested(|d| {
                                d.vis(f.vis);
                                let _ = write!(d.out, "{}: ", f.name.name);
                                d.ty(f.ty);
                            });
                        }
                    }
                    StructKind::Tuple(t) => {
                        self.out.push('(');
                        self.ty(*t);
                        self.out.push(')');
                    }
                }
            }
            ItemKind::Enum(e) => {
                let _ = write!(self.out, "enum {}", e.name.name);
                self.generics(&e.generics);
                for v in &e.variants {
                    self.nested(|d| {
                        d.out.push_str(&v.name.name);
                        if !v.fields.is_empty() {
                            d.out.push('(');
                            d.comma(&v.fields, |d, t| d.ty(*t));
                            d.out.push(')');
                        }
                    });
                }
            }
            ItemKind::TypeAlias { name, ty } => {
                let _ = write!(self.out, "type {} = ", name.name);
                self.ty(*ty);
            }
            ItemKind::OpaqueType { name } => {
                let _ = write!(self.out, "type {}", name.name);
            }
            ItemKind::Trait(t) => {
                let _ = write!(self.out, "trait {}", t.name.name);
                self.generics(&t.generics);
                for &i in &t.items {
                    self.nested(|d| d.item(i));
                }
            }
            ItemKind::Impl(i) => {
                self.out.push_str("impl");
                self.generics(&i.generics);
                self.out.push(' ');
                if let Some(t) = &i.trait_ {
                    self.path(t);
                    self.out.push_str(" for ");
                }
                self.ty(i.self_ty);
                for &it in &i.items {
                    self.nested(|d| d.item(it));
                }
            }
            ItemKind::Effect(e) => {
                if e.blocking {
                    self.out.push_str("blocking ");
                }
                let _ = write!(self.out, "effect {}", e.name.name);
                for &i in &e.ops {
                    self.nested(|d| d.item(i));
                }
            }
            ItemKind::Handler(h) => {
                let _ = write!(self.out, "handler {}", h.name.name);
                if !h.params.is_empty() {
                    self.params(&h.params);
                }
                self.out.push_str(": ");
                self.path(&h.effect);
                for &i in &h.items {
                    self.nested(|d| d.item(i));
                }
            }
            ItemKind::Const(c) => {
                let _ = write!(self.out, "const {}: ", c.name.name);
                self.ty(c.ty);
                if let Some(v) = c.value {
                    self.out.push_str(" = ");
                    self.expr(v);
                }
            }
            ItemKind::Use(u) => {
                self.out.push_str("use ");
                self.path(&u.path);
                if let Some(names) = &u.names {
                    let names: Vec<&str> = names.iter().map(|n| n.name.as_str()).collect();
                    let _ = write!(self.out, ".{{{}}}", names.join(", "));
                }
            }
            ItemKind::Extern(e) => {
                self.out.push_str("extern ");
                self.str_lit(&e.abi);
                self.out.push_str(" lib ");
                self.str_lit(&e.lib);
                for &i in &e.items {
                    self.nested(|d| d.item(i));
                }
            }
            ItemKind::Target(inner) => {
                self.out.push_str("target ");
                self.item_kind(inner);
            }
            ItemKind::Test { name, body } => {
                self.out.push_str("test ");
                self.str_lit(name);
                self.nested(|d| d.expr(*body));
            }
        }
    }

    fn fn_decl(&mut self, f: &FnDecl) {
        if f.rt {
            self.out.push_str("rt ");
        }
        let _ = write!(self.out, "fn {}", f.name.name);
        self.generics(&f.generics);
        self.params(&f.params);
        if let Some(r) = f.ret {
            self.out.push_str(" -> ");
            self.ty(r);
        }
        if let Some(e) = &f.effects {
            self.effects(e);
        }
        if let Some(b) = f.body {
            self.nested(|d| d.expr(b));
        }
    }

    fn effects(&mut self, e: &EffectRow) {
        self.out.push_str(" uses {");
        let mut first = true;
        for p in &e.effects {
            if !first {
                self.out.push_str(", ");
            }
            first = false;
            self.path(p);
        }
        self.out.push('}');
    }

    fn generics(&mut self, g: &[GenericParam]) {
        if g.is_empty() {
            return;
        }
        self.out.push('[');
        for (i, p) in g.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            match p {
                GenericParam::Type { name, bounds } => {
                    self.out.push_str(&name.name);
                    if !bounds.is_empty() {
                        self.out.push_str(": ");
                        for (j, b) in bounds.iter().enumerate() {
                            if j > 0 {
                                self.out.push_str(" + ");
                            }
                            if b.relaxed {
                                self.out.push('?');
                            }
                            self.path(&b.path);
                        }
                    }
                }
                GenericParam::Const { name, ty } => {
                    let _ = write!(self.out, "const {}: ", name.name);
                    self.ty(*ty);
                }
                GenericParam::Effect { name } => {
                    let _ = write!(self.out, "effect {}", name.name);
                }
            }
        }
        self.out.push(']');
    }

    fn params(&mut self, ps: &[Param]) {
        self.out.push('(');
        for (i, p) in ps.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            for a in &p.attrs {
                self.attr(a);
                self.out.push(' ');
            }
            self.mode(p.mode);
            match &p.name {
                ParamName::Ident(id) => self.out.push_str(&id.name),
                ParamName::Wild(_) => self.out.push('_'),
                ParamName::SelfParam(_) => self.out.push_str("self"),
            }
            if let Some(t) = p.ty {
                self.out.push_str(": ");
                self.ty(t);
            }
        }
        self.out.push(')');
    }

    fn mode(&mut self, m: Mode) {
        match m {
            Mode::Borrow => {}
            Mode::Inout => self.out.push_str("inout "),
            Mode::Move => self.out.push_str("move "),
        }
    }

    fn comma<T>(&mut self, xs: &[T], f: impl Fn(&mut Self, &T)) {
        for (i, x) in xs.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            f(self, x);
        }
    }

    fn ty(&mut self, id: TypeId) {
        match &self.ast.ty(id).kind {
            TypeKind::Path { path, args } => {
                self.path(path);
                if !args.is_empty() {
                    self.out.push('[');
                    self.comma(args, |d, t| d.ty(*t));
                    self.out.push(']');
                }
            }
            TypeKind::Array { elem, len } => {
                self.out.push('[');
                self.ty(*elem);
                self.out.push_str("; ");
                self.expr(*len);
                self.out.push(']');
            }
            TypeKind::Unit => self.out.push_str("()"),
            TypeKind::Tuple(elems) => {
                self.out.push('(');
                self.comma(elems, |d, t| d.ty(*t));
                self.out.push(')');
            }
            TypeKind::Fn { rt, params, ret, effects } => {
                if *rt {
                    self.out.push_str("rt ");
                }
                self.out.push_str("fn(");
                self.comma(params, |d, (m, t)| {
                    d.mode(*m);
                    d.ty(*t);
                });
                self.out.push(')');
                if let Some(r) = ret {
                    self.out.push_str(" -> ");
                    self.ty(*r);
                }
                if let Some(e) = effects {
                    self.effects(e);
                }
            }
        }
    }

    fn str_lit(&mut self, s: &StrLit) {
        self.out.push('"');
        for seg in &s.segments {
            match seg {
                StrSeg::Text(t) => {
                    for c in t.chars() {
                        match c {
                            '\n' => self.out.push_str("\\n"),
                            '"' => self.out.push_str("\\\""),
                            '{' => self.out.push_str("{{"),
                            '}' => self.out.push_str("}}"),
                            c => self.out.push(c),
                        }
                    }
                }
                StrSeg::Interp(p) => {
                    self.out.push('{');
                    self.path(p);
                    self.out.push('}');
                }
            }
        }
        self.out.push('"');
    }

    fn lit(&mut self, l: &Lit) {
        match l {
            Lit::Int { value, .. } => {
                let _ = write!(self.out, "{value}");
            }
            Lit::Float { text } => self.out.push_str(text),
            Lit::Char(c) => {
                let _ = write!(self.out, "'{}'", c.escape_default());
            }
            Lit::Str(s) => self.str_lit(s),
            Lit::Bool(b) => {
                let _ = write!(self.out, "{b}");
            }
        }
    }

    fn block(&mut self, b: &Block) {
        self.out.push_str("(block");
        for &s in &b.stmts {
            self.nested(|d| d.stmt(s));
        }
        if let Some(t) = b.tail {
            self.nested(|d| {
                d.out.push_str("tail ");
                d.expr(t);
            });
        }
        self.out.push(')');
    }

    fn stmt(&mut self, id: StmtId) {
        match &self.ast.stmt(id).kind {
            StmtKind::Let { pat, ty, init } => {
                self.out.push_str("(let ");
                self.pat(*pat);
                if let Some(t) = ty {
                    self.out.push_str(": ");
                    self.ty(*t);
                }
                self.out.push_str(" = ");
                self.expr(*init);
                self.out.push(')');
            }
            StmtKind::Var { name, ty, init } => {
                let _ = write!(self.out, "(var {}", name.name);
                if let Some(t) = ty {
                    self.out.push_str(": ");
                    self.ty(*t);
                }
                self.out.push_str(" = ");
                self.expr(*init);
                self.out.push(')');
            }
            StmtKind::Assign { target, value } => {
                self.out.push_str("(assign ");
                self.expr(*target);
                self.out.push(' ');
                self.expr(*value);
                self.out.push(')');
            }
            StmtKind::For { pat, moved, iter, body } => {
                self.out.push_str("(for ");
                self.pat(*pat);
                self.out.push_str(if *moved { " in move " } else { " in " });
                self.expr(*iter);
                self.out.push(' ');
                self.expr(*body);
                self.out.push(')');
            }
            StmtKind::While { cond, body } => {
                self.out.push_str("(while ");
                self.expr(*cond);
                self.out.push(' ');
                self.expr(*body);
                self.out.push(')');
            }
            StmtKind::Break => self.out.push_str("(break)"),
            StmtKind::Continue => self.out.push_str("(continue)"),
            StmtKind::Return(e) => {
                self.out.push_str("(return");
                if let Some(e) = e {
                    self.out.push(' ');
                    self.expr(*e);
                }
                self.out.push(')');
            }
            StmtKind::Assert(e) => {
                self.out.push_str("(assert ");
                self.expr(*e);
                self.out.push(')');
            }
            StmtKind::Expr(e) => self.expr(*e),
        }
    }

    fn args(&mut self, args: &[Arg]) {
        self.out.push('(');
        self.comma(args, |d, a| {
            d.mode(a.mode);
            d.expr(a.expr);
        });
        self.out.push(')');
    }

    fn expr(&mut self, id: ExprId) {
        match &self.ast.expr(id).kind {
            ExprKind::Lit(l) => self.lit(l),
            ExprKind::Path(p) => self.path(p),
            ExprKind::Hole => self.out.push('_'),
            ExprKind::Paren(e) => {
                self.out.push('(');
                self.expr(*e);
                self.out.push(')');
            }
            ExprKind::Tuple(elems) => {
                self.out.push_str("(tuple");
                for &e in elems {
                    self.out.push(' ');
                    self.expr(e);
                }
                self.out.push(')');
            }
            ExprKind::Array(elems) => {
                self.out.push('[');
                self.comma(elems, |d, e| d.expr(*e));
                self.out.push(']');
            }
            ExprKind::Repeat { elem, len } => {
                self.out.push('[');
                self.expr(*elem);
                self.out.push_str("; ");
                self.expr(*len);
                self.out.push(']');
            }
            ExprKind::Struct { path, fields } => {
                self.out.push_str("(struct ");
                self.path(path);
                for (name, value) in fields {
                    let _ = write!(self.out, " {}: ", name.name);
                    self.expr(*value);
                }
                self.out.push(')');
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::If { cond, then, else_ } => {
                self.out.push_str("(if ");
                self.expr(*cond);
                self.out.push(' ');
                self.expr(*then);
                if let Some(e) = else_ {
                    self.out.push_str(" else ");
                    self.expr(*e);
                }
                self.out.push(')');
            }
            ExprKind::Match { scrutinee, arms } => {
                self.out.push_str("(match ");
                self.expr(*scrutinee);
                for arm in arms {
                    self.nested(|d| {
                        d.pat(arm.pat);
                        if let Some(g) = arm.guard {
                            d.out.push_str(" if ");
                            d.expr(g);
                        }
                        d.out.push_str(" => ");
                        d.expr(arm.body);
                    });
                }
                self.out.push(')');
            }
            ExprKind::Closure { params, ret, effects, body } => {
                self.out.push_str("(fn");
                self.params(params);
                if let Some(r) = ret {
                    self.out.push_str(" -> ");
                    self.ty(*r);
                }
                if let Some(e) = effects {
                    self.effects(e);
                }
                self.out.push(' ');
                self.expr(*body);
                self.out.push(')');
            }
            ExprKind::Handle { body, with } => {
                self.out.push_str("(handle ");
                self.expr(*body);
                self.out.push_str(" with ");
                match with {
                    HandlerRef::Named { path, args } => {
                        self.path(path);
                        if !args.is_empty() {
                            self.args(args);
                        }
                    }
                    HandlerRef::Inline { effect, items } => {
                        self.path(effect);
                        for &i in items {
                            self.nested(|d| d.item(i));
                        }
                    }
                }
                self.out.push(')');
            }
            ExprKind::Unsafe(e) => {
                self.out.push_str("(unsafe ");
                self.expr(*e);
                self.out.push(')');
            }
            ExprKind::Par { var, from, to, body } => {
                let _ = write!(self.out, "(par {} in ", var.name);
                self.expr(*from);
                self.out.push_str("..");
                self.expr(*to);
                self.out.push(' ');
                self.expr(*body);
                self.out.push(')');
            }
            ExprKind::Binary { operands, ops } => {
                self.out.push_str("(chain ");
                self.expr(operands[0]);
                for (i, (op, _)) in ops.iter().enumerate() {
                    let _ = write!(self.out, " {} ", op.symbol());
                    self.expr(operands[i + 1]);
                }
                self.out.push(')');
            }
            ExprKind::Cast { expr, ty } => {
                self.out.push_str("(as ");
                self.expr(*expr);
                self.out.push(' ');
                self.ty(*ty);
                self.out.push(')');
            }
            ExprKind::Unary { op, expr } => {
                self.out.push('(');
                self.out.push_str(match op {
                    UnOp::Neg => "neg ",
                    UnOp::Not => "not ",
                });
                self.expr(*expr);
                self.out.push(')');
            }
            ExprKind::Call { callee, kind, args } => {
                self.out.push_str(match kind {
                    CallKind::Plain => "(call ",
                    CallKind::Flow => "(call~ ",
                    CallKind::Bang => "(call! ",
                });
                self.expr(*callee);
                self.out.push(' ');
                self.args(args);
                self.out.push(')');
            }
            ExprKind::Field { base, name } => {
                self.out.push_str("(. ");
                self.expr(*base);
                let _ = write!(self.out, " {})", name.name);
            }
            ExprKind::TupleIndex { base, index, .. } => {
                self.out.push_str("(. ");
                self.expr(*base);
                let _ = write!(self.out, " {index})");
            }
            ExprKind::Index { base, index } => {
                self.out.push_str("(index ");
                self.expr(*base);
                self.out.push(' ');
                self.expr(*index);
                self.out.push(')');
            }
            ExprKind::Try(e) => {
                self.out.push_str("(try ");
                self.expr(*e);
                self.out.push(')');
            }
            ExprKind::Range { lo, hi } => {
                self.out.push_str("(range ");
                self.expr(*lo);
                self.out.push(' ');
                self.expr(*hi);
                self.out.push(')');
            }
        }
    }

    fn pat(&mut self, id: PatId) {
        match &self.ast.pat(id).kind {
            PatKind::Wild => self.out.push('_'),
            PatKind::Bind(i) => self.out.push_str(&i.name),
            PatKind::Lit(l) => self.lit(l),
            PatKind::Neg(l) => {
                self.out.push('-');
                self.lit(l);
            }
            PatKind::Path(p) => self.path(p),
            PatKind::TupleStruct { path, elems } => {
                self.path(path);
                self.out.push('(');
                self.comma(elems, |d, p| d.pat(*p));
                self.out.push(')');
            }
            PatKind::Tuple(elems) => {
                self.out.push_str("(tuple");
                for &p in elems {
                    self.out.push(' ');
                    self.pat(p);
                }
                self.out.push(')');
            }
            PatKind::Struct { path, fields } => {
                self.path(path);
                self.out.push_str(" {");
                for (i, (name, p)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.out.push(',');
                    }
                    let _ = write!(self.out, " {}: ", name.name);
                    self.pat(*p);
                }
                self.out.push_str(" }");
            }
            PatKind::Or(alts) => {
                self.out.push('(');
                for (i, &p) in alts.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(" | ");
                    }
                    self.pat(p);
                }
                self.out.push(')');
            }
        }
    }
}
