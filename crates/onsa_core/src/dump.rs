//! Deterministic text form of a Core module (`onsa dump --core`), for golden
//! tests and for reading what the backends get.

use std::collections::HashSet;
use std::fmt::Write;

use crate::ir::*;

pub fn dump(m: &Module) -> String {
    let mut d = Dumper::new(m);
    for t in &m.types {
        d.type_def(t);
    }
    for c in &m.consts {
        d.const_def(c);
    }
    for f in &m.fns {
        d.fn_def(f);
    }
    d.out
}

/// The `const`s and functions named `name`, as in the dump (the part of a
/// module a verifier error names, R-82).
pub fn dump_item(m: &Module, name: &str) -> String {
    let mut d = Dumper::new(m);
    for c in m.consts.iter().filter(|c| c.name == name) {
        d.const_def(c);
    }
    for f in m.fns.iter().filter(|f| f.name == name) {
        d.fn_def(f);
    }
    d.out
}

/// One type, as in the dump.
pub fn type_name(m: &Module, ty: CTy) -> String {
    let mut d = Dumper::new(m);
    d.ty(ty);
    d.out
}

/// A type of the kind `k`, as in the dump, whether `m` has it or not.
pub fn kind_name(m: &Module, k: &TyKind) -> String {
    let mut d = Dumper::new(m);
    d.kind(k);
    d.out
}

struct Dumper<'a> {
    m: &'a Module,
    out: String,
    indent: usize,
    locals: &'a [Local],
    /// The names of more than one of `locals`, made once for the function (R-498).
    dups: HashSet<&'a str>,
    /// The id of the type whose part is being written: a part is before it.
    below: usize,
}

impl<'a> Dumper<'a> {
    fn new(m: &'a Module) -> Self {
        Dumper { m, out: String::new(), indent: 0, locals: &[], dups: HashSet::new(), below: usize::MAX }
    }

    fn nl(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    /// A type out of range, or a part not before its type (a broken table,
    /// V-20), is marked, so the dump ends on any table.
    fn ty(&mut self, t: CTy) {
        let m = self.m;
        let Some(k) = m.tys.kinds().get(t.index()).filter(|_| t.index() < self.below) else {
            let _ = write!(self.out, "<bad ty {}>", t.index());
            return;
        };
        let outer = std::mem::replace(&mut self.below, t.index());
        self.kind(k);
        self.below = outer;
    }

    fn kind(&mut self, k: &TyKind) {
        match k {
            TyKind::Int(k) => self.out.push_str(k.name()),
            TyKind::Float(k) => self.out.push_str(k.name()),
            TyKind::Bool => self.out.push_str("Bool"),
            TyKind::Char => self.out.push_str("Char"),
            TyKind::Unit => self.out.push_str("()"),
            TyKind::Array(e, n) => {
                self.out.push('[');
                self.ty(*e);
                let _ = write!(self.out, "; {n}]");
            }
            TyKind::Tuple(ts) => {
                self.out.push('(');
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.ty(*t);
                }
                self.out.push(')');
            }
            TyKind::Struct(id) | TyKind::Enum(id) => {
                let name = self.type_ref_name(*id);
                self.out.push_str(&name);
            }
            TyKind::Span(e) => {
                self.out.push_str("Span[");
                self.ty(*e);
                self.out.push(']');
            }
            TyKind::Buf(e) => {
                self.out.push_str("Buf[");
                self.ty(*e);
                self.out.push(']');
            }
            TyKind::FnPtr(sig) => {
                self.out.push_str(if sig.rt { "rt fn(" } else { "fn(" });
                for (i, (m, t)) in sig.params.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.mode(*m);
                    self.ty(*t);
                }
                self.out.push_str(") -> ");
                self.ty(sig.ret);
            }
        }
    }

    fn mode(&mut self, m: Mode) {
        match m {
            Mode::Borrow => {}
            Mode::Inout => self.out.push_str("inout "),
            Mode::Move => self.out.push_str("move "),
        }
    }

    fn type_def(&mut self, t: &TypeDef) {
        let _ = write!(self.out, "type {} = ", t.name);
        match &t.kind {
            TypeDefKind::Struct { fields } => {
                self.out.push_str("struct {");
                for (i, (n, ty)) in fields.iter().enumerate() {
                    self.out.push_str(if i > 0 { ", " } else { " " });
                    let _ = write!(self.out, "{n}: ");
                    self.ty(*ty);
                }
                self.out.push_str(if fields.is_empty() { "}" } else { " }" });
            }
            TypeDefKind::Enum { variants } => {
                self.out.push_str("enum {");
                for (i, (n, tys)) in variants.iter().enumerate() {
                    self.out.push_str(if i > 0 { ", " } else { " " });
                    self.out.push_str(n);
                    if !tys.is_empty() {
                        self.out.push('(');
                        for (j, t) in tys.iter().enumerate() {
                            if j > 0 {
                                self.out.push_str(", ");
                            }
                            self.ty(*t);
                        }
                        self.out.push(')');
                    }
                }
                self.out.push_str(" }");
            }
            TypeDefKind::Opaque => self.out.push_str("opaque"),
        }
        self.out.push('\n');
    }

    /// A type of the module, or `None` for an id out of range (a broken
    /// Core the verifier reports must still dump, R-82).
    fn type_def_of(&self, id: TypeId) -> Option<&'a TypeDef> {
        self.m.types.get(id.0 as usize)
    }

    fn type_ref_name(&self, id: TypeId) -> String {
        match self.type_def_of(id) {
            Some(d) => d.name.clone(),
            None => format!("<bad type {}>", id.0),
        }
    }

    /// The name of variant `tag` of an enum (the tag itself when it is not one).
    fn variant_name(def: Option<&TypeDef>, tag: u32) -> String {
        match def.map(|d| &d.kind) {
            Some(TypeDefKind::Enum { variants }) => match variants.get(tag as usize) {
                Some((n, _)) => n.clone(),
                None => format!("<bad variant {tag}>"),
            },
            _ => tag.to_string(),
        }
    }

    fn local(&mut self, l: LocalId) {
        let Some(local) = self.locals.get(l.0 as usize) else {
            let _ = write!(self.out, "<bad local {}>", l.0);
            return;
        };
        let name = &local.name;
        if self.dups.contains(name.as_str()) || name.is_empty() {
            let _ = write!(self.out, "{name}@{}", l.0);
        } else {
            self.out.push_str(name);
        }
    }

    fn const_def(&mut self, c: &ConstDef) {
        self.out.push_str("const ");
        self.out.push_str(&c.name);
        self.out.push_str(": ");
        self.ty(c.ty);
        self.out.push_str(" = ");
        self.expr(&c.init);
        self.out.push('\n');
    }

    fn fn_def(&mut self, f: &'a FnDef) {
        self.locals = &f.locals;
        let mut seen = HashSet::new();
        self.dups = f.locals.iter().map(|l| l.name.as_str()).filter(|n| !seen.insert(*n)).collect();
        self.out.push_str(if f.rt { "rt fn " } else { "fn " });
        self.out.push_str(&f.name);
        self.out.push('(');
        for (i, p) in f.params.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.mode(p.mode);
            self.local(p.local);
            self.out.push_str(": ");
            self.ty(p.ty);
        }
        self.out.push_str(") -> ");
        self.ty(f.ret);
        if f.sret {
            self.out.push_str(" sret");
        }
        let Some(body) = &f.body else {
            self.out.push_str(" = extern\n");
            return;
        };
        self.out.push_str(" {");
        self.indent += 1;
        if !f.hoisted.is_empty() {
            self.nl();
            self.out.push_str("hoisted ");
            for (i, l) in f.hoisted.iter().enumerate() {
                self.out.push_str(if i > 0 { ", " } else { "" });
                self.local(*l);
            }
        }
        self.block_body(body);
        self.indent -= 1;
        self.nl();
        self.out.push_str("}\n");
        self.locals = &[];
    }

    fn block_body(&mut self, b: &Block) {
        for s in &b.stmts {
            self.nl();
            self.stmt(s);
        }
        if let Some(v) = &b.value {
            self.nl();
            self.expr(v);
        }
    }

    fn block(&mut self, b: &Block) {
        self.out.push('{');
        self.indent += 1;
        self.block_body(b);
        self.indent -= 1;
        self.nl();
        self.out.push('}');
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let(l, e) => {
                self.out.push_str("let ");
                self.typed(*l);
                self.out.push_str(" = ");
                self.expr(e);
            }
            StmtKind::Assign(p, e) => {
                self.place(p);
                self.out.push_str(" = ");
                self.expr(e);
            }
            // `alias r: T = g[i]`, `alias inout r: T = g[i]` of a write through it.
            StmtKind::Alias(l, p) => {
                let write = self.locals.get(l.0 as usize).map(|l| l.kind) == Some(LocalKind::Alias { write: true });
                self.out.push_str(if write { "alias inout " } else { "alias " });
                self.typed(*l);
                self.out.push_str(" = ");
                self.place(p);
            }
            StmtKind::Expr(e) => self.expr(e),
            StmtKind::If(c, t, e) => {
                self.out.push_str("if ");
                self.expr(c);
                self.out.push(' ');
                self.block(t);
                if !e.stmts.is_empty() || e.value.is_some() {
                    self.out.push_str(" else ");
                    self.block(e);
                }
            }
            StmtKind::While(c, b) => {
                self.out.push_str("while ");
                self.expr(c);
                self.out.push(' ');
                self.block(b);
            }
            StmtKind::ForRange { local, lo, hi, body: b, inclusive } => {
                self.out.push_str("for ");
                self.local(*local);
                self.out.push_str(" in ");
                self.expr(lo);
                self.out.push_str(if *inclusive { "..=" } else { ".." });
                self.expr(hi);
                self.out.push(' ');
                self.block(b);
            }
            StmtKind::Break => self.out.push_str("break"),
            StmtKind::Continue => self.out.push_str("continue"),
            StmtKind::Return(e) => {
                self.out.push_str("return");
                if let Some(e) = e {
                    self.out.push(' ');
                    self.expr(e);
                }
            }
        }
    }

    /// `l: T`, the local and its type.
    fn typed(&mut self, l: LocalId) {
        self.local(l);
        self.out.push_str(": ");
        match self.locals.get(l.0 as usize) {
            Some(local) => self.ty(local.ty),
            None => {
                let _ = write!(self.out, "<bad local {}>", l.0);
            }
        }
    }

    /// `[i]`, or `[known i]` for an index known in range (S-196).
    fn index(&mut self, i: &Expr, bounds: Bounds) {
        self.out.push_str(match bounds {
            Bounds::Checked => "[",
            Bounds::Known => "[known ",
        });
        self.expr(i);
        self.out.push(']');
    }

    fn place(&mut self, p: &Place) {
        match p {
            Place::Local(l) => self.local(*l),
            Place::Field(b, i) => {
                self.place(b);
                let _ = write!(self.out, ".{i}");
            }
            Place::Index(b, i, _, bounds) => {
                self.place(b);
                self.index(i, *bounds);
            }
        }
    }

    fn args(&mut self, args: &[Arg]) {
        self.out.push('(');
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.mode(a.mode);
            self.expr(&a.expr);
        }
        self.out.push(')');
    }

    fn exprs(&mut self, es: &[Expr]) {
        for (i, e) in es.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.expr(e);
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Lit(l) => match l {
                Lit::Int(v) => {
                    let _ = write!(self.out, "{v}:");
                    self.ty(e.ty);
                }
                Lit::F32(v) => {
                    let _ = write!(self.out, "{v:?}:F32");
                }
                Lit::F64(v) => {
                    let _ = write!(self.out, "{v:?}:F64");
                }
                Lit::Bool(b) => {
                    let _ = write!(self.out, "{b}");
                }
                Lit::Char(c) => {
                    let _ = write!(self.out, "{c:?}");
                }
                Lit::Unit => self.out.push_str("()"),
            },
            ExprKind::Local(l) => self.local(*l),
            ExprKind::Const(c) => match self.m.consts.get(c.0 as usize) {
                Some(def) => {
                    let _ = write!(self.out, "const {}", def.name);
                }
                None => {
                    let _ = write!(self.out, "<bad const {}>", c.0);
                }
            },
            ExprKind::Zeroed => {
                self.out.push_str("zeroed:");
                self.ty(e.ty);
            }
            ExprKind::Unary(op, x) => {
                self.out.push('(');
                self.out.push_str(match op {
                    UnOp::Neg => "-",
                    UnOp::Not => "!",
                });
                self.expr(x);
                self.out.push(')');
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                self.out.push('(');
                self.expr(lhs);
                let sym = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Rem => "%",
                    BinOp::BitAnd => "&",
                    BinOp::BitOr => "|",
                    BinOp::BitXor => "^",
                    BinOp::Shl => "<<",
                    BinOp::Shr => ">>",
                };
                let suffix = match overflow {
                    Overflow::Checked => "",
                    Overflow::Wrap => "%",
                    Overflow::Sat => "|",
                };
                let _ = write!(self.out, " {sym}{suffix} ");
                self.expr(rhs);
                self.out.push(')');
            }
            ExprKind::Cmp { op, lhs, rhs } => {
                self.out.push('(');
                self.expr(lhs);
                let sym = match op {
                    CmpOp::Eq => "==",
                    CmpOp::Ne => "!=",
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                    CmpOp::Gt => ">",
                    CmpOp::Ge => ">=",
                };
                let _ = write!(self.out, " {sym} ");
                self.expr(rhs);
                self.out.push(')');
            }
            ExprKind::Logic { op, lhs, rhs } => {
                self.out.push('(');
                self.expr(lhs);
                self.out.push_str(match op {
                    LogicOp::And => " && ",
                    LogicOp::Or => " || ",
                });
                self.expr(rhs);
                self.out.push(')');
            }
            ExprKind::Cast(x) => {
                self.out.push('(');
                self.expr(x);
                self.out.push_str(" as ");
                self.ty(e.ty);
                self.out.push(')');
            }
            ExprKind::Call { fn_, args } => {
                match self.m.fns.get(fn_.0 as usize) {
                    Some(def) => self.out.push_str(&def.name),
                    None => {
                        let _ = write!(self.out, "<bad fn {}>", fn_.0);
                    }
                }
                self.args(args);
            }
            ExprKind::Prim { prim, args } => {
                self.out.push_str(&prim.name());
                self.args(args);
            }
            ExprKind::Field { base, index } => {
                self.expr(base);
                let _ = write!(self.out, ".{index}");
            }
            ExprKind::Index { base, index, bounds } => {
                self.expr(base);
                self.index(index, *bounds);
            }
            ExprKind::SpanOf(x) => {
                self.out.push_str("span(");
                self.expr(x);
                self.out.push(')');
            }
            ExprKind::Struct { ty, fields } => {
                let names: Vec<String> = match self.type_def_of(*ty).map(|d| &d.kind) {
                    Some(TypeDefKind::Struct { fields }) => fields.iter().map(|(n, _)| n.clone()).collect(),
                    _ => Vec::new(),
                };
                let _ = write!(self.out, "{} {{", self.type_ref_name(*ty));
                for (i, (k, f)) in fields.iter().enumerate() {
                    self.out.push_str(if i > 0 { ", " } else { " " });
                    match names.get(*k as usize) {
                        Some(n) => _ = write!(self.out, "{n}: "),
                        None => _ = write!(self.out, "{k}: "),
                    }
                    self.expr(f);
                }
                self.out.push_str(if fields.is_empty() { "}" } else { " }" });
            }
            ExprKind::Variant { ty, tag, fields } => {
                let vname = Self::variant_name(self.type_def_of(*ty), *tag);
                let _ = write!(self.out, "{}.{vname}", self.type_ref_name(*ty));
                if !fields.is_empty() {
                    self.out.push('(');
                    self.exprs(fields);
                    self.out.push(')');
                }
            }
            ExprKind::Array(es) => {
                self.out.push('[');
                self.exprs(es);
                self.out.push(']');
            }
            ExprKind::Repeat { elem, n } => {
                self.out.push('[');
                self.expr(elem);
                let _ = write!(self.out, "; {n}]");
            }
            ExprKind::Tuple(es) => {
                self.out.push('(');
                self.exprs(es);
                self.out.push(')');
            }
            ExprKind::Tag(x) => {
                self.out.push_str("tag(");
                self.expr(x);
                self.out.push(')');
            }
            ExprKind::Payload { base, tag, index } => {
                let vname = match self.m.tys.kinds().get(base.ty.index()) {
                    Some(TyKind::Enum(id)) => Self::variant_name(self.type_def_of(*id), *tag),
                    _ => tag.to_string(),
                };
                self.out.push_str("payload(");
                self.expr(base);
                let _ = write!(self.out, ", {vname}, {index})");
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                self.out.push_str("if ");
                self.expr(cond);
                self.out.push(' ');
                self.block(then);
                self.out.push_str(" else ");
                self.block(else_);
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let names: Vec<String> = match self.m.tys.kinds().get(scrutinee.ty.index()) {
                    Some(TyKind::Enum(id)) => match self.type_def_of(*id).map(|d| &d.kind) {
                        Some(TypeDefKind::Enum { variants }) => variants.iter().map(|(n, _)| n.clone()).collect(),
                        _ => Vec::new(),
                    },
                    _ => Vec::new(),
                };
                self.out.push_str("switch ");
                self.expr(scrutinee);
                self.out.push_str(" {");
                self.indent += 1;
                for (tag, b) in arms {
                    self.nl();
                    match names.get(*tag as usize) {
                        Some(n) => self.out.push_str(n),
                        None => {
                            let _ = write!(self.out, "{tag}");
                        }
                    }
                    self.out.push_str(" => ");
                    self.block(b);
                }
                if let Some(b) = default {
                    self.nl();
                    self.out.push_str("_ => ");
                    self.block(b);
                }
                self.indent -= 1;
                self.nl();
                self.out.push('}');
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Panic { msg: id, shown, .. } => {
                match self.m.messages.get(id.0 as usize) {
                    Some(text) => {
                        let _ = write!(self.out, "panic({text:?}");
                    }
                    None => {
                        let _ = write!(self.out, "panic(<bad message {}>", id.0);
                    }
                }
                // The values a failed `assert` shows: `panic("assert a == 1"; a, 1:I32)`.
                if !shown.is_empty() {
                    self.out.push_str("; ");
                    self.exprs(shown);
                }
                self.out.push(')');
            }
        }
    }
}
