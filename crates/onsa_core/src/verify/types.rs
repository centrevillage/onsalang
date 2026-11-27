//! The type checks of the verifier, form by form (V-01, V-08).

use super::{R, Rule, V};
use crate::ir::*;
use crate::prim::Prim;
use crate::walk::written_places;

impl<'a> V<'a> {
    pub(super) fn same(&self, a: CTy, b: CTy, what: &str) -> R<()> {
        if a == b {
            Ok(())
        } else {
            Err(self.err(
                Rule::V01,
                format!(
                    "{what}: type mismatch `{}` vs `{}`",
                    crate::dump::type_name(self.m, a),
                    crate::dump::type_name(self.m, b)
                ),
            ))
        }
    }

    /// That `t` is the type `want` (the type of a literal of a struct, an
    /// enum or a span), which the verifier compares by kind, adding no type.
    fn is(&self, want: &TyKind, t: CTy, what: &str) -> R<()> {
        if self.kind(t)? == want {
            Ok(())
        } else {
            Err(self.err(
                Rule::V01,
                format!(
                    "{what}: type mismatch `{}` vs `{}`",
                    crate::dump::kind_name(self.m, want),
                    crate::dump::type_name(self.m, t)
                ),
            ))
        }
    }

    /// Type of a block's value: `None` for no value.
    pub(super) fn block(&mut self, b: &Block) -> R<Option<CTy>> {
        for s in &b.stmts {
            self.stmt(s)?;
        }
        match &b.value {
            Some(v) => Ok(Some(self.expr(v)?)),
            None => Ok(None),
        }
    }

    /// A block in value position must produce `ty` or diverge.
    fn value_block(&mut self, b: &Block, ty: CTy, what: &str) -> R<()> {
        let t = self.block(b)?;
        if b.diverges() {
            return Ok(());
        }
        match t {
            Some(t) => self.same(t, ty, what),
            None => self.same(Types::UNIT, ty, what),
        }
    }

    /// A statement or an expression is the position of the errors in it
    /// but in its parts.
    fn stmt(&mut self, s: &Stmt) -> R<()> {
        let outer = self.at.replace(s.span);
        self.stmt_here(s)?;
        self.at = outer;
        Ok(())
    }

    fn stmt_here(&mut self, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                let t = self.expr(e)?;
                let lt = self.local_ty(*l)?;
                self.same(t, lt, "let")?;
                self.define(*l)?;
                self.lets[l.0 as usize] = true;
                Ok(())
            }
            StmtKind::Assign(p, e) => {
                let pt = self.place(p)?;
                let t = self.expr(e)?;
                self.same(t, pt, "assignment")
            }
            StmtKind::Expr(e) => self.expr(e).map(|_| ()),
            StmtKind::If(c, t, e) => {
                let ct = self.expr(c)?;
                self.same(ct, Types::BOOL, "if condition")?;
                self.block(t)?;
                self.block(e)?;
                Ok(())
            }
            StmtKind::While(c, b) => {
                let ct = self.expr(c)?;
                self.same(ct, Types::BOOL, "while condition")?;
                self.loops += 1;
                let r = self.block(b);
                self.loops -= 1;
                r.map(|_| ())
            }
            StmtKind::ForRange(l, lo, hi, b) => {
                let lt = self.expr(lo)?;
                let ht = self.expr(hi)?;
                if !self.tys_of(lt)?.is_int(lt) {
                    return Err(self.err(Rule::V01, "for range bounds must be integers"));
                }
                self.same(lt, ht, "for range bounds")?;
                let vt = self.local_ty(*l)?;
                self.same(lt, vt, "for variable")?;
                self.define(*l)?;
                self.loops += 1;
                let here = self.known || self.process;
                let outer = std::mem::replace(&mut self.known, here);
                let r = self.block(b);
                self.known = outer;
                self.loops -= 1;
                r.map(|_| ())
            }
            StmtKind::Break | StmtKind::Continue => {
                if self.loops == 0 {
                    return Err(self.err(Rule::V07, "break / continue outside a loop"));
                }
                Ok(())
            }
            StmtKind::Return(e) => {
                let ret = self.f.map_or(Types::UNIT, |f| f.ret);
                match e {
                    Some(e) => {
                        let t = self.expr(e)?;
                        self.same(t, ret, "return")
                    }
                    None => self.same(Types::UNIT, ret, "return without a value"),
                }
            }
        }
    }

    fn place(&mut self, p: &Place) -> R<CTy> {
        match p {
            Place::Local(l) => {
                // Assignment defines a `var` whose initializer was lowered to an assignment.
                let t = self.local_ty(*l)?;
                self.defined[l.0 as usize] = true;
                Ok(t)
            }
            Place::Field(b, i) => {
                let bt = self.place(b)?;
                self.field_ty(bt, *i)
            }
            Place::Index(b, i, _, bounds) => {
                self.bounds(*bounds)?;
                let bt = self.place(b)?;
                let it = self.expr(i)?;
                self.same(it, Types::U32, "index")?;
                self.elem_ty(bt)
            }
        }
    }

    fn field_ty(&self, base: CTy, i: u32) -> R<CTy> {
        match self.kind(base)? {
            TyKind::Struct(id) => match &self.ty(*id)?.kind {
                TypeDefKind::Struct { fields } => fields
                    .get(i as usize)
                    .map(|&(_, t)| t)
                    .ok_or_else(|| self.err(Rule::V20, "field index out of range")),
                TypeDefKind::Opaque => Err(self.err(Rule::V20, "field access on an opaque type")),
                TypeDefKind::Enum { .. } => Err(self.err(Rule::V01, "field access on an enum")),
            },
            TyKind::Tuple(ts) => {
                ts.get(i as usize).copied().ok_or_else(|| self.err(Rule::V20, "tuple index out of range"))
            }
            _ => Err(self.err(Rule::V01, format!("field access on `{}`", crate::dump::type_name(self.m, base)))),
        }
    }

    fn elem_ty(&self, base: CTy) -> R<CTy> {
        match self.kind(base)? {
            TyKind::Array(e, _) | TyKind::Span(e) | TyKind::Buf(e) => Ok(*e),
            _ => Err(self.err(Rule::V01, format!("index on `{}`", crate::dump::type_name(self.m, base)))),
        }
    }

    fn args(&mut self, args: &[Arg], params: &[(Mode, CTy)]) -> R<()> {
        if args.len() != params.len() {
            return Err(self.err(Rule::V01, format!("call with {} argument(s), expected {}", args.len(), params.len())));
        }
        for (a, (m, pt)) in args.iter().zip(params) {
            if a.mode != *m {
                return Err(self.err(Rule::V01, "argument mode does not match the parameter"));
            }
            let at = self.expr(&a.expr)?;
            self.same(at, *pt, "argument")?;
            if a.mode == Mode::Inout && !written_places(&a.expr, &mut |_| {}) {
                return Err(self.err(Rule::V05, "inout argument is not a place"));
            }
        }
        Ok(())
    }

    pub(super) fn expr(&mut self, e: &Expr) -> R<CTy> {
        let outer = self.at.replace(e.span);
        let ty = self.expr_here(e)?;
        self.at = outer;
        Ok(ty)
    }

    fn expr_here(&mut self, e: &Expr) -> R<CTy> {
        let (ty, tys) = (e.ty, self.tys_of(e.ty)?);
        match &e.kind {
            ExprKind::Lit(l) => {
                let ok = match l {
                    Lit::Int(_) => tys.is_int(ty),
                    Lit::F32(_) => ty == Types::float(FloatKind::F32),
                    Lit::F64(_) => ty == Types::float(FloatKind::F64),
                    Lit::Bool(_) => ty == Types::BOOL,
                    Lit::Char(_) => ty == Types::CHAR,
                    Lit::Unit => ty == Types::UNIT,
                };
                if !ok {
                    return Err(self.err(Rule::V01, "literal type mismatch"));
                }
                if let (Lit::Int(v), TyKind::Int(k)) = (l, tys.kind(ty)) {
                    let (lo, hi) = k.range();
                    if *v < lo || *v > hi {
                        return Err(self.err(Rule::V01, format!("literal {v} out of range for {}", k.name())));
                    }
                }
            }
            ExprKind::Local(l) => {
                let t = self.read_local(*l)?;
                self.same(t, ty, "local")?;
            }
            ExprKind::Const(c) => {
                let ct = self.const_(*c)?.ty;
                self.same(ct, ty, "const")?;
            }
            ExprKind::Zeroed => {}
            ExprKind::Unary(op, x) => {
                let xt = self.expr(x)?;
                self.same(xt, ty, "unary operand")?;
                match op {
                    UnOp::Neg => {
                        let ok = matches!(tys.kind(ty), TyKind::Int(k) if k.signed()) || tys.is_float(ty);
                        if !ok {
                            return Err(self.err(Rule::V01, "`-` on a non-signed type"));
                        }
                    }
                    UnOp::Not => {
                        if !(ty == Types::BOOL || tys.is_int(ty)) {
                            return Err(self.err(Rule::V01, "`!` on a non-Bool, non-integer type"));
                        }
                    }
                }
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                let lt = self.expr(lhs)?;
                let rt = self.expr(rhs)?;
                self.same(lt, ty, "binary lhs")?;
                if matches!(op, BinOp::Shl | BinOp::Shr) {
                    self.same(rt, Types::U32, "shift amount")?;
                } else {
                    self.same(rt, ty, "binary rhs")?;
                }
                let bitwise = matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr);
                if bitwise && !tys.is_int(ty) {
                    return Err(self.err(Rule::V01, "bitwise operator on a non-integer"));
                }
                if !tys.is_int(ty) && !tys.is_float(ty) {
                    return Err(self.err(Rule::V01, "arithmetic on a non-numeric type"));
                }
                if tys.is_float(ty) && *overflow != Overflow::Checked {
                    return Err(self.err(Rule::V01, "overflow mode on a float operation"));
                }
            }
            ExprKind::Cmp { op, lhs, rhs } => {
                let lt = self.expr(lhs)?;
                let rt = self.expr(rhs)?;
                self.same(lt, rt, "comparison operands")?;
                // `()` is compared by the lowering (`lower::eq::compare`).
                if !self.tys_of(lt)?.is_scalar(lt) {
                    return Err(self.err(Rule::V01, "comparison of non-scalar values (use a generated eq function)"));
                }
                if lt == Types::BOOL && !matches!(op, CmpOp::Eq | CmpOp::Ne) {
                    return Err(self.err(Rule::V01, "ordering on Bool"));
                }
                self.same(ty, Types::BOOL, "comparison result")?;
            }
            ExprKind::Logic { lhs, rhs, .. } => {
                let lt = self.expr(lhs)?;
                let rt = self.expr(rhs)?;
                self.same(lt, Types::BOOL, "logic lhs")?;
                self.same(rt, Types::BOOL, "logic rhs")?;
                self.same(ty, Types::BOOL, "logic result")?;
            }
            ExprKind::Cast(x) => {
                let xt = self.expr(x)?;
                let xs = self.tys_of(xt)?;
                if !(xs.is_int(xt) || xs.is_float(xt)) || !(tys.is_int(ty) || tys.is_float(ty)) {
                    return Err(self.err(Rule::V03, "cast between non-numeric types"));
                }
            }
            ExprKind::Call { fn_, args } => {
                let callee = self.callee(*fn_)?;
                if self.f.is_some_and(|f| f.rt) && !callee.rt {
                    return Err(self.err(Rule::V06, format!("rt function calls non-rt `{}`", callee.name)));
                }
                let params: Vec<(Mode, CTy)> = callee.params.iter().map(|p| (p.mode, p.ty)).collect();
                self.args(args, &params)?;
                self.same(callee.ret, ty, "call result")?;
            }
            ExprKind::Prim { prim, args } => {
                for a in args {
                    self.expr(&a.expr)?;
                    if a.mode == Mode::Inout && !written_places(&a.expr, &mut |_| {}) {
                        return Err(self.err(Rule::V05, "inout primitive argument is not a place"));
                    }
                }
                if self.f.is_some_and(|f| f.rt) && matches!(prim, Prim::BufZeroed) {
                    return Err(self.err(Rule::V06, "rt function allocates (Buf.zeroed)"));
                }
            }
            ExprKind::Field { base, index } => {
                let bt = self.expr(base)?;
                let ft = self.field_ty(bt, *index)?;
                self.same(ft, ty, "field")?;
            }
            ExprKind::Index { base, index, bounds } => {
                self.bounds(*bounds)?;
                let bt = self.expr(base)?;
                let it = self.expr(index)?;
                self.same(it, Types::U32, "index")?;
                let et = self.elem_ty(bt)?;
                self.same(et, ty, "element")?;
            }
            ExprKind::SpanOf(x) => {
                let xt = self.expr(x)?;
                if x.as_place().is_none() {
                    return Err(self.err(Rule::V01, "span of a non-place"));
                }
                let et = match self.kind(xt)? {
                    TyKind::Array(e, _) | TyKind::Buf(e) => *e,
                    _ => return Err(self.err(Rule::V01, "span of a non-array / non-Buf")),
                };
                self.is(&TyKind::Span(et), ty, "span")?;
            }
            ExprKind::Struct { ty: id, fields } => {
                let defs = match &self.ty(*id)?.kind {
                    TypeDefKind::Struct { fields } => fields,
                    TypeDefKind::Opaque => return Err(self.err(Rule::V20, "struct literal of an opaque type")),
                    TypeDefKind::Enum { .. } => return Err(self.err(Rule::V01, "struct literal of a non-struct")),
                };
                if defs.len() != fields.len() {
                    return Err(self.err(Rule::V01, "struct literal field count"));
                }
                for (f, (_, dt)) in fields.iter().zip(defs) {
                    let ft = self.expr(f)?;
                    self.same(ft, *dt, "struct field")?;
                }
                self.is(&TyKind::Struct(*id), ty, "struct literal")?;
            }
            ExprKind::Variant { ty: id, tag, fields } => {
                let TypeDefKind::Enum { variants } = &self.ty(*id)?.kind else {
                    return Err(self.err(Rule::V01, "variant of a non-enum"));
                };
                let (_, defs) =
                    variants.get(*tag as usize).ok_or_else(|| self.err(Rule::V20, "variant tag out of range"))?;
                if defs.len() != fields.len() {
                    return Err(self.err(Rule::V01, "variant field count"));
                }
                for (f, dt) in fields.iter().zip(defs) {
                    let ft = self.expr(f)?;
                    self.same(ft, *dt, "variant field")?;
                }
                self.is(&TyKind::Enum(*id), ty, "variant")?;
            }
            ExprKind::Array(es) => {
                let TyKind::Array(et, n) = tys.kind(ty) else {
                    return Err(self.err(Rule::V01, "array literal of a non-array type"));
                };
                if *n as usize != es.len() {
                    return Err(self.err(Rule::V01, "array literal length"));
                }
                for x in es {
                    let xt = self.expr(x)?;
                    self.same(xt, *et, "array element")?;
                }
            }
            ExprKind::Repeat { elem, n } => {
                let TyKind::Array(et, m) = tys.kind(ty) else {
                    return Err(self.err(Rule::V01, "repeat of a non-array type"));
                };
                if m != n {
                    return Err(self.err(Rule::V01, "repeat length"));
                }
                let xt = self.expr(elem)?;
                self.same(xt, *et, "repeat element")?;
            }
            ExprKind::Tuple(es) => {
                let TyKind::Tuple(ts) = tys.kind(ty) else {
                    if es.is_empty() && ty == Types::UNIT {
                        return Ok(ty);
                    }
                    return Err(self.err(Rule::V01, "tuple literal of a non-tuple type"));
                };
                if ts.len() != es.len() {
                    return Err(self.err(Rule::V01, "tuple literal length"));
                }
                for (x, t) in es.iter().zip(ts) {
                    let xt = self.expr(x)?;
                    self.same(xt, *t, "tuple element")?;
                }
            }
            ExprKind::Tag(x) => {
                let xt = self.expr(x)?;
                let TyKind::Enum(id) = *self.kind(xt)? else { return Err(self.err(Rule::V01, "tag of a non-enum")) };
                let n = self.variants(id)?.len();
                self.same(Types::int(onsa_sema::layout::tag_kind(n)), ty, "tag")?;
            }
            ExprKind::Payload { base, tag, index } => {
                let bt = self.expr(base)?;
                let TyKind::Enum(id) = *self.kind(bt)? else {
                    return Err(self.err(Rule::V01, "payload of a non-enum"));
                };
                let variants = self.variants(id)?;
                let (_, defs) =
                    variants.get(*tag as usize).ok_or_else(|| self.err(Rule::V20, "payload tag out of range"))?;
                let ft = defs.get(*index as usize).ok_or_else(|| self.err(Rule::V20, "payload index out of range"))?;
                self.same(*ft, ty, "payload")?;
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                let ct = self.expr(cond)?;
                self.same(ct, Types::BOOL, "if condition")?;
                self.value_block(then, ty, "if branch")?;
                self.value_block(else_, ty, "else branch")?;
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let st = self.expr(scrutinee)?;
                let TyKind::Enum(id) = *self.kind(st)? else { return Err(self.err(Rule::V01, "switch on a non-enum")) };
                let n = self.variants(id)?.len();
                let mut seen = vec![false; n];
                for (tag, b) in arms {
                    if *tag as usize >= n || seen[*tag as usize] {
                        return Err(self.err(Rule::V08, "switch arm tag out of range or duplicated"));
                    }
                    seen[*tag as usize] = true;
                    self.value_block(b, ty, "switch arm")?;
                }
                match default {
                    Some(b) => self.value_block(b, ty, "switch default")?,
                    None => {
                        if seen.iter().any(|s| !s) {
                            return Err(self.err(Rule::V08, "switch does not cover every variant"));
                        }
                    }
                }
            }
            ExprKind::Block(b) => self.value_block(b, ty, "block")?,
            ExprKind::Panic { msg: id, shown, .. } => {
                if id.0 as usize >= self.m.messages.len() {
                    return Err(self.err(Rule::V20, "panic message out of range"));
                }
                for x in shown {
                    self.expr(x)?;
                }
            }
        }
        Ok(ty)
    }
}
