//! The checks of the verifier where a node is, form by form (V-01, V-03,
//! V-05 to V-08): the type of a child is the `ty` of the child, which the walk
//! (`scope.rs`) has checked.

use onsa_sema::widens;

use super::{R, Rule, V};
use crate::ir::*;
use crate::prim::scalar;
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

    /// A block in value position must produce `ty` or diverge.
    fn value_block(&self, b: &Block, ty: CTy, what: &str) -> R<()> {
        if b.diverges() {
            return Ok(());
        }
        match &b.value {
            Some(v) => self.same(v.ty, ty, what),
            None => self.same(Types::UNIT, ty, what),
        }
    }

    pub(super) fn stmt_here(&self, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                let lt = self.local_ty(*l)?;
                self.same(e.ty, lt, "let")
            }
            StmtKind::Assign(p, e) => {
                let pt = self.place_ty(p)?;
                self.same(e.ty, pt, "assignment")
            }
            StmtKind::Expr(_) => Ok(()),
            StmtKind::If(c, ..) => self.same(c.ty, Types::BOOL, "if condition"),
            StmtKind::While(c, _) => self.same(c.ty, Types::BOOL, "while condition"),
            StmtKind::ForRange(l, lo, hi, _) => {
                let lt = lo.ty;
                if !self.tys_of(lt)?.is_int(lt) {
                    return Err(self.err(Rule::V01, "for range bounds must be integers"));
                }
                self.same(lt, hi.ty, "for range bounds")?;
                let vt = self.local_ty(*l)?;
                self.same(lt, vt, "for variable")
            }
            StmtKind::Break | StmtKind::Continue => {
                if !self.in_loop {
                    return Err(self.err(Rule::V07, "break / continue outside a loop"));
                }
                Ok(())
            }
            StmtKind::Return(e) => {
                let ret = self.f.map_or(Types::UNIT, |f| f.ret);
                match e {
                    Some(e) => self.same(e.ty, ret, "return"),
                    None => self.same(Types::UNIT, ret, "return without a value"),
                }
            }
        }
    }

    /// A place has no `ty`: its type is of its form.
    fn place_ty(&self, p: &Place) -> R<CTy> {
        match p {
            Place::Local(l) => self.local_ty(*l),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                self.field_ty(bt, *i)
            }
            Place::Index(b, ..) => {
                let bt = self.place_ty(b)?;
                self.elem_ty(bt)
            }
        }
    }

    pub(super) fn place_here(&self, p: &Place) -> R<()> {
        match p {
            // The root of a place written: seen (an assignment defines no local) and writable.
            Place::Local(l) => {
                self.read_local(*l, "written")?;
                self.writable(*l)
            }
            Place::Field(..) => Ok(()),
            Place::Index(_, i, _, bounds) => {
                self.bounds(*bounds)?;
                self.same(i.ty, Types::U32, "index")
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

    fn args(&self, args: &[Arg], params: &[(Mode, CTy)]) -> R<()> {
        if args.len() != params.len() {
            return Err(self.err(Rule::V01, format!("call with {} argument(s), expected {}", args.len(), params.len())));
        }
        for (a, (m, pt)) in args.iter().zip(params) {
            if a.mode != *m {
                return Err(self.err(Rule::V01, "argument mode does not match the parameter"));
            }
            self.same(a.expr.ty, *pt, "argument")?;
            if a.mode == Mode::Inout && !written_places(&a.expr, &mut |_| {}) {
                return Err(self.err(Rule::V05, "inout argument is not a place"));
            }
        }
        Ok(())
    }

    pub(super) fn expr_here(&self, e: &Expr) -> R<()> {
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
                let t = self.read_local(*l, "read")?;
                self.same(t, ty, "local")?;
            }
            ExprKind::Const(c) => {
                let ct = self.const_(*c)?.ty;
                self.same(ct, ty, "const")?;
            }
            ExprKind::Zeroed => {}
            ExprKind::Unary(op, x) => {
                self.same(x.ty, ty, "unary operand")?;
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
                let (lt, rt) = (lhs.ty, rhs.ty);
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
                let lt = lhs.ty;
                self.same(lt, rhs.ty, "comparison operands")?;
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
                self.same(lhs.ty, Types::BOOL, "logic lhs")?;
                self.same(rhs.ty, Types::BOOL, "logic rhs")?;
                self.same(ty, Types::BOOL, "logic result")?;
            }
            // The widenings of §3.3, as sema judges them.
            ExprKind::Cast(x) => {
                if !widens(scalar(self.kind(x.ty)?), scalar(tys.kind(ty))) {
                    let name = |t| crate::dump::type_name(self.m, t);
                    return Err(self.err(Rule::V03, format!("`{}` as `{}` is no widening", name(x.ty), name(ty))));
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
                    if a.mode == Mode::Inout && !written_places(&a.expr, &mut |_| {}) {
                        return Err(self.err(Rule::V05, "inout primitive argument is not a place"));
                    }
                }
                if self.f.is_some_and(|f| f.rt) && !prim.rt() {
                    return Err(
                        self.err(Rule::V06, format!("rt function calls the non-rt primitive `{}`", prim.name()))
                    );
                }
                self.prim_sig(prim, args, ty)?;
            }
            ExprKind::Field { base, index } => {
                let ft = self.field_ty(base.ty, *index)?;
                self.same(ft, ty, "field")?;
            }
            ExprKind::Index { base, index, bounds } => {
                self.bounds(*bounds)?;
                self.same(index.ty, Types::U32, "index")?;
                let et = self.elem_ty(base.ty)?;
                self.same(et, ty, "element")?;
            }
            ExprKind::SpanOf(x) => {
                if x.as_place().is_none() {
                    return Err(self.err(Rule::V01, "span of a non-place"));
                }
                let et = match self.kind(x.ty)? {
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
                // Each field once, in any order (the order of evaluation).
                let mut seen = vec![false; defs.len()];
                for (k, f) in fields {
                    let Some((_, dt)) = defs.get(*k as usize) else {
                        return Err(self.err(Rule::V20, format!("struct literal field {k} out of range")));
                    };
                    if std::mem::replace(&mut seen[*k as usize], true) {
                        return Err(self.err(Rule::V01, format!("struct literal field {k} given twice")));
                    }
                    self.same(f.ty, *dt, "struct field")?;
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
                    self.same(f.ty, *dt, "variant field")?;
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
                    self.same(x.ty, *et, "array element")?;
                }
            }
            ExprKind::Repeat { elem, n } => {
                let TyKind::Array(et, m) = tys.kind(ty) else {
                    return Err(self.err(Rule::V01, "repeat of a non-array type"));
                };
                if m != n {
                    return Err(self.err(Rule::V01, "repeat length"));
                }
                self.same(elem.ty, *et, "repeat element")?;
            }
            ExprKind::Tuple(es) => {
                let TyKind::Tuple(ts) = tys.kind(ty) else {
                    if es.is_empty() && ty == Types::UNIT {
                        return Ok(());
                    }
                    return Err(self.err(Rule::V01, "tuple literal of a non-tuple type"));
                };
                if ts.len() != es.len() {
                    return Err(self.err(Rule::V01, "tuple literal length"));
                }
                for (x, t) in es.iter().zip(ts) {
                    self.same(x.ty, *t, "tuple element")?;
                }
            }
            ExprKind::Tag(x) => {
                let TyKind::Enum(id) = *self.kind(x.ty)? else { return Err(self.err(Rule::V01, "tag of a non-enum")) };
                let n = self.variants(id)?.len();
                self.same(Types::int(onsa_sema::layout::tag_kind(n)), ty, "tag")?;
            }
            ExprKind::Payload { base, tag, index } => {
                let TyKind::Enum(id) = *self.kind(base.ty)? else {
                    return Err(self.err(Rule::V01, "payload of a non-enum"));
                };
                let variants = self.variants(id)?;
                let (_, defs) =
                    variants.get(*tag as usize).ok_or_else(|| self.err(Rule::V20, "payload tag out of range"))?;
                let ft = defs.get(*index as usize).ok_or_else(|| self.err(Rule::V20, "payload index out of range"))?;
                self.same(*ft, ty, "payload")?;
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                self.same(cond.ty, Types::BOOL, "if condition")?;
                self.value_block(then, ty, "if branch")?;
                self.value_block(else_, ty, "else branch")?;
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let TyKind::Enum(id) = *self.kind(scrutinee.ty)? else {
                    return Err(self.err(Rule::V01, "switch on a non-enum"));
                };
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
            ExprKind::Panic { msg: id, .. } => {
                if id.0 as usize >= self.m.messages.len() {
                    return Err(self.err(Rule::V20, "panic message out of range"));
                }
            }
        }
        Ok(())
    }
}
