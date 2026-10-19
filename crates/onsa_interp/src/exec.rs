//! The walk of the tree: statements and expressions.

use onsa_core::{
    Arg, BinOp, Block, CmpOp, Expr, ExprKind, FnId, IntKind, Lit, LocalId, LogicOp, Mode, MsgId, Overflow, PanicOrigin,
    Place, Stmt, StmtKind, Ty, UnOp,
};
use onsa_diag::Span;

use crate::numeric::{bool_of, int_kind_of, int_of};
use crate::place::{ArgVal, Frame, Leaf, Loc};
use crate::value::{ArrayData, SpanRef, Value, int_value, slot, zero};
use crate::{Interp, R, Signal, internal, panic, panic_from};

impl<'m> Interp<'m> {
    // ------------------------------------------------------------ statements

    /// Run a block; its value, or `()`.
    pub(super) fn exec_block(&self, f: &mut Frame, b: &Block) -> R<Value> {
        for s in &b.stmts {
            self.exec(f, s)?;
        }
        match &b.value {
            Some(e) => self.eval(f, e),
            None => Ok(Value::Unit),
        }
    }

    /// A statement. Each kind with locals of its own is a function (R-05).
    fn exec(&self, f: &mut Frame, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => self.exec_let(f, *l, e),
            StmtKind::Assign(p, e) => self.exec_assign(f, p, e, s.span),
            StmtKind::Expr(e) => self.exec_expr(f, e),
            StmtKind::If(c, t, e) => self.exec_if(f, c, t, e),
            StmtKind::While(c, body) => self.exec_while(f, c, body),
            StmtKind::ForRange(l, lo, hi, body) => self.exec_for(f, *l, lo, hi, body, s.span),
            StmtKind::Break => Err(Signal::Break),
            StmtKind::Continue => Err(Signal::Continue),
            StmtKind::Return(e) => self.exec_return(f, e.as_ref()),
        }
    }

    #[inline(never)]
    fn exec_let(&self, f: &mut Frame, l: LocalId, e: &Expr) -> R<()> {
        let v = self.eval(f, e)?;
        f.locals[l.0 as usize] = Some(Loc::Slot(slot(v)));
        Ok(())
    }

    #[inline(never)]
    fn exec_expr(&self, f: &mut Frame, e: &Expr) -> R<()> {
        self.eval(f, e)?;
        Ok(())
    }

    #[inline(never)]
    fn exec_if(&self, f: &mut Frame, c: &Expr, t: &Block, e: &Block) -> R<()> {
        let c = self.eval_bool(f, c)?;
        self.exec_block(f, if c { t } else { e })?;
        Ok(())
    }

    #[inline(never)]
    fn exec_return(&self, f: &mut Frame, e: Option<&Expr>) -> R<()> {
        let v = match e {
            Some(e) => self.eval(f, e)?,
            None => Value::Unit,
        };
        Err(Signal::Return(v))
    }

    #[inline(never)]
    fn exec_assign(&self, f: &mut Frame, p: &Place, e: &Expr, span: Span) -> R<()> {
        let v = self.eval(f, e)?;
        let r = self.resolve_place(f, p, span)?;
        self.write(&r, v, span)
    }

    #[inline(never)]
    fn exec_while(&self, f: &mut Frame, c: &Expr, body: &Block) -> R<()> {
        while self.eval_bool(f, c)? {
            match self.exec_block(f, body) {
                Ok(_) | Err(Signal::Continue) => {}
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    #[inline(never)]
    fn exec_for(&self, f: &mut Frame, l: LocalId, lo: &Expr, hi: &Expr, body: &Block, span: Span) -> R<()> {
        let lo_v = self.eval(f, lo)?;
        let hi_v = self.eval(f, hi)?;
        let kind = int_kind_of(&lo_v, span);
        let (lo_i, hi_i) = (int_of(&lo_v, kind, span), int_of(&hi_v, kind, span));
        let var = slot(lo_v);
        f.locals[l.0 as usize] = Some(Loc::Slot(var.clone()));
        let mut i = lo_i;
        while i < hi_i {
            *var.borrow_mut() = int_value(kind, i);
            match self.exec_block(f, body) {
                Ok(_) | Err(Signal::Continue) => {}
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
            i += 1;
        }
        Ok(())
    }

    // ------------------------------------------------------------ expressions

    fn eval_bool(&self, f: &mut Frame, e: &Expr) -> R<bool> {
        let v = self.eval(f, e)?;
        Ok(bool_of(&v, e.span))
    }

    /// An index, a length, a bound of a slice: a `U32` and nothing else (R-92).
    #[inline(never)]
    pub(super) fn eval_u32(&self, f: &mut Frame, e: &Expr) -> R<u32> {
        let v = self.eval(f, e)?;
        Ok(int_of(&v, IntKind::U32, e.span) as u32)
    }

    fn eval_args(&self, f: &mut Frame, args: &[Arg]) -> R<Vec<ArgVal>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            if a.mode == Mode::Inout
                && let Some(p) = a.expr.as_place()
            {
                out.push(ArgVal::Place(self.resolve_place(f, &p, a.expr.span)?));
            } else {
                out.push(ArgVal::Val(self.eval(f, &a.expr)?));
            }
        }
        Ok(out)
    }

    /// The values of `xs`, in order.
    fn eval_all(&self, f: &mut Frame, xs: &[Expr]) -> R<Vec<Value>> {
        let mut out = Vec::with_capacity(xs.len());
        for x in xs {
            out.push(self.eval(f, x)?);
        }
        Ok(out)
    }

    /// An expression. The dispatch only: every kind with locals of its own is
    /// a function, so that this frame, which is on the way down every
    /// recursion, stays small (R-05).
    pub(super) fn eval(&self, f: &mut Frame, e: &Expr) -> R<Value> {
        let span = e.span;
        match &e.kind {
            ExprKind::Lit(l) => self.eval_lit(l, e),
            ExprKind::Local(l) => self.eval_local(f, *l, span),
            ExprKind::Const(c) => self.const_val(*c),
            ExprKind::Zeroed => self.eval_zeroed(&e.ty),
            ExprKind::Unary(op, x) => self.eval_unary(f, *op, x, e),
            ExprKind::Binary { op, overflow, lhs, rhs } => self.eval_binary(f, (*op, *overflow), lhs, rhs, e),
            ExprKind::Cmp { op, lhs, rhs } => self.eval_cmp(f, *op, lhs, rhs, e),
            ExprKind::Logic { op, lhs, rhs } => self.eval_logic(f, *op, lhs, rhs),
            ExprKind::Cast(x) => self.eval_cast(f, x, e),
            ExprKind::Call { fn_, args } => self.eval_call(f, *fn_, args, e),
            ExprKind::Prim { prim, args } => self.prim(f, prim, args, &e.ty, span),
            ExprKind::Field { base, index } => self.eval_field(f, base, *index, e),
            ExprKind::Index { base, index } => self.eval_index(f, base, index, e),
            ExprKind::SpanOf(inner) => self.eval_span_of(f, inner, e),
            ExprKind::Struct { fields, .. } => self.eval_struct(f, fields),
            ExprKind::Variant { tag, fields, .. } => self.eval_variant(f, *tag, fields),
            ExprKind::Array(items) => self.eval_array(f, items, e),
            ExprKind::Repeat { elem, n } => self.eval_repeat(f, elem, *n),
            ExprKind::Tuple(items) => self.eval_tuple(f, items),
            ExprKind::Tag(x) => self.eval_tag(f, x, e),
            ExprKind::Payload { base, tag, index } => self.eval_payload(f, base, *tag, *index, e),
            ExprKind::IfExpr { cond, then, else_ } => self.eval_if(f, cond, then, else_),
            ExprKind::Switch { scrutinee, arms, default } => self.eval_switch(f, scrutinee, arms, default, e),
            ExprKind::Block(b) => self.exec_block(f, b),
            ExprKind::Panic { msg, origin } => self.eval_panic(*msg, *origin, span),
        }
    }

    #[inline(never)]
    fn eval_zeroed(&self, ty: &Ty) -> R<Value> {
        Ok(zero(self.m, ty))
    }

    #[inline(never)]
    fn eval_unary(&self, f: &mut Frame, op: UnOp, x: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let v = self.eval(f, x)?;
        self.unary(op, v, span)
    }

    #[inline(never)]
    fn eval_cast(&self, f: &mut Frame, x: &Expr, e: &Expr) -> R<Value> {
        let v = self.eval(f, x)?;
        self.cast(v, &x.ty, &e.ty, e.span)
    }

    #[inline(never)]
    fn eval_call(&self, f: &mut Frame, fn_: FnId, args: &[Arg], at: &Expr) -> R<Value> {
        let span = at.span;
        let args = self.eval_args(f, args)?;
        self.call_with(fn_, args, span)
    }

    #[inline(never)]
    fn eval_struct(&self, f: &mut Frame, fields: &[Expr]) -> R<Value> {
        Ok(Value::Struct(self.eval_all(f, fields)?))
    }

    #[inline(never)]
    fn eval_variant(&self, f: &mut Frame, tag: u32, fields: &[Expr]) -> R<Value> {
        Ok(Value::Enum { tag, fields: self.eval_all(f, fields)? })
    }

    #[inline(never)]
    fn eval_tuple(&self, f: &mut Frame, items: &[Expr]) -> R<Value> {
        Ok(Value::Tuple(self.eval_all(f, items)?))
    }

    #[inline(never)]
    fn eval_if(&self, f: &mut Frame, cond: &Expr, then: &Block, else_: &Block) -> R<Value> {
        let c = self.eval_bool(f, cond)?;
        self.exec_block(f, if c { then } else { else_ })
    }

    #[cold]
    #[inline(never)]
    fn eval_panic(&self, msg: MsgId, origin: PanicOrigin, span: Span) -> R<Value> {
        panic_from(origin, span, self.m.messages[msg.0 as usize].clone())
    }

    #[inline(never)]
    fn eval_lit(&self, l: &Lit, e: &Expr) -> R<Value> {
        Ok(match l {
            Lit::Int(n) => match &e.ty {
                Ty::Int(k) => int_value(*k, *n),
                _ => internal(e.span, "integer literal type"),
            },
            Lit::F32(x) => Value::F32(*x),
            Lit::F64(x) => Value::F64(*x),
            Lit::Bool(b) => Value::Bool(*b),
            Lit::Char(c) => Value::Char(*c),
            Lit::Unit => Value::Unit,
        })
    }

    #[inline(never)]
    fn eval_local(&self, f: &Frame, l: LocalId, span: Span) -> R<Value> {
        let r = self.local_place(f, l, span)?;
        self.read(&r, span)
    }

    #[inline(never)]
    fn eval_binary(&self, f: &mut Frame, op: (BinOp, Overflow), lhs: &Expr, rhs: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let a = self.eval(f, lhs)?;
        let b = self.eval(f, rhs)?;
        self.binary(op.0, op.1, a, b, span)
    }

    #[inline(never)]
    fn eval_cmp(&self, f: &mut Frame, op: CmpOp, lhs: &Expr, rhs: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let a = self.eval(f, lhs)?;
        let b = self.eval(f, rhs)?;
        Ok(Value::Bool(self.compare(op, &a, &b, span)?))
    }

    #[inline(never)]
    fn eval_logic(&self, f: &mut Frame, op: LogicOp, lhs: &Expr, rhs: &Expr) -> R<Value> {
        let a = self.eval_bool(f, lhs)?;
        Ok(Value::Bool(match op {
            LogicOp::And => a && self.eval_bool(f, rhs)?,
            LogicOp::Or => a || self.eval_bool(f, rhs)?,
        }))
    }

    #[inline(never)]
    fn eval_field(&self, f: &mut Frame, base: &Expr, index: u32, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_field(r, index, span)?;
            return self.read(&r, span);
        }
        match self.eval(f, base)? {
            Value::Struct(fs) | Value::Tuple(fs) | Value::Enum { fields: fs, .. } => {
                fs.into_iter().nth(index as usize).map_or_else(|| internal(span, "field out of range"), Ok)
            }
            _ => internal(span, "field on a non-aggregate"),
        }
    }

    #[inline(never)]
    fn eval_index(&self, f: &mut Frame, base: &Expr, index: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let i = self.eval_u32(f, index)?;
            let r = self.resolve_place(f, &p, span)?;
            let r = self.project_index(r, i, span)?;
            return self.read(&r, span);
        }
        let v = self.eval(f, base)?;
        let i = self.eval_u32(f, index)?;
        self.index_value(v, i, span)
    }

    /// Element `i` of the sequence `v`, off the way down a recursion (R-05).
    #[inline(never)]
    fn index_value(&self, v: Value, i: u32, span: Span) -> R<Value> {
        let s = self.seq_of_value(v, span)?;
        if i >= s.len {
            return panic(span, format!("index {i} out of range for a sequence of length {}", s.len));
        }
        self.seq_get(&s, i, span)
    }

    #[inline(never)]
    fn eval_span_of(&self, f: &mut Frame, inner: &Expr, at: &Expr) -> R<Value> {
        let span = at.span;
        let s = match inner.as_place() {
            Some(p) => {
                let r = self.resolve_place(f, &p, span)?;
                self.seq_of_place(r, span)?
            }
            None => {
                let v = self.eval(f, inner)?;
                self.seq_of_value(v, span)?
            }
        };
        Ok(Value::Span(SpanRef { root: s.root, projs: s.projs, start: s.start, len: s.len }))
    }

    #[inline(never)]
    fn eval_array(&self, f: &mut Frame, items: &[Expr], e: &Expr) -> R<Value> {
        let out = self.eval_all(f, items)?;
        let elem = match &e.ty {
            Ty::Array(el, _) => (**el).clone(),
            _ => internal(e.span, "array literal type"),
        };
        Ok(Value::Array(ArrayData::from_values(&elem, out)))
    }

    #[inline(never)]
    fn eval_repeat(&self, f: &mut Frame, elem: &Expr, n: u32) -> R<Value> {
        let v = self.eval(f, elem)?;
        Ok(Value::Array(match v {
            Value::F32(x) => ArrayData::F32(vec![x; n as usize]),
            v => ArrayData::Any(vec![v; n as usize]),
        }))
    }

    #[inline(never)]
    fn eval_tag(&self, f: &mut Frame, x: &Expr, e: &Expr) -> R<Value> {
        let span = e.span;
        let tag = match x.as_place() {
            Some(p) => {
                let r = self.resolve_place(f, &p, span)?;
                self.peek(&r, span, |v| match v {
                    Leaf::Val(Value::Enum { tag, .. }) => Some(*tag),
                    _ => None,
                })?
            }
            None => match self.eval(f, x)? {
                Value::Enum { tag, .. } => Some(tag),
                _ => None,
            },
        };
        let Some(tag) = tag else { internal(span, "tag of a non-enum") };
        match &e.ty {
            Ty::Int(k) => Ok(int_value(*k, tag as i128)),
            _ => internal(span, "tag type"),
        }
    }

    #[inline(never)]
    fn eval_payload(&self, f: &mut Frame, base: &Expr, tag: u32, index: u32, at: &Expr) -> R<Value> {
        let span = at.span;
        if let Some(p) = base.as_place() {
            let r = self.resolve_place(f, &p, span)?;
            let ok = self.peek(&r, span, |v| matches!(v, Leaf::Val(Value::Enum { tag: t, .. }) if *t == tag))?;
            if !ok {
                internal(span, "payload of the wrong variant");
            }
            let r = self.project_field(r, index, span)?;
            return self.read(&r, span);
        }
        match self.eval(f, base)? {
            Value::Enum { tag: t, fields } if t == tag => {
                fields.into_iter().nth(index as usize).map_or_else(|| internal(span, "payload field out of range"), Ok)
            }
            _ => internal(span, "payload of the wrong variant"),
        }
    }

    #[inline(never)]
    fn eval_switch(
        &self,
        f: &mut Frame,
        scrutinee: &Expr,
        arms: &[(u32, Block)],
        default: &Option<Block>,
        at: &Expr,
    ) -> R<Value> {
        let span = at.span;
        let tag = match self.eval(f, scrutinee)? {
            Value::Enum { tag, .. } => tag,
            _ => internal(span, "switch on a non-enum"),
        };
        match arms.iter().find(|(t, _)| *t == tag) {
            Some((_, b)) => self.exec_block(f, b),
            None => match default {
                Some(b) => self.exec_block(f, b),
                None => internal(span, "switch without a matching arm"),
            },
        }
    }
}
