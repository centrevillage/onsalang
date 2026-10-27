//! The entry points: the body of a function with its parameters, a `const`,
//! and the end of a body.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ entry points

    pub(super) fn check_fn_body(&mut self, body: ExprId, ret: TyId) {
        self.frames.push(Frame { ret, loop_depth: 0 });
        let r = (|| -> R<()> {
            self.bind_params()?;
            self.with_why("the result of the function".into(), ret, |ck| ck.check_expr(body, Some(ret)))?;
            Ok(())
        })();
        let _ = r;
        self.frames.pop();
    }

    /// The types of the parameters, from the signature (the bindings are
    /// the record's).
    fn bind_params(&mut self) -> R<()> {
        let def = self.a.defs[self.def.0 as usize].clone();
        let DefKind::Fn(f) = &def.kind else { return Ok(()) };
        let Some(item) = def.item else { return Ok(()) };
        let params: Vec<Param> = match &self.ast.item(item).kind {
            onsa_syntax::ast::ItemKind::Fn(fd) => fd.params.clone(),
            onsa_syntax::ast::ItemKind::Target(inner) => match inner.as_ref() {
                onsa_syntax::ast::ItemKind::Fn(fd) => fd.params.clone(),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let mut sig_params = (0..).zip(f.params.iter());
        for p in &params {
            match &p.name {
                ParamName::SelfParam(span) => {
                    let Some(st) = self.self_ty else { continue };
                    let id = self.local_of(Origin::SelfParam)?;
                    self.bind_local(id, st, false, *span)?;
                }
                ParamName::Ident(name) => {
                    let Some((k, sig)) = sig_params.next() else { continue };
                    let id = self.local_of(Origin::Param(k))?;
                    self.bind_local(id, sig.ty, p.mode == Mode::Borrow, name.span)?;
                }
                ParamName::Wild(_) => {
                    sig_params.next();
                }
            }
        }
        Ok(())
    }

    pub(super) fn check_const(&mut self, value: ExprId, ty: TyId) {
        self.frames.push(Frame { ret: ty, loop_depth: 0 });
        let r = (|| -> R<()> {
            self.check_expr(value, Some(ty))?;
            // E0407: the result must be Copy (static Shared placement is phase 2).
            if let Some(k) = self.a.kind_of(ty)
                && k != Kind::Copy
            {
                let span = self.expr(value).span;
                let shown = self.display(ty);
                return Err(self.err(
                    Code::E0407,
                    span,
                    format!("a `const` must be Copy in this version; `{shown}` is {} (§6.6)", k.name()),
                ));
            }
            Ok(())
        })();
        let _ = r;
        self.frames.pop();
        // The literals first (E0408, E0401 of `-` on an unsigned type): the evaluation
        // below reads the values they denote.
        if !self.failed {
            self.check_deferred_end();
        }
        if !self.failed
            && let Some(v) = crate::consteval::eval(self, value)
        {
            // A negation of a value is evaluated, not folded into a literal (S-227), so it can
            // leave the type (`-(-2147483648)`, `-LOW`): the evaluation panics, E0419 (§6.6).
            // A stopgap for the value of the whole initializer until the evaluator of W9-03
            // (R-155) checks every operation; an out-of-range value must not reach Core.
            if let Some(k) = self.const_overflow(&v, ty) {
                let span = self.expr(value).span;
                self.err(
                    Code::E0419,
                    span,
                    format!("the compile-time evaluation of this `const` overflows `{}` (§6.6, §3.4)", k.name()),
                );
                return;
            }
            self.a.const_values.insert(self.def, v);
        }
    }

    /// E0406 at the first expression whose type still has a variable that is not a
    /// literal's at the end of the body (§4.7). The origins of `deferred.rs` name the
    /// expression that made a variable; this net catches every variable no origin covers,
    /// so that no open type reaches the lowering.
    // SPEC-GAP(S-262): a variable that only diverging expressions decide (`let x = { return }`,
    // `let x = if c { return } else { return }`) has no type: E0406 at that expression.
    fn open_variable_net(&mut self) {
        let mut open: Vec<(Span, ExprId)> = Vec::new();
        for (&e, &t) in &self.info.expr_types {
            if self.infer.has_open_vars(&self.a.types, t) {
                open.push((self.expr(e).span, e));
            }
        }
        // The first in the source; of nested ones starting together, the outermost.
        open.sort_by_key(|(s, e)| (s.start, std::cmp::Reverse(s.end), e.0));
        if let Some(&(span, _)) = open.first() {
            self.diag(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0406,
                    span,
                    "the type of this expression cannot be determined by the end of the function; annotate it (§4.7)",
                )
                .with_found(self.src(span)),
            );
        }
    }

    /// The integer type an evaluated `const` value leaves, looking into arrays, tuples and
    /// structs (the stopgap of `check_const`).
    fn const_overflow(&mut self, v: &crate::consteval::ConstValue, ty: TyId) -> Option<IntKind> {
        use crate::consteval::ConstValue as V;
        match (v, self.ty(ty)) {
            (V::Int(n), Ty::Int(k)) => (!(k.range().0..=k.range().1).contains(n)).then_some(k),
            (V::Array(xs), Ty::Array(e, _)) => xs.iter().find_map(|x| self.const_overflow(x, e)),
            (V::Tuple(xs), Ty::Tuple(ts)) => xs.iter().zip(ts).find_map(|(x, t)| self.const_overflow(x, t)),
            (V::Struct(xs), Ty::Named(d, args)) => {
                let s = self.a.def(d).as_struct().cloned()?;
                let Fields::Named(fs) = &s.fields else { return None };
                let tys: Vec<TyId> = fs.iter().map(|f| self.subst(f.ty, &args)).collect();
                xs.iter().zip(tys).find_map(|(x, t)| self.const_overflow(x, t))
            }
            _ => None,
        }
    }

    /// The checks at the end of the body (`deferred.rs`) and the resolution of the tables.
    pub(super) fn finish(mut self) -> BodyInfo {
        if !self.failed {
            self.check_deferred_end();
        }
        if !self.failed {
            self.open_variable_net();
        }
        // Resolve the tables.
        let keys: Vec<ExprId> = self.info.expr_types.keys().copied().collect();
        for e in keys {
            let t = self.info.expr_types[&e];
            let r = self.infer.resolve(&mut self.a.types, t);
            self.info.expr_types.insert(e, r);
        }
        for l in 0..self.info.locals.len() {
            let t = self.info.locals[l].ty;
            self.info.locals[l].ty = self.infer.resolve(&mut self.a.types, t);
        }
        for i in 0..self.info.instances.len() {
            for j in 0..self.info.instances[i].args.len() {
                let t = self.info.instances[i].args[j];
                self.info.instances[i].args[j] = self.infer.resolve(&mut self.a.types, t);
            }
        }
        self.info.complete = !self.failed;
        self.info
    }
}
