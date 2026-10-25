//! The names in bodies: the chains of names, the paths, the constants, the
//! entities a name is, and the types of functions and fields.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ names

    /// `a.b.c` as a chain of identifiers with the expression of each prefix.
    pub(crate) fn name_chain(&self, e: ExprId) -> Option<Vec<(ExprId, Ident)>> {
        let mut out = Vec::new();
        let mut cur = e;
        loop {
            match &self.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    out.push((cur, name.clone()));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    out.push((cur, p.segments[0].clone()));
                    break;
                }
                _ => return None,
            }
        }
        out.reverse();
        Some(out)
    }

    pub(crate) fn is_local_head(&mut self, name: &str) -> bool {
        name == "self" || self.lookup_local(name).is_some() || self.const_param(name).is_some()
    }

    fn const_param(&self, name: &str) -> Option<u32> {
        self.generics.iter().position(|g| g.name == name && matches!(g.kind, GenericKind::Const(_))).map(|i| i as u32)
    }

    /// Resolve the longest prefix of a dotted name that denotes a value, then
    /// apply the remaining segments as field accesses. Records types and
    /// targets of every prefix expression. Returns the type of the whole chain.
    pub(super) fn check_chain(&mut self, chain: &[(ExprId, Ident)], expected: Option<TyId>) -> R<TyId> {
        let n = chain.len();
        let head = &chain[0].1;
        // Local, `self`, const parameter: ordinary field accesses from there.
        if self.is_local_head(&head.name) {
            let mut t = self.check_single_path(chain[0].0, head, if n == 1 { expected } else { None })?;
            for (e, name) in &chain[1..] {
                let base = self.known(t, self.expr(*e).span, "value")?;
                t = self.field_type(base, name)?;
                self.record(*e, t);
            }
            return Ok(t);
        }
        // Module-level resolution of the longest value prefix.
        let mut k = 1;
        let mut value_ty: Option<TyId> = None;
        while k <= n {
            let path = Path {
                segments: chain[..k].iter().map(|(_, i)| i.clone()).collect(),
                span: self.expr(chain[k - 1].0).span,
            };
            let entity = match self.a.resolve_path(self.m, &path) {
                Ok(e) => e,
                Err(err) => {
                    // A scalar / builtin type followed by an associated builtin item.
                    if k >= 2 {
                        let prefix =
                            Path { segments: chain[..k - 1].iter().map(|(_, i)| i.clone()).collect(), span: path.span };
                        if let Ok(Entity::Builtin(b)) = self.a.resolve_path(self.m, &prefix)
                            && let Some(t) = self.builtin_const(b, &chain[k - 1].1)
                        {
                            self.info.targets.insert(
                                chain[k - 1].0,
                                Target::BuiltinConst { ty: t, name: chain[k - 1].1.name.clone() },
                            );
                            value_ty = Some(t);
                            break;
                        }
                    }
                    // A head with no `use`: the error of the whole chain, whose
                    // candidate needs the member after the head (R-39).
                    let err = match err {
                        e @ ResolveError::NeedsUse { .. } if n > 1 => {
                            let whole =
                                Path { segments: chain.iter().map(|(_, i)| i.clone()).collect(), span: path.span };
                            self.a.resolve_path(self.m, &whole).err().unwrap_or(e)
                        }
                        e => e,
                    };
                    return Err(self.resolve_error(&path, err));
                }
            };
            let last = k == n;
            // A def whose heading a syntax error cut (a flow's namespace, S-59):
            // its members are not known; the next segment does not resolve,
            // and `resolve_error` gives no diagnostic (R-71).
            if !last
                && let Entity::Def(d) = entity
                && self.a.heading_failed(d)
            {
                k += 1;
                continue;
            }
            match self.value_of_entity(entity, chain[k - 1].0, &chain[k - 1].1, if last { expected } else { None })? {
                Some(t) => {
                    value_ty = Some(t);
                    break;
                }
                None => {
                    if last {
                        let name = self.src(path.span);
                        return Err(self.err(Code::E0401, path.span, format!("`{name}` is not a value")));
                    }
                }
            }
            k += 1;
        }
        let Some(mut t) = value_ty else {
            let span = self.expr(chain[n - 1].0).span;
            return Err(self.err(Code::E0401, span, "not a value"));
        };
        self.record(chain[k - 1].0, t);
        for (e, name) in &chain[k..] {
            let base = self.known(t, self.expr(*e).span, "value")?;
            t = self.field_type(base, name)?;
            self.record(*e, t);
        }
        Ok(t)
    }

    fn builtin_const(&mut self, b: Builtin, name: &Ident) -> Option<TyId> {
        match b {
            Builtin::Scalar(t) => builtin::assoc_const(&mut self.a.types, t, &name.name),
            _ => None,
        }
    }

    /// A single identifier in expression position.
    pub(super) fn check_single_path(&mut self, e: ExprId, name: &Ident, expected: Option<TyId>) -> R<TyId> {
        if let Some(id) = self.lookup_local(&name.name) {
            if self.flow.is_some() {
                self.flow_use_local(id, name.span)?;
            }
            self.info.targets.insert(e, Target::Local(id));
            let t = self.local_ty(id);
            return Ok(self.record(e, t));
        }
        if let Some(i) = self.const_param(&name.name) {
            self.info.targets.insert(e, Target::ConstParam(i));
            let t = self.u32();
            return Ok(self.record(e, t));
        }
        if name.name == "self" {
            return Err(self.name_err(Code::E0302, name.span, "`self` is only available inside a method"));
        }
        let path = Path { segments: vec![name.clone()], span: name.span };
        let entity = match self.a.resolve_path(self.m, &path) {
            Ok(en) => en,
            Err(ResolveError::NotFound { .. }) => {
                return Err(self.name_err(
                    Code::E0302,
                    name.span,
                    format!("cannot find `{}` in this scope", name.name),
                ));
            }
            Err(err) => return Err(self.resolve_error(&path, err)),
        };
        match self.value_of_entity(entity, e, name, expected)? {
            Some(t) => Ok(self.record(e, t)),
            None => Err(self.err(Code::E0401, name.span, format!("`{}` is not a value", name.name))),
        }
    }

    /// Type of an entity used as a value (`None` when it is a type / module /
    /// namespace). Records the target on `e`.
    fn value_of_entity(&mut self, entity: Entity, e: ExprId, name: &Ident, expected: Option<TyId>) -> R<Option<TyId>> {
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                match &def.kind {
                    DefKind::Fn(_) if self.a.heading_failed(d) => Ok(Some(self.a.types.error())),
                    DefKind::Fn(f) => {
                        if f.self_mode.is_some() {
                            return Err(self.err(
                                Code::E0401,
                                name.span,
                                format!("`{}` is a method; call it as `value.{}(...)` (§6.2)", def.name, def.name),
                            ));
                        }
                        let args = self.fresh_args(d);
                        let fty = self.fn_type(f, &args);
                        if let Some(exp) = expected {
                            self.unify_at(name.span, fty, exp)?;
                        }
                        let espan = self.expr(e).span;
                        let inst = self.finish_instance(d, args, espan)?;
                        self.info.targets.insert(e, Target::Fn { def: d, inst });
                        Ok(Some(fty))
                    }
                    DefKind::Const(c) => {
                        self.info.targets.insert(e, Target::Const(d));
                        Ok(Some(c.ty))
                    }
                    DefKind::Flow(_) => Err(self.err(
                        Code::E0401,
                        name.span,
                        format!(
                            "`{}` is a flow; outside a flow body use its namespace (`{}.init`, `{}.process`, §11.6)",
                            def.name, def.name, def.name
                        ),
                    )),
                    DefKind::Unsupported => Ok(Some(self.a.types.error())),
                    _ => Ok(None),
                }
            }
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                let variant = self.a.def(d).as_enum().unwrap().variants[i as usize].clone();
                let enum_ty = self.a.types.intern(Ty::Named(d, args.clone()));
                let t = if variant.fields.is_empty() {
                    enum_ty
                } else {
                    let params: Vec<(Mode, TyId)> =
                        variant.fields.iter().map(|&f| (Mode::Borrow, self.subst(f, &args))).collect();
                    self.a.types.intern(Ty::Fn(FnTy { rt: true, params, ret: enum_ty, effects: Default::default() }))
                };
                if let Some(exp) = expected {
                    self.unify_at(name.span, t, exp)?;
                }
                // The whole path (`E.A`), where the variable is made.
                let espan = self.expr(e).span;
                self.finish_instance(d, args, espan)?;
                self.info.targets.insert(e, Target::Variant { def: d, index: i });
                Ok(Some(t))
            }
            Entity::Builtin(b) => match b {
                Builtin::None => {
                    let t = self.fresh();
                    self.defer(name.span, t, DeferredKind::Origin { what: "the type in `None`".into() });
                    let opt = self.a.types.builtin(BuiltinTy::Option, vec![t]);
                    if let Some(exp) = expected {
                        self.unify_at(name.span, opt, exp)?;
                    }
                    self.info.targets.insert(e, Target::Prelude(b));
                    Ok(Some(opt))
                }
                Builtin::Some | Builtin::Ok | Builtin::Err => {
                    let ret = self.prelude_ctor(b, name.span);
                    let param = match self.ty(ret) {
                        Ty::Builtin(BuiltinTy::Result, a) if b == Builtin::Err => a[1],
                        Ty::Builtin(_, a) => a[0],
                        _ => unreachable!("a prelude constructor makes an `Option` or a `Result`"),
                    };
                    let fty = self.a.types.intern(Ty::Fn(FnTy {
                        rt: true,
                        params: vec![(Mode::Borrow, param)],
                        ret,
                        effects: Default::default(),
                    }));
                    if let Some(exp) = expected {
                        self.unify_at(name.span, fty, exp)?;
                    }
                    self.info.targets.insert(e, Target::Prelude(b));
                    Ok(Some(fty))
                }
                _ => Ok(None),
            },
            Entity::Module(_) => Ok(None),
        }
    }

    /// The type `Some(_)` / `Ok(_)` / `Err(_)` makes at `span`: the argument's
    /// type, and an origin for the other type argument of `Result` (E0406, §4.7).
    pub(super) fn prelude_ctor(&mut self, b: Builtin, span: Span) -> TyId {
        let t = self.fresh();
        self.defer(span, t, DeferredKind::Origin { what: format!("the type in `{}`", self.src(span)) });
        match b {
            Builtin::Some => self.a.types.builtin(BuiltinTy::Option, vec![t]),
            Builtin::Ok => {
                let e2 = self.fresh();
                self.defer(span, e2, DeferredKind::Origin { what: "the error type of `Ok`".into() });
                self.a.types.builtin(BuiltinTy::Result, vec![t, e2])
            }
            _ => {
                let ok = self.fresh();
                self.defer(span, ok, DeferredKind::Origin { what: "the value type of `Err`".into() });
                self.a.types.builtin(BuiltinTy::Result, vec![ok, t])
            }
        }
    }

    pub(crate) fn fn_type(&mut self, f: &FnDef, args: &[TyId]) -> TyId {
        let params: Vec<(Mode, TyId)> = f.params.iter().map(|p| (p.mode, self.subst(p.ty, args))).collect();
        let ret = self.subst(f.ret, args);
        self.a.types.intern(Ty::Fn(FnTy { rt: f.rt, params, ret, effects: f.effects.clone() }))
    }

    /// Type of field `name` of a resolved base type.
    pub(crate) fn field_type(&mut self, base: TyId, name: &Ident) -> R<TyId> {
        match self.ty(base) {
            Ty::Named(d, args) => {
                let def = self.a.def(d).clone();
                if let DefKind::Struct(s) = &def.kind
                    && let Fields::Named(fs) = &s.fields
                    && let Some(f) = fs.iter().find(|f| f.name == name.name)
                {
                    self.field_reach(d, f, name.span)?;
                    return Ok(self.subst(f.ty, &args));
                }
                // SPEC-GAP(S-260): a field of a struct whose unit failed in the
                // syntax stage gets no diagnostic, whatever its name (the
                // fields that were not read are not known, R-71).
                if self.a.partly_read(d) {
                    return Ok(self.a.types.error());
                }
                let shown = self.display(base);
                Err(self.err(Code::E0413, name.span, format!("`{shown}` has no field `{}`", name.name)))
            }
            Ty::Error => Ok(base),
            _ => {
                let shown = self.display(base);
                Err(self.err(Code::E0413, name.span, format!("`{shown}` has no field `{}`", name.name)))
            }
        }
    }
}
