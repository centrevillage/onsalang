//! The names of a body as the names stage resolved them
//! ([`crate::names::body::BodyNames`]): the values they name, the type of a
//! field, and the types written in the body. The types stage reads the
//! record and resolves no name of its own (D-15), except the errors the
//! flow stage reports at the callee of an instance and after `^` (W4-12,
//! W7-04: `flow/check.rs`, `flow_map.rs`).

use super::*;
use crate::names::body::PathRes;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ names

    /// The value a name or a chain of names (`a.b.c`) ends at, as the
    /// record has it; a node with no record is a field of the value before
    /// it (`p.x`), or a node of a chain with a name held as an error (§18.1,
    /// S-692), which has no record down to its head, where the check stops.
    pub(super) fn check_name(&mut self, e: ExprId, expected: Option<TyId>) -> R<TyId> {
        let Some(r) = self.names.paths.get(&e).cloned() else {
            let ExprKind::Field { base, name } = &self.expr(e).kind else { return Err(self.held_stop()) };
            // The span of the operand: of the chain so far when it is one of
            // names (`p.x.y`), else of the value (`f().x`).
            let at = if self.of_names(*base) { e } else { *base };
            let bt = self.check_expr(*base, None)?;
            let bt = self.known(bt, self.expr(at).span, "value")?;
            return self.field_type(bt, name);
        };
        if matches!(r, PathRes::Item { .. }) {
            self.namespaces_before(e)?;
        }
        let name = self.last_name(e);
        let t = self.value_of_record(r, e, &name, self.expr(e).span, expected)?;
        Ok(self.record(e, t))
    }

    /// The type of the value the record `r` of the name `name` names, at the
    /// node `e` (its targets go there), `span` that of the chain up to the
    /// name: a local, a const parameter, an item or an associated constant
    /// of a builtin type.
    fn value_of_record(&mut self, r: PathRes, e: ExprId, name: &Ident, span: Span, expected: Option<TyId>) -> R<TyId> {
        match r {
            PathRes::Local(b) => {
                let id = LocalId(b.0);
                if self.flow.is_some() {
                    self.flow_use_local(id, span)?;
                }
                self.info.targets.insert(e, Target::Local(id));
                Ok(self.local_ty(id))
            }
            PathRes::ConstParam(i) => {
                self.info.targets.insert(e, Target::ConstParam(i));
                Ok(self.u32())
            }
            PathRes::Item { entity, owner } => match self.value_of_entity((entity, owner), e, name, span, expected)? {
                Some(t) => Ok(t),
                None => {
                    let shown = self.src(span);
                    Err(self.err(Code::E0401, span, format!("`{shown}` is not a value")))
                }
            },
            PathRes::BuiltinAssoc { ty, name: assoc, .. } => {
                let Some(t) = builtin::assoc_const(&mut self.a.types, ty, &assoc) else {
                    onsa_diag::internal::bug(Some(span), "an associated constant the names stage did not find")
                };
                self.info.targets.insert(e, Target::BuiltinConst { ty: t, name: assoc });
                Ok(t)
            }
            PathRes::Namespace(_) | PathRes::TypeParam(_) | PathRes::FlowBuiltin(_) => {
                onsa_diag::internal::bug(Some(span), "a value of a name the names stage reports")
            }
        }
    }

    /// The type of the hole `k` of the string literal `e` (§2.4), whose path
    /// is `path`: the value its records end at (the namespaces they pass
    /// read as an expression's, [`Self::namespaces`]), then its fields and tuple
    /// elements. A hole with no record has a name held as an error.
    pub(super) fn check_hole(&mut self, e: ExprId, k: u32, path: &Path) -> R<TyId> {
        let records = self.names.interp.get(&(e, k)).cloned().unwrap_or_default();
        let Some((at, last)) = records.last().cloned() else { return Err(self.held_stop()) };
        let segs = &path.segments;
        self.namespaces(records.iter().map(|(i, r)| (e, r.clone(), segs[*i as usize].clone())).collect())?;
        let name = &segs[at as usize];
        let span = Span::new(name.span.file, segs[0].span.start, name.span.end);
        let mut t = self.value_of_record(last, e, name, span, None)?;
        // The targets of a hole are kept by the hole (the literal is no name).
        if let Some(target) = self.info.targets.remove(&e) {
            self.info.hole_targets.insert((e, k), target);
        }
        for seg in &segs[at as usize + 1..] {
            let base = self.known(t, seg.span, "value")?;
            // A tuple element that is no tuple index of an expression
            // (`{t.01}`) is a field, which the tuple has not (E0413).
            t = match onsa_syntax::hole_tuple_index(&seg.name) {
                Some(index) => self.tuple_element(base, index, seg.span)?,
                None => self.field_type(base, seg)?,
            };
        }
        Ok(t)
    }

    /// The namespaces a chain passes before `e`, from its head, by the
    /// records of the nodes before it.
    fn namespaces_before(&mut self, e: ExprId) -> R<()> {
        let mut records = Vec::new();
        let mut cur = e;
        while let ExprKind::Field { base, .. } = &self.expr(cur).kind {
            cur = *base;
            if let Some(r) = self.names.paths.get(&cur) {
                records.push((cur, r.clone(), self.last_name(cur)));
            }
        }
        records.reverse();
        self.namespaces(records)
    }

    /// The namespaces a chain passes, of its records from its head, each at
    /// its node and with its name: none is a value but a flow, an error
    /// there (§11.6). The namespace of a def whose heading a syntax error
    /// cut is not known (S-59, R-71).
    fn namespaces(&mut self, records: Vec<(ExprId, PathRes, Ident)>) -> R<()> {
        for (node, r, name) in records {
            let PathRes::Namespace(entity) = r else { continue };
            if !matches!(entity, Entity::Def(d) if self.a.heading_failed(d)) {
                let span = self.expr(node).span;
                self.value_of_entity((entity, None), node, &name, span, None)?;
            }
        }
        Ok(())
    }

    /// The last name of the node `e` of a chain.
    pub(super) fn last_name(&self, e: ExprId) -> Ident {
        match &self.expr(e).kind {
            ExprKind::Field { name, .. } => name.clone(),
            ExprKind::Path(p) => p.segments[0].clone(),
            _ => onsa_diag::internal::bug(Some(self.expr(e).span), "a chain of names with no name"),
        }
    }

    /// Whether `e` is a chain of names (`a`, `a.b`), by its form.
    fn of_names(&self, e: ExprId) -> bool {
        match &self.expr(e).kind {
            ExprKind::Field { base, .. } => self.of_names(*base),
            ExprKind::Path(p) => p.segments.len() == 1,
            _ => false,
        }
    }

    /// The end of the check of the body at a name the names stage holds as
    /// an error or that it did not read (§18.1, S-692): no diagnostic, and
    /// what the body reads and the check does not is recorded
    /// ([`BodyInfo::read_unread`]).
    pub(crate) fn held_stop(&mut self) -> Stop {
        self.a.read_held.insert(self.def);
        self.failed = true;
        Stop
    }

    /// The record of a constructor of a pattern, and the type an alias or
    /// `Self` names it by.
    pub(crate) fn ctor_of(&mut self, pat: PatId) -> R<(Entity, Option<TyId>)> {
        match self.names.pats.get(&pat) {
            Some(crate::names::body::PatRes::Ctor { entity, owner }) => Ok((*entity, *owner)),
            _ => Err(self.held_stop()),
        }
    }

    /// The type arguments `args` of the def `d` that a path names through
    /// an alias or `Self` (`owner`, §4.4, S-91, S-595): the type `d` is of
    /// (the struct or the enum of a literal, a pattern or a variant; the
    /// type of the `impl` of an associated function) with `args` is the
    /// owner (`type Samples = Buf[F32]`, `Self` of `impl[T] G[T]` is `G[T]`).
    pub(crate) fn of_owner(&mut self, d: DefId, args: &[TyId], owner: Option<TyId>, span: Span) -> R<()> {
        let Some(owner) = owner else { return Ok(()) };
        let def = self.a.def(d);
        let ty = match (&def.kind, def.owner.map(|o| &self.a.def(o).kind)) {
            (DefKind::Struct(_) | DefKind::Enum(_), _) => self.a.types.intern(Ty::Named(d, args.to_vec())),
            (DefKind::Fn(_), Some(&DefKind::Impl(crate::def::ImplDef { self_ty, .. }))) => self.subst(self_ty, args),
            _ => return Ok(()),
        };
        self.unify_at(span, ty, owner)
    }

    /// A type written in the body, as the names stage lowered it; its
    /// diagnostic of the types stage, if any, is reported here.
    pub(crate) fn lower_type_expr(&mut self, t: onsa_syntax::ast::TypeId) -> R<TyId> {
        match self.names.types.get(&t).cloned() {
            Some((_, Some(d))) => Err(self.diag(d)),
            // An error with no diagnostic (a name held as an error, a member
            // of a def a syntax error cut): the check goes on (§18.1, S-690).
            Some((ty, None)) => Ok(ty),
            None => Err(self.held_stop()),
        }
    }

    /// Type of an entity used as a value (`None` when it is none,
    /// [`crate::names::body::is_value`]), with the type an alias or `Self`
    /// names it by ([`Self::of_owner`]). Records the target on `e`; `span`
    /// is that of the path up to the name, where an instance is made (the
    /// hole, not the whole literal, for a hole of a string).
    pub(super) fn value_of_entity(
        &mut self,
        (entity, owner): (Entity, Option<TyId>),
        e: ExprId,
        name: &Ident,
        span: Span,
        expected: Option<TyId>,
    ) -> R<Option<TyId>> {
        if !crate::names::body::is_value(self.a, entity) {
            return Ok(None);
        }
        let no_value = || onsa_diag::internal::bug(Some(name.span), "a value that `is_value` does not take");
        match entity {
            Entity::Def(d) | Entity::Member(d) => {
                let def = self.a.def(d).clone();
                match &def.kind {
                    DefKind::Fn(_) if self.a.heading_failed(d) || crate::names::self_outside_impl(self.a, entity) => {
                        Ok(Some(self.a.types.error()))
                    }
                    DefKind::Fn(f) => {
                        if f.self_mode.is_some() {
                            onsa_diag::internal::bug(Some(name.span), "a method as a value the names stage took");
                        }
                        let args = self.fresh_args(d);
                        self.of_owner(d, &args, owner, span)?;
                        let fty = self.fn_type(f, &args);
                        if let Some(exp) = expected {
                            self.unify_at(name.span, fty, exp)?;
                        }
                        let inst = self.finish_instance(d, args, span)?;
                        self.info.targets.insert(e, Target::Fn { def: d, inst });
                        Ok(Some(fty))
                    }
                    DefKind::Const(c) => {
                        self.info.targets.insert(e, Target::Const(d));
                        Ok(Some(c.ty))
                    }
                    DefKind::Unsupported(_) => Ok(Some(self.a.types.error())),
                    _ => no_value(),
                }
            }
            Entity::Variant(d, i) => {
                let args = self.fresh_args(d);
                self.of_owner(d, &args, owner, span)?;
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
                self.finish_instance(d, args, span)?;
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
                Builtin::Panic => Err(self.unsupported(name.span, Feature::Panic, &[])),
                _ => no_value(),
            },
            Entity::Module(_) => no_value(),
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
