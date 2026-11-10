//! The names of a body as a chain (§15.1, §4.5, §2.2): a chain of an
//! expression (`a.b.c`), the path of a hole of a string (§2.4), of a pattern
//! and of a struct literal. The head of a chain is a local, a parameter of
//! the heading (§4.5), a name of the body of the module (`Modules::lookup`:
//! the prelude and the builtin types, the items, the names of the `use`) or,
//! in a flow body, a builtin name of the flow (§2.2, §11.4), in that order;
//! the elements after it are members of what the one before names
//! (`Modules::members`), up to a value, whose fields and methods are the
//! types stage's; after a type parameter, the members its bounds give. The
//! path of a pattern or a struct literal names an item of the module's names
//! alone.
//!
//! A name that is not found, or whose kind the place does not take, is the
//! error of the names stage that stops the walk of the body (§18.1); a name
//! the names stage holds as an error stops it with no diagnostic (S-692).

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, Ident, PatId, Path, TypeArgList};

use super::kinds::Want;
use super::{Fail, PatRes, PathRes, StructRes, W, Walker};
use crate::Analysis;
use crate::body::slot::{Form, slot_of};
use crate::def::{Bound, GenericKind};
use crate::flow_names::FlowBuiltin;
use crate::names::{BuiltinMember, builtin_ty};
use crate::resolve::NameKind;
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::traits::{MAX, MIN, implies, member_note};
use crate::ty::{Ty, TyId};

/// The names of a chain with their nodes, and its type arguments, each with
/// the index of the name before it ([`Walker::chain`]).
pub(super) type Chain<'a> = (Vec<(ExprId, &'a Ident)>, Vec<(usize, ExprId)>);

/// What the types stage does with the end of a chain of names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Place {
    /// A value, whose fields may follow.
    Value,
    /// The callee of `v.(x)`: as a value.
    DotCallee,
    /// The callee of the call `.0` (`f(x)`, `a.m(x)`, `x.m!(y)`): its last
    /// name may be a method of the value before it, or an associated function.
    Callee(ExprId),
    /// The callee of the instance `.0` (`f~(x)`) of a flow body: its errors
    /// come before the `~` of `flow.rs` (§2.6, S-590, R-247). Outside a flow
    /// body the call is an E0821 before its callee (S-815).
    Instance(ExprId),
    /// The `[…]` of a callee after a field (`p.m[I32](1)`): the type
    /// arguments of a method or an index, which the types stage tells apart
    /// (§4.5); the walk records what it finds, but a method named through
    /// its type, neither of them (E0308).
    TypeOrValue,
}

/// The function `panic` of the prelude (§9.2).
pub(super) const PANIC: Entity = Entity::Builtin(Builtin::Panic);

/// Whether the entity is a value at the place of a value: a function (of
/// an `extern` block too, a value of the error type), a constant, a variant
/// or `panic` ([`NameKind::is_value`]). The
/// fields and methods of a value follow it; a name after what is neither a
/// value nor a namespace has no members.
pub(crate) fn is_value(a: &Analysis, e: Entity) -> bool {
    NameKind::of(e, &a.defs).is_some_and(NameKind::is_value)
}

/// The span from the first name of `segs` to its last.
pub(super) fn span_of(segs: &[&Ident]) -> Span {
    let (first, last) = (segs[0].span, segs[segs.len() - 1].span);
    Span::new(first.file, first.start, last.end)
}

pub(super) fn path_of(segs: &[&Ident]) -> Path {
    Path { segments: segs.iter().map(|&s| s.clone()).collect(), span: span_of(segs) }
}

impl<'a> Walker<'a> {
    /// The records of the chain of names `e` ends at the place `place`, at
    /// the nodes of the names it resolves; a node that is no chain walks its
    /// children.
    pub(super) fn name_at(&mut self, e: ExprId, place: Place) -> W {
        let Some((chain, lists)) = self.chain(e) else {
            return match &self.ast.expr(e).kind {
                // A field of a value that is no name (`f().x`).
                ExprKind::Path(_) | ExprKind::Field { .. } => self.exprs(self.ast.sub_exprs(e)),
                // After a method of such a value (U2b).
                ExprKind::TypeArgs { args, .. } => Err(self.fail(self.type_args(args.span))),
                _ => self.expr(e),
            };
        };
        let (nodes, names): (Vec<ExprId>, Vec<&Ident>) = chain.iter().copied().unzip();
        self.listed = lists.clone();
        let (records, fail) = self.resolve(&names, &nodes, place);
        self.listed.clear();
        let fail = match lists.is_empty() {
            true => fail,
            false => self.lists((&nodes, &names), &lists, &records, fail),
        };
        for (&(e, _), r) in chain.iter().zip(records) {
            self.out.paths.insert(e, r);
        }
        if matches!(fail, Some(Fail::Held)) {
            self.out.held.insert(e);
            // In a constant expression, the names after it are read
            // (`Self::const_expr`).
            if self.in_const {
                self.const_held = true;
                return Ok(());
            }
        }
        fail.map_or(Ok(()), |f| Err(self.fail(f)))
    }

    /// The records of the names of a chain, one for each element from its
    /// head to the last one the names stage resolves, and the error that
    /// stopped it. `nodes`: the expression of each element, none in a hole
    /// of a string (where a candidate writes no other form).
    pub(super) fn resolve(&mut self, segs: &[&Ident], nodes: &[ExprId], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let head = segs[0];
        if let Some(b) = self.lookup(head).or_else(|| self.outer.get(&head.name).copied()) {
            return (vec![PathRes::Local(b)], None);
        }
        if head.name == crate::names::SELF_VALUE {
            let d = Diagnostic::new(Stage::Names, Code::E0302, head.span, "`self` is only available inside a method");
            return (Vec::new(), Some(Fail::Report(d.with_found(crate::names::SELF_VALUE))));
        }
        match self.heading(head) {
            Some(PathRes::TypeParam(i)) => return self.type_param(i, segs, nodes, place),
            Some(r) => return (vec![r], None),
            None => {}
        }
        if let Some(f) = self.effect_var(segs, Some(place)) {
            return (Vec::new(), Some(f));
        }
        let a = self.a;
        if let Some(b) = self.flow_name(&head.name) {
            return self.flow_builtin(b, segs, place);
        }
        let (first, owner) = match a.path_head(self.m, &path_of(segs), self.self_ty) {
            Ok(found) => found,
            Err(ResolveError::Failed) => return (Vec::new(), Some(Fail::Held)),
            Err(ResolveError::NotFound { .. }) => return (Vec::new(), Some(self.not_found(head))),
            Err(err) => return (Vec::new(), Some(Fail::Report(err.into_diagnostic()))),
        };
        // `panic` is called, and is no value (§6.1, S-887).
        if first == PANIC
            && !(segs.len() == 1 && matches!(place, Place::Callee(_) | Place::DotCallee | Place::Instance(_)))
        {
            return (Vec::new(), Some(Fail::Report(Self::panic_as_a_value(segs))));
        }
        let typed = a.typed_members(first, owner, segs[1..].iter().copied(), self.m);
        let (err, owner, of) = (typed.err, typed.owner, typed.at);
        let mut out = Vec::new();
        let mut cur = first;
        for e in typed.reached {
            out.push(PathRes::Namespace(cur));
            cur = e;
        }
        // The element that is no member of `of` (the last reached, or the
        // type an alias there stands for), and whether it is the name of the
        // method of a call.
        let at = out.len() + 1;
        let method = matches!(place, Place::Callee(_) | Place::Instance(_)) && at + 1 == segs.len();
        // `Option.None`, `Result.Ok(1)`, `O.None` (S-607).
        let (variant, called) = match &err {
            Some(ResolveError::NotFound { .. }) => {
                // A method of a builtin type with a name after it is no value
                // either (`Str.len.zz`, as `P.get.zz`).
                let place = if at + 1 == segs.len() { place } else { Place::Value };
                let called = self.builtin_called(of, &segs[..=at], place);
                (self.qualified_variant(&path_of(segs), at, (of, owner)), called)
            }
            _ => (None, None),
        };
        // The namespace a name is not found in has its record, before the
        // type arguments after it (`Wrap::[Nope].nope2`, `type_args.rs`).
        if let Some(ResolveError::NotFound { .. }) = err {
            out.push(PathRes::Namespace(cur));
        }
        let fail = match err {
            // An alias of the error type stands for a failed name (§18.1, S-728).
            None if a.alias_type(cur).is_err() => Some(Fail::Held),
            None => {
                out.push(PathRes::Item { entity: cur, owner });
                let kind = NameKind::of(cur, &a.defs);
                kind.and_then(|k| self.kind_fail(k, segs, place)).or_else(|| self.method_form(cur, segs, place))
            }
            // A value, or the receiver of a method (what is no value there
            // is the types stage's error, unless the check does not read it;
            // in a constant expression, the reader's E0417, S-967); a method
            // named through its type is no value whatever follows it.
            Some(ResolveError::NotANamespace { .. }) if is_value(a, cur) => {
                let method = self.method_form(cur, &segs[..at], Place::Value);
                if method.is_none() {
                    out.push(PathRes::Item { entity: cur, owner });
                }
                method
            }
            Some(ResolveError::NotANamespace { kind: Some(k), .. }) if !k.is_namespace() => {
                Some(Fail::Report(self.no_namespace(&segs[..=at], k)))
            }
            // What is no namespace before the method of a call (a namespace
            // with no such member is the E0302 below: `Alloc.x()`, R-300).
            Some(err @ ResolveError::NotANamespace { kind, .. })
                if method
                    && !kind.is_some_and(NameKind::is_namespace)
                    && !a.unread(self.m, &path_of(&segs[..=at]), &err) =>
            {
                out.push(PathRes::Item { entity: cur, owner });
                None
            }
            Some(ResolveError::NotFound { .. }) if variant.is_some() => variant.map(Fail::Report),
            Some(ResolveError::NotFound { .. }) if called.is_some() => called,
            Some(err) => Some(self.no_member(err, segs, nodes, place, (at, of, owner))),
        };
        // A chain held as an error has no record, as one held at its head
        // (`BodyNames`): the types stage stops at its head.
        if matches!(fail, Some(Fail::Held)) {
            out.clear();
        }
        (out, fail)
    }

    /// The chain `segs` from the type parameter `param`, a type (§15.1): the
    /// member after it is of its bounds (§3.3, [`crate::traits::member`]),
    /// as the member of a type is; a name its bounds do not give is not
    /// found, of a parameter whose bounds were all read (§18.1).
    fn type_param(&self, param: u32, segs: &[&Ident], nodes: &[ExprId], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let head = vec![PathRes::TypeParam(param)];
        let Some(name) = segs.get(1) else {
            let kind = self.kind_fail(NameKind::Type, segs, place);
            return (head, Some(kind.unwrap_or_else(|| self.not_found(segs[0]))));
        };
        let g = &self.generics[param as usize];
        let GenericKind::Type { bounds, unknown, .. } = &g.kind else {
            onsa_diag::internal::bug(Some(name.span), "a type parameter of another kind");
        };
        let Some(member) = crate::traits::member(self.a, bounds, &name.name) else {
            if *unknown {
                return (Vec::new(), Some(Fail::Held));
            }
            let float = bounds.iter().any(|&b| implies(b, Bound::Float));
            let d = ResolveError::NotFound { name: name.name.clone(), span: name.span }.into_diagnostic();
            let d = match (
                float.then(|| self.float_min(segs, 1, nodes, place)).flatten(),
                member_note(&g.name, &name.name),
            ) {
                (Some(fix), _) => d.with_fix(fix),
                (None, Some(note)) => d.with_rule(note),
                (None, None) => d,
            };
            return (head, Some(Fail::Report(d)));
        };
        // Up to the member, a value, whose fields and methods may follow.
        let (at, place_at) = if segs.len() == 2 { (segs, place) } else { (&segs[..2], Place::Value) };
        let entity = Entity::Member(member);
        let kind = NameKind::of(entity, &self.a.defs);
        let fail =
            kind.and_then(|k| self.kind_fail(k, at, place_at)).or_else(|| self.method_form(entity, at, place_at));
        (vec![head[0].clone(), PathRes::BoundMember { param, member }], fail)
    }

    /// The error `err` of `segs[at]`, no member of `of` as written (`owner`):
    /// after a float type, with the candidate of `MIN`.
    fn no_member(
        &self,
        err: ResolveError,
        segs: &[&Ident],
        nodes: &[ExprId],
        place: Place,
        (at, of, owner): (usize, Entity, Option<TyId>),
    ) -> Fail {
        let fail = self.member_error(&path_of(&segs[..=at]), self.written(err, &segs[..=at], owner));
        let float = builtin_ty(self.a, of).is_some_and(|t| matches!(self.a.types.get(t), Ty::Float(_)));
        match (fail, float.then(|| self.float_min(segs, at, nodes, place)).flatten()) {
            (Fail::Report(d), Some(fix)) => Fail::Report(d.with_fix(fix)),
            (fail, _) => fail,
        }
    }

    /// The candidate of the E0302 of `MIN` at `segs[at]` after a float type
    /// or a `T: Float`, `-F32.MAX` (§6.6), in parentheses where a prefix form
    /// takes them or after a `-` (`--` is no prefix, §3.1): none of another
    /// name, at a place that takes no such form (a callee, a hole of a
    /// string), and in a constant expression of §4.5, which has no float.
    fn float_min(&self, segs: &[&Ident], at: usize, nodes: &[ExprId], place: Place) -> Option<Fix> {
        let last = at + 1 == segs.len();
        if segs[at].name != MIN || self.in_const || (last && place != Place::Value) {
            return None;
        }
        let slot = slot_of(self.ast, self.root, *nodes.get(at)?)?.slot;
        let (head, name) = (segs[0].span, segs[at].span);
        let wraps = slot.wraps(Form::Prefix) || self.text[..head.start as usize].ends_with('-');
        let (open, close) = if wraps { ("(-", ")") } else { ("-", "") };
        let text = format!("{open}{}.{MAX}{close}", self.src(span_of(&segs[..at])));
        let edits = vec![Edit::insert(head.file, head.start, open), Edit::replace(name, format!("{MAX}{close}"))];
        Some(Fix::new(format!("write `{text}`"), edits))
    }

    /// E0308 for `panic` at the place of a value, or with a name after it
    /// (`segs`, §6.1): it has no type to be a value of.
    fn panic_as_a_value(segs: &[&Ident]) -> Diagnostic {
        let message = "`panic` is no value: it can only be called";
        Diagnostic::new(Stage::Names, Code::E0308, span_of(segs), message)
            .with_found(segs.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join("."))
            .with_rule(
                "call it as `panic(\"…\")`; a function value that panics is an anonymous function \
                 with its result type written, `fn(x: I32) -> I32 { panic(\"…\") }` (§6.1)",
            )
    }

    /// The error of a path that did not resolve (`err`): none for what the
    /// check does not read ([`Analysis::unread`]), else its diagnostic.
    fn member_error(&self, path: &Path, err: ResolveError) -> Fail {
        match self.a.unread(self.m, path, &err) {
            true => Fail::Held,
            false => Fail::Report(err.into_diagnostic()),
        }
    }

    /// E0302 for the head of a chain not found: one form wherever the chain
    /// is (a value, a callee, a hole, a constant expression).
    fn not_found(&self, head: &Ident) -> Fail {
        Fail::Report(ResolveError::NotFound { name: head.name.clone(), span: head.span }.into_diagnostic())
    }

    /// E0302 for the variant of the prelude `path[at]` named through its
    /// type `of` (`Option.None`, `Result.Ok(1)`, `Option.None =>`; §4.1,
    /// S-607): the variants are names of the prelude, not members of the
    /// type. The candidate takes off the qualifier, and then reads the name
    /// of the prelude (none when an item clashes with it, an E0304, and in a
    /// constant expression, where a variant is no constant), with the type
    /// arguments of the qualifier after it (`None::[I32]`): those written
    /// after the type, or those of the type an alias stands for (`alias`).
    fn qualified_variant(&self, path: &Path, at: usize, (of, alias): (Entity, Option<TyId>)) -> Option<Diagnostic> {
        let a = self.a;
        let name = &path.segments[at];
        let variant = a.prelude.get(&name.name).copied()?;
        let (Entity::Def(ty), Entity::Variant(owner, _)) = (of, variant) else { return None };
        if ty != owner {
            return None;
        }
        let msg = format!("`{}` is a variant of the prelude, not a member of the type `{}`", name.name, a.def(ty).name);
        let d = Diagnostic::new(Stage::Names, Code::E0302, name.span, msg)
            .with_found(name.name.clone())
            .with_rule(format!("a variant of the prelude is written by its name alone (`{}`, §4.1)", name.name));
        let args = match (&self.listed[..], alias) {
            ([], None) => Some(String::new()),
            ([], Some(t)) => self.shown_args(t),
            (&[(k, x)], _) if k + 1 == at => match &self.ast.expr(x).kind {
                ExprKind::TypeArgs { args, .. } => Some(self.src(args.span)),
                _ => None,
            },
            _ => None,
        };
        let (Some(args), false) = (args, self.in_const) else { return Some(d) };
        let names = (&a.prelude, &a.defs[..], &a.builtin_key);
        Some(match a.modules.body_fix(self.m, path, at, Some(variant), names) {
            Ok(fix) if args.is_empty() => d.with_fix(fix),
            Ok(fix) => {
                let edits = [fix.edits(), &[Edit::insert(name.span.file, name.span.end, &args)]].concat();
                d.with_fix(Fix::new(format!("write `{}{args}`", name.name), edits))
            }
            // An item that clashes with the name of the prelude (E0304).
            Err(_) => d,
        })
    }

    /// The type arguments of the type `t` an alias stands for, as written
    /// after a name (`::[I32]` of `Option[I32]`): none when one names a type
    /// the module does not see by its name, or is a type with an error (it
    /// has no text of a type: `type X = Option[Nope]`, `X.None`).
    fn shown_args(&self, t: TyId) -> Option<String> {
        let a = self.a;
        let Ty::Named(_, args) = a.types.get(t) else { return Some(String::new()) };
        let seen = |n: crate::DefId| a.modules.lookup(self.m, &a.def(n).name, &a.prelude) == Some(Entity::Def(n));
        let shown = (args.iter())
            .map(|&x| {
                let written =
                    a.types.named(x).into_iter().all(seen) && !a.types.mentions_param(x) && !a.types.has_error(x);
                written.then(|| a.display_type(x))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(if shown.is_empty() { String::new() } else { format!("::[{}]", shown.join(", ")) })
    }

    /// The builtin name of a flow `name` is, in a flow body, where no item
    /// or `use` takes it (that one is an E0304, and held as an error).
    pub(super) fn flow_name(&self, name: &str) -> Option<FlowBuiltin> {
        let a = self.a;
        let found = a.modules.lookup(self.m, name, &a.prelude).is_some() || a.modules.held_as_error(self.m, name);
        FlowBuiltin::named(name).filter(|_| self.flow && !found)
    }

    /// A builtin name of a flow body alone at `segs` (§2.2, §11.4): the
    /// callee of a call (`prev~(x)`, `sample_rate()`; its mark is `flow.rs`'s,
    /// E0811, E0812); anywhere else, after it a `.` too (`prev.x~(x, 0.0)`,
    /// S-723), E0308 (S-720, the one place of its error in a body).
    fn flow_builtin(&self, b: FlowBuiltin, segs: &[&Ident], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let called = match place {
            Place::Instance(_) | Place::Callee(_) => segs.len() == 1,
            Place::Value | Place::DotCallee | Place::TypeOrValue => false,
        };
        let fail = (!called).then(|| Fail::Report(b.misplaced(segs.iter().map(|s| s.span), self.text)));
        (vec![PathRes::FlowBuiltin(b)], fail)
    }

    /// The error `err` of the element after `segs[..len - 1]` as written,
    /// when an alias or `Self` passed (`owner`): `Q.nope`, not the name of the
    /// type it stands for (W4-04 U6).
    fn written(&self, err: ResolveError, segs: &[&Ident], owner: Option<TyId>) -> ResolveError {
        match err {
            ResolveError::NotFound { span, .. } if owner.is_some() => {
                ResolveError::NotFound { name: self.src(span_of(segs)), span }
            }
            err => err,
        }
    }

    /// The type or const parameter `name` of the heading.
    fn heading(&self, name: &Ident) -> Option<PathRes> {
        let (i, g) = (0..).zip(self.generics).find(|(_, g)| g.name == name.name)?;
        self.a.note_use(g.span, name.span);
        match g.kind {
            GenericKind::Type { .. } => Some(PathRes::TypeParam(i)),
            GenericKind::Const(_) => Some(PathRes::ConstParam(i)),
            GenericKind::Effect => None,
        }
    }

    /// The E0308 of the effect row variable of the heading at the head of
    /// `segs`, a name that is neither a namespace nor a value (§15.1, §8.1):
    /// of a `.` after it, as in a heading (R-406), and of it alone at `place`
    /// (R-411); none for another path, and where `place` reads no value.
    fn effect_var(&self, segs: &[&Ident], place: Option<Place>) -> Option<Fail> {
        let g = self.generics.iter().find(|g| g.name == segs[0].name && matches!(g.kind, GenericKind::Effect))?;
        let kind = NameKind::of_generic(&g.kind);
        match segs {
            [head, next, ..] => Some(Fail::Report(crate::sig::member_error(head, next, kind).into_diagnostic())),
            _ => self.kind_fail(kind, segs, place?),
        }
    }

    /// The chain of names `e` ends (`a.b.c` is `Field(Field(Path(a), b), c)`),
    /// from its head, with the node of each, and its type arguments
    /// (`Buf::[F32].zeroed`, §4.5), each with the index of the name before
    /// it; none when its head is no name (`f().x`).
    pub(super) fn chain(&self, e: ExprId) -> Option<Chain<'a>> {
        let ast = self.ast;
        let (mut out, mut lists) = (Vec::new(), Vec::new());
        let mut cur = e;
        loop {
            match &ast.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    out.push((cur, name));
                    cur = *base;
                }
                ExprKind::TypeArgs { base, .. } => {
                    lists.push((out.len(), cur));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    out.push((cur, &p.segments[0]));
                    out.reverse();
                    let n = out.len();
                    return Some((out, lists.into_iter().rev().map(|(after, x)| (n - after - 1, x)).collect()));
                }
                _ => return None,
            }
        }
    }

    /// The item a path of a pattern or a struct literal names, of the names
    /// of the module (as a type is named), and the type an alias or `Self`
    /// before it stands for; a path that ends at an alias or at `Self` names
    /// the type (`P { x }`, `Self { x }`). A name of a kind the place does
    /// not take (`want`) is E0308 (§15.1, §7): a struct literal and a struct
    /// pattern name a type, a path with fields after it a variant, and one
    /// with nothing after it a variant or a constant (the form of each is the
    /// types stage's).
    fn item(&self, path: &Path, want: Want) -> Result<(Entity, Option<TyId>, Entity), Fail> {
        let a = self.a;
        let segs: Vec<&Ident> = path.segments.iter().collect();
        let head = segs[0];
        let error = |err| self.member_error(path, err);
        // A builtin name of a flow in a pattern (`prev(z) =>`, S-720).
        if let Some(b) = self.flow_name(&head.name) {
            return Err(Fail::Report(b.misplaced(path.segments.iter().map(|s| s.span), self.text)));
        }
        // A type or const parameter in a pattern (S-185) or at the head of
        // a struct literal (`M { x: 1 }`, R-302).
        if let ([_], Some(r)) = (&segs[..], self.heading(head)) {
            let kind = if matches!(r, PathRes::ConstParam(_)) { NameKind::ConstParam } else { NameKind::Type };
            // A type parameter is a type, and no struct (`T { x: 1 }`).
            let no_struct = || Fail::Report(crate::body::not_a_struct(head.name.clone(), head.span));
            return Err(self.want(kind, &segs, want).unwrap_or_else(no_struct));
        }
        if let Some(f) = self.effect_var(&segs, None) {
            return Err(f);
        }
        let (first, typed) = a.typed_path(self.m, path, self.self_ty).map_err(error)?;
        let at = typed.reached.len() + 1;
        match typed.err {
            // A pattern takes no type arguments (§4.5).
            Some(err @ ResolveError::NotFound { .. }) => match self.qualified_variant(path, at, (typed.at, None)) {
                Some(d) => Err(Fail::Report(d)),
                // An associated name of a builtin type (`F32.PI { x: 1 }`, R-302).
                None => {
                    let member = (at + 1 == segs.len())
                        .then(|| crate::names::builtin_member(a, typed.at, &segs[at].name))
                        .flatten();
                    match (member.and_then(|_| self.want(NameKind::Function, &segs, want)), member) {
                        (Some(f), _) => Err(f),
                        (None, Some(BuiltinMember::Missing { feature })) => {
                            Err(Fail::Report(self.missing_name(feature, &segs)))
                        }
                        (None, _) => Err(error(self.written(err, &segs[..=at], typed.owner))),
                    }
                }
            },
            Some(err) => Err(error(err)),
            None => {
                let end = typed.reached.last().copied().unwrap_or(first);
                let (entity, owner) = match a.alias_type(end).map_err(error)? {
                    Some((ns, t)) => (ns, Some(t)),
                    // An alias of no struct: the types stage reads the alias.
                    None => (end, typed.owner),
                };
                match NameKind::of(entity, &a.defs).and_then(|k| self.want(k, &segs, want)) {
                    Some(f) => Err(f),
                    None => Ok((entity, owner, end)),
                }
            }
        }
    }

    /// The member of the type parameter that the path `segs` of two names
    /// starts at, read as an expression reads it ([`Self::type_param`]), of
    /// the kind `want` takes. `None` for another path.
    fn bound_member(&self, segs: &[&Ident], want: Want) -> Option<Result<PatRes, Fail>> {
        let [head, _] = segs else { return None };
        let Some(PathRes::TypeParam(i)) = self.heading(head) else { return None };
        let (records, fail) = self.type_param(i, segs, &[], Place::Value);
        let Some(&PathRes::BoundMember { param, member }) = records.last() else {
            return fail.map(Err);
        };
        let kind = NameKind::of(Entity::Member(member), &self.a.defs);
        Some(match kind.and_then(|k| self.want(k, segs, want)) {
            Some(f) => Err(f),
            None => Ok(PatRes::BoundMember { param, member }),
        })
    }

    /// The item the path of the pattern `p` names (§7).
    pub(super) fn ctor(&mut self, p: PatId, path: &Path, want: Want) -> W {
        let segs: Vec<&Ident> = path.segments.iter().collect();
        let found = match self.bound_member(&segs, want) {
            Some(found) => found,
            None => self.item(path, want).map(|(entity, owner, _)| PatRes::Ctor { entity, owner }),
        };
        match found {
            Ok(r) => {
                self.out.pats.insert(p, r);
                Ok(())
            }
            Err(f) => self.fail_at_let(f),
        }
    }

    /// The item the path of the struct literal `e` names, and its type
    /// arguments `lists` (§4.5): of the struct, after its name
    /// (`Pr::[U8] { a: 1 }`); after any other name (a module, `Self`), E0412.
    pub(super) fn struct_lit(&mut self, e: ExprId, path: &Path, lists: &[(usize, TypeArgList)], filled: bool) -> W {
        let (entity, owner, end) = self.item(path, Want::Type).map_err(|f| self.fail(f))?;
        self.out.structs.insert(e, StructRes { entity, owner });
        if let (true, Entity::Def(d) | Entity::Member(d)) = (filled, entity) {
            self.out.filled.insert(d);
        }
        self.struct_args(e, path, lists, end);
        Ok(())
    }
}
