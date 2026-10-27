//! The names of a body as a chain (§15.1, §4.5, §2.2): a chain of an
//! expression (`a.b.c`), the path of a hole of a string (§2.4), of a pattern
//! and of a struct literal. The head of a chain is a local, a parameter of
//! the heading (§4.5), a name of the body of the module (`Modules::lookup`:
//! the prelude and the builtin types, the items, the names of the `use`) or,
//! in a flow body, a builtin name of the flow (§2.2, §11.4), in that order;
//! the elements after it are members of what the one before names
//! (`Modules::members`), up to a value, whose fields and methods are the
//! types stage's. The path of a pattern or a struct literal names an item
//! of the module's names alone.
//!
//! A name that is not found, or whose kind the place does not take, is the
//! error of the names stage that stops the walk of the body (§18.1); a name
//! the names stage holds as an error stops it with no diagnostic (S-692).

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{ExprId, ExprKind, Ident, PatId, Path};

use super::{Fail, PatRes, PathRes, StructRes, W, Walker};
use crate::def::{DefKind, GenericKind};
use crate::flow_names::FlowBuiltin;
use crate::resolve::{Builtin, Entity, ResolveError};
use crate::{Analysis, builtin};

/// What the types stage does with the end of a chain of names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Place {
    /// A value, whose fields may follow.
    Value,
    /// The callee of a call (`f(x)`, `a.m(x)`, `x.m!(y)`): its last name may
    /// be a method of the value before it, or an associated function.
    Callee,
    /// The callee of an instance (`f~(x)`): the flow stage reads it and
    /// reports its errors (W4-12); the walk records what it finds alone.
    Instance,
    /// A name of a constant expression (§4.5, `Walker::const_expr`): a
    /// value, whose error has the words of the constants (`cannot find `n``).
    Const,
}

/// Whether the entity is a value at the place of a value: a function, a
/// constant, a variant, a constructor of the prelude, `panic`, a flow (an
/// error there, reported by the types stage) or what this version does
/// not support. The fields and methods of a value follow it; a name after
/// what is neither a value nor a namespace has no members.
pub(crate) fn is_value(a: &Analysis, e: Entity) -> bool {
    match e {
        Entity::Def(d) | Entity::Member(d) => {
            matches!(a.def(d).kind, DefKind::Fn(_) | DefKind::Const(_) | DefKind::Flow(_) | DefKind::Unsupported)
        }
        Entity::Variant(..) => true,
        Entity::Builtin(b) => matches!(b, Builtin::None | Builtin::Some | Builtin::Ok | Builtin::Err | Builtin::Panic),
        Entity::Module(_) => false,
    }
}

/// The span from the first name of `segs` to its last.
fn span_of(segs: &[&Ident]) -> Span {
    let (first, last) = (segs[0].span, segs[segs.len() - 1].span);
    Span::new(first.file, first.start, last.end)
}

fn path_of(segs: &[&Ident]) -> Path {
    Path { segments: segs.iter().map(|&s| s.clone()).collect(), span: span_of(segs) }
}

impl<'a> Walker<'a> {
    /// The records of the chain of names `e` ends at the place `place`, at
    /// the nodes of the names it resolves; a node that is no chain walks its
    /// children.
    pub(super) fn name_at(&mut self, e: ExprId, place: Place) -> W {
        let Some(chain) = self.chain(e) else {
            return match &self.ast.expr(e).kind {
                // A field of a value that is no name (`f().x`).
                ExprKind::Path(_) | ExprKind::Field { .. } => self.exprs(self.ast.sub_exprs(e)),
                _ => self.expr(e),
            };
        };
        let names: Vec<&Ident> = chain.iter().map(|&(_, n)| n).collect();
        let (records, fail) = self.resolve(&names, place);
        for (&(e, _), r) in chain.iter().zip(records) {
            self.out.paths.insert(e, r);
        }
        match fail {
            Some(f) if place != Place::Instance => Err(self.fail(f)),
            _ => Ok(()),
        }
    }

    /// The records of the names of a chain, one for each element from its
    /// head to the last one the names stage resolves, and the error that
    /// stopped it.
    pub(super) fn resolve(&mut self, segs: &[&Ident], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let head = segs[0];
        if let Some(b) = self.lookup(&head.name) {
            return (vec![PathRes::Local(b)], None);
        }
        if head.name == "self" {
            let d = Diagnostic::new(Stage::Names, Code::E0302, head.span, "`self` is only available inside a method");
            return (Vec::new(), Some(Fail::Report(d.with_found("self"))));
        }
        match self.heading(&head.name) {
            Some(r @ PathRes::ConstParam(_)) => return (vec![r], None),
            // A type parameter is no value (`T.ZERO` from W4-04 U6).
            Some(r) => return (vec![r], Some(self.not_found(segs, place))),
            None => {}
        }
        let a = self.a;
        let Some(first) = a.modules.lookup(self.m, &head.name, &a.prelude) else {
            if !a.modules.held_as_error(self.m, &head.name)
                && let Some(b) = FlowBuiltin::named(&head.name).filter(|_| self.flow)
            {
                return self.flow_builtin(b, segs, place);
            }
            return match a.modules.head_error(self.m, &path_of(segs), (&a.prelude, &a.defs, &a.builtin_key)) {
                ResolveError::Failed => (Vec::new(), Some(Fail::Held)),
                ResolveError::NotFound { .. } => (Vec::new(), Some(self.not_found(segs, place))),
                err => (Vec::new(), Some(Fail::Report(err.into_diagnostic()))),
            };
        };
        let (reached, err) =
            a.modules.members(first, segs[1..].iter().copied(), self.m, (&a.prelude, &a.defs, &a.builtin_key));
        let mut out = Vec::new();
        let mut cur = first;
        for e in reached {
            out.push(PathRes::Namespace(cur));
            cur = e;
        }
        // The element that is no member of `cur`, and whether it is the
        // name of the method of a call.
        let at = out.len() + 1;
        let method = matches!(place, Place::Callee | Place::Instance) && at + 1 == segs.len();
        let fail = match err {
            None => {
                out.push(PathRes::Item { entity: cur, owner: None });
                None
            }
            Some(ResolveError::NotANamespace { .. })
                if matches!(cur, Entity::Builtin(Builtin::Trait(_) | Builtin::Kind(_))) =>
            {
                Some(Fail::Report(self.no_namespace(&segs[..=at])))
            }
            // A value, or the receiver of a method (what is no value there
            // is the types stage's error, unless the check does not read it).
            Some(ResolveError::NotANamespace { .. }) if is_value(a, cur) => {
                out.push(PathRes::Item { entity: cur, owner: None });
                None
            }
            Some(err @ ResolveError::NotANamespace { .. })
                if method && !a.unread(self.m, &path_of(&segs[..=at]), &err) =>
            {
                out.push(PathRes::Item { entity: cur, owner: None });
                None
            }
            Some(ResolveError::NotFound { .. }) if self.builtin_assoc(cur, segs[at], method).is_some() => {
                let assoc = self.builtin_assoc(cur, segs[at], method).expect("an associated item");
                out.extend([PathRes::Namespace(cur), assoc]);
                None
            }
            Some(err) => Some(self.member_error(&path_of(&segs[..=at]), err)),
        };
        // A chain held as an error has no record, as one held at its head
        // (`BodyNames`): the types stage stops at its head.
        if matches!(fail, Some(Fail::Held)) {
            out.clear();
        }
        (out, fail)
    }

    /// The error of a path that did not resolve (`err`): none for what the
    /// check does not read ([`Analysis::unread`]), else its diagnostic.
    fn member_error(&self, path: &Path, err: ResolveError) -> Fail {
        match self.a.unread(self.m, path, &err) {
            true => Fail::Held,
            false => Fail::Report(err.into_diagnostic()),
        }
    }

    /// E0302 for the head of `segs` not found at `place`, in the words the
    /// types stage had: it typed a chain of one name as a value apart (S-720
    /// keeps its words), and a constant as a name of a type position. The
    /// split by `place` and by the length goes with W4-04 U5 (the errors of
    /// a path), with [`Place::Const`].
    fn not_found(&self, segs: &[&Ident], place: Place) -> Fail {
        let head = segs[0];
        let alone = match place {
            Place::Value => segs.len() == 1,
            Place::Callee | Place::Instance => segs.len() <= 2,
            Place::Const => false,
        };
        let d = match alone {
            true => Diagnostic::new(
                Stage::Names,
                Code::E0302,
                head.span,
                format!("cannot find `{}` in this scope", head.name),
            )
            .with_found(head.name.clone()),
            false => ResolveError::NotFound { name: head.name.clone(), span: head.span }.into_diagnostic(),
        };
        Fail::Report(d)
    }

    /// A builtin name of a flow body at the head of `segs` (§2.2, §11.4):
    /// the callee of a delay or of `sample_rate()`, which the flow stage
    /// reads; anywhere else, not found (S-720, the one place of its error).
    fn flow_builtin(&self, b: FlowBuiltin, segs: &[&Ident], place: Place) -> (Vec<PathRes>, Option<Fail>) {
        let called = match place {
            Place::Instance => true,
            Place::Callee => segs.len() == 1 && b != FlowBuiltin::SampleTick,
            Place::Value | Place::Const => false,
        };
        let fail = (!called).then(|| self.not_found(segs, place));
        (vec![PathRes::FlowBuiltin(b)], fail)
    }

    /// E0308 for a `.` after a name that is neither a value nor a namespace
    /// (a trait, a kind constraint; §15.1, S-713 (e)), with no candidate.
    fn no_namespace(&self, segs: &[&Ident]) -> Diagnostic {
        let (name, member) = (segs[segs.len() - 2], segs[segs.len() - 1]);
        let span = span_of(segs);
        let msg = format!("`{}` is a trait or a kind constraint, which has no members (§15.1)", name.name);
        Diagnostic::new(Stage::Names, Code::E0308, span, msg).with_found(self.src(span)).with_note(
            name.span,
            format!(
                "a method is called on a value (`x.{}()`), and an associated function or constant is named after \
                 a type (`F32.from_bits(b)`, §6.6)",
                member.name
            ),
        )
    }

    /// The type or const parameter `name` of the heading.
    fn heading(&self, name: &str) -> Option<PathRes> {
        let (i, g) = (0..).zip(self.generics).find(|(_, g)| g.name == name)?;
        match g.kind {
            GenericKind::Type { .. } => Some(PathRes::TypeParam(i)),
            GenericKind::Const(_) => Some(PathRes::ConstParam(i)),
            GenericKind::Effect => None,
        }
    }

    /// An associated item `name` of the builtin type `of`: at the place of a
    /// value, a constant of the compiler's table (`F32.PI`); as the name of
    /// the method of a call, any (the types stage reads the associated
    /// function, `Buf.zeroed`, and reports one that is none).
    fn builtin_assoc(&self, of: Entity, name: &Ident, method: bool) -> Option<PathRes> {
        let a = self.a;
        let ty = match of {
            Entity::Builtin(Builtin::Scalar(t)) => {
                (method || builtin::has_assoc_const(&a.types, t, &name.name)).then_some(t)
            }
            Entity::Builtin(Builtin::Generic(g)) if method => a.builtin_key.get(&g).copied(),
            _ => None,
        }?;
        Some(PathRes::BuiltinAssoc { ty, name: name.name.clone() })
    }

    /// The chain of names `e` ends (`a.b.c` is `Field(Field(Path(a), b), c)`),
    /// from its head, with the node of each; none when its head is no name
    /// (`f().x`).
    pub(super) fn chain(&self, e: ExprId) -> Option<Vec<(ExprId, &'a Ident)>> {
        let ast = self.ast;
        let mut out = Vec::new();
        let mut cur = e;
        loop {
            match &ast.expr(cur).kind {
                ExprKind::Field { base, name } => {
                    out.push((cur, name));
                    cur = *base;
                }
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    out.push((cur, &p.segments[0]));
                    out.reverse();
                    return Some(out);
                }
                _ => return None,
            }
        }
    }

    /// The item a path of a pattern or a struct literal names, of the names
    /// of the module (as a type is named).
    fn item(&self, path: &Path) -> Result<Entity, Fail> {
        let a = self.a;
        let names = (&a.prelude, &a.defs[..], &a.builtin_key);
        let head = &path.segments[0];
        let error = |err| self.member_error(path, err);
        let Some(first) = a.modules.lookup(self.m, &head.name, &a.prelude) else {
            return Err(error(a.modules.head_error(self.m, path, names)));
        };
        match a.modules.members(first, &path.segments[1..], self.m, names) {
            (_, Some(err)) => Err(error(err)),
            (reached, None) => Ok(reached.last().copied().unwrap_or(first)),
        }
    }

    /// The item the path of the pattern `p` names (§7).
    pub(super) fn ctor(&mut self, p: PatId, path: &Path) -> W {
        let entity = self.item(path).map_err(|f| self.fail(f))?;
        self.out.pats.insert(p, PatRes::Ctor { entity, owner: None });
        Ok(())
    }

    /// The item the path of the struct literal `e` names.
    pub(super) fn struct_lit(&mut self, e: ExprId, path: &Path) -> W {
        let entity = self.item(path).map_err(|f| self.fail(f))?;
        self.out.structs.insert(e, StructRes { entity, owner: None });
        Ok(())
    }
}
