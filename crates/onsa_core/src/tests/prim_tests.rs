//! The table of the operands of the primitives (`prim::sig`, V-02) against
//! the `std` `target` declarations, which are its source: of every primitive
//! a row gives, the number of the operands, their modes and the forms of
//! their types and of the value are those of its declaration, the receiver
//! first (D-15).

use onsa_sema::def::{Bound, FnDef, GenericKind};
use onsa_sema::ty::BuiltinTy;
use onsa_sema::{Analysis, DefKind, Ty, TyId};

use crate::ir::Mode;
use crate::lower::core_mode;
use crate::prim::{FLOATS, INTS, MathFn, Prim, PrimRow, Scalar, Shape, row_self, rows, sig};

/// Every list of at most two type arguments a row reads: a row instantiates
/// at one of them every primitive it has.
fn type_arguments() -> Vec<Vec<Scalar>> {
    let one: Vec<Scalar> =
        INTS.map(Scalar::Int).into_iter().chain(FLOATS.map(Scalar::Float)).chain([Scalar::Other]).collect();
    let pairs = one.iter().flat_map(|&a| one.iter().map(move |&b| vec![a, b]));
    [Vec::new()].into_iter().chain(one.iter().map(|&a| vec![a])).chain(pairs).collect()
}

/// Every primitive: of every row, and the float `%`, which has none.
pub(super) fn every_prim() -> Vec<Prim> {
    let lists = type_arguments();
    let mut out: Vec<Prim> = FLOATS.map(|k| Prim::Math(MathFn::Fmod, k)).into();
    for p in rows().iter().flat_map(|r| lists.iter().filter_map(|l| r.prim.instantiate(l))) {
        if !out.contains(&p) {
            out.push(p);
        }
    }
    out
}

/// A declaration of a row at the type arguments of a use (`args`, the
/// `Self` of a member first, `own` of them, as the row reads them).
struct Decl<'a> {
    a: &'a Analysis,
    f: &'a FnDef,
    args: &'a [Scalar],
    own: usize,
    /// The type parameters of a `Span` or a `Buf` of the declaration: the element `E`.
    elems: Vec<u32>,
    /// A `Span` was met: the first gives `E`, and so its bound.
    spanned: bool,
}

impl Decl<'_> {
    /// The form the table gives the type `t` of the declaration. A type of
    /// `std.test` (`Gen[T]`, a `fn`) and a `Str` or `Bytes` are of none it
    /// reads (`Shape::Any`); the operand of `Len` is wider (`LEN`).
    fn shape(&mut self, t: TyId) -> Shape {
        match self.a.types.get(t) {
            Ty::Int(k) => Shape::Int(*k),
            Ty::Float(k) => Shape::Float(*k),
            Ty::Bool => Shape::Bool,
            Ty::Unit => Shape::Unit,
            Ty::Param(i) if self.elems.contains(i) => Shape::Elem,
            &Ty::Param(i) => match self.args.get(self.own + i as usize) {
                Some(&Scalar::Int(k)) => Shape::Int(k),
                Some(&Scalar::Float(k)) => Shape::Float(k),
                other => panic!("the parameter {i} at {other:?}"),
            },
            Ty::Tuple(ts) if ts.len() == 2 && self.a.types.get(ts[0]) == &Ty::Bool => match self.shape(ts[1]) {
                Shape::Int(k) => Shape::Parts(k),
                other => panic!("a pair of {other:?}"),
            },
            Ty::Builtin(BuiltinTy::Span, ts) => {
                let num = !self.spanned && self.number(ts[0]);
                self.spanned = true;
                if num { Shape::SpanOfNum } else { Shape::SpanOf }
            }
            Ty::Builtin(BuiltinTy::Buf, _) => Shape::BufOf,
            Ty::Named(d, _) if self.a.def(*d).name == "Gen" => Shape::Any,
            Ty::Fn(_) | Ty::Builtin(BuiltinTy::Str | BuiltinTy::Bytes, _) => Shape::Any,
            other => panic!("a type of no form: {other:?}"),
        }
    }

    /// Whether `t` is a type parameter bound to the numbers (`AnyNum`).
    fn number(&self, t: TyId) -> bool {
        let &Ty::Param(i) = self.a.types.get(t) else { return false };
        matches!(&self.f.generics[i as usize].kind, GenericKind::Type { bounds, .. } if bounds.contains(&Bound::AnyNum))
    }
}

/// The type parameters of a `Span` or a `Buf` among `tys`.
fn elements(a: &Analysis, tys: &[TyId]) -> Vec<u32> {
    let of = |t: &TyId| match a.types.get(*t) {
        Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf, ts) => match a.types.get(ts[0]) {
            &Ty::Param(i) => Some(i),
            _ => None,
        },
        _ => None,
    };
    tys.iter().filter_map(of).collect()
}

/// The operand of `Len` is any sequence (lowering's `for` over a `Buf`, an
/// array place it does not fold), wider than the declaration's `Span[T]`.
const LEN: Shape = Shape::Seq;

/// The primitives of a form the table does not read (`Shape::Any`).
fn of_no_form(p: &Prim) -> bool {
    matches!(p, Prim::StrLen | Prim::Pending(_))
}

#[test]
fn every_primitive_has_the_operands_of_its_declaration() {
    let (_, pkg) = super::package("");
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let lists = type_arguments();
    let (mut declarations, mut prims) = (0, 0);
    for (&def, &row) in &a.prims {
        let DefKind::Fn(f) = &a.def(def).kind else { panic!("the row {row:?} of no function") };
        let own = row_self(&a, def);
        // The receiver, then the parameters.
        let operands: Vec<(Mode, TyId)> = f
            .self_mode
            .map(|m| (m, own.expect("a receiver of a member")))
            .into_iter()
            .chain(f.params.iter().map(|p| (p.mode, p.ty)))
            .map(|(m, t)| (core_mode(m), t))
            .collect();
        let mut tys: Vec<TyId> = own.into_iter().chain(operands.iter().map(|o| o.1)).collect();
        tys.push(f.ret);
        declarations += 1;
        // `array.from_fn` is expanded, no primitive.
        if row == PrimRow::FromFn {
            assert!(lists.iter().all(|l| row.instantiate(l).is_none()));
            continue;
        }
        let mut found = 0;
        for l in &lists {
            let Some(p) = row.instantiate(l) else { continue };
            let elems = elements(&a, &tys);
            let mut d = Decl { a: &a, f, args: l, own: usize::from(own.is_some()), elems, spanned: false };
            let mut want: Vec<(Mode, Shape)> = operands.iter().map(|&(m, t)| (m, d.shape(t))).collect();
            let want_ret = d.shape(f.ret);
            if p == Prim::Len {
                want[0].1 = LEN;
            }
            let got = sig(&p);
            assert_eq!((&got.args, got.ret), (&want, want_ret), "the operands and the value of `{}`", p.name());
            let any = want.iter().any(|&(_, s)| s == Shape::Any) || want_ret == Shape::Any;
            assert_eq!(any, of_no_form(&p), "`{}`", p.name());
            found += 1;
        }
        assert!(found > 0, "the row {row:?} gives no primitive");
        prims += found;
    }
    assert_eq!(declarations, rows().len(), "a declaration of every row");
    assert!(prims > declarations, "{prims} primitives");
    // The float `%`, which has no declaration, as the operator is lowered;
    // of the primitives it alone has no row, and it is `rt`.
    for k in FLOATS {
        assert_eq!(sig(&Prim::Math(MathFn::Fmod, k)).args, vec![(Mode::Borrow, Shape::Float(k)); 2]);
    }
    for p in every_prim() {
        let fmod = matches!(p, Prim::Math(MathFn::Fmod, _));
        assert_eq!(p.std_name().is_none(), fmod, "`{}`", p.name());
        assert!(!fmod || p.rt());
    }
}
