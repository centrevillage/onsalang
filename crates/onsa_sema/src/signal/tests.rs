//! Unit tests of whether a type holds a function type (`signal.rs`, §11.3,
//! S-372): by its structure, the same answer as the note's walk, kept for
//! the package through a type that holds itself, and a note of a few steps.

use super::{fn_in, holds_fn};
use crate::Analysis;
use crate::def::DefKind;
use crate::tests::{check, def};
use crate::ty::{Ty, TyId};

const DECLS: &str = "pub struct Pt { cb: fn(F32) -> F32, k: F32 }\n\
    pub struct Sealed { priv cb: fn(F32) -> F32, k: F32 }\n\
    pub struct Level { k: F32 }\n\
    pub enum Hook { Off, On(fn(F32) -> F32) }\n\
    pub type Shaper = fn(F32) -> F32\n\
    pub struct Box2[T] { a: T, b: T }\n\
    pub struct FA[T] { f: fn(T) -> T }\n";

/// The type the alias `name` names.
fn alias(a: &Analysis, name: &str) -> TyId {
    let DefKind::Alias(ty) = a.def(def(a, name)).kind else { panic!("{name} is no alias") };
    ty
}

/// A function type itself, in an element, an item, a field (`priv` too), a
/// variant, a type argument, an alias, an array of length 0; none in the
/// types of numbers and their aggregates. The note's walk agrees.
#[test]
fn a_function_type_is_found_by_the_structure() {
    let table = [
        (
            true,
            "fn(F32) -> F32 | Pt | Sealed | Hook | Shaper | (F32, fn(F32) -> F32) | [fn(F32) -> F32; 0] | \
                Option[fn(F32) -> F32] | Box2[Pt] | Array[Pt] | FA[I32] | Option[(I32, Box2[Shaper])]",
        ),
        (false, "F32 | Level | (F32, I32) | Option[F32] | Array[Level] | [F32; 4] | Box2[Level] | Str"),
    ];
    let table: Vec<(&str, bool)> =
        table.iter().flat_map(|&(holds, ts)| ts.split('|').map(move |t| (t.trim(), holds))).collect();
    let src: String = table.iter().enumerate().map(|(i, (t, _))| format!("type K{i} = {t}\n")).collect();
    let a = check(&format!("{DECLS}{src}"));
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    for (i, (t, holds)) in table.iter().enumerate() {
        let ty = alias(&a, &format!("K{i}"));
        assert_eq!(holds_fn(&a, ty), *holds, "{t}");
        assert_eq!(holds_fn(&a, ty), *holds, "{t}: asked again");
        assert_eq!(fn_in(&a, ty).is_some(), *holds, "{t}: the note's walk");
    }
}

/// A type that holds itself through an `Array` is answered whichever of a
/// cycle is asked first: `Y` reaches the function of `X` through `X`, which
/// was being entered when `X` was asked; the answers of the question are
/// not kept for `Y` as it found none there. One with none keeps its answer.
#[test]
fn a_cycle_is_answered_whichever_is_asked_first() {
    let src = "pub struct X { a: Y, f: fn(F32) -> F32 }\npub struct Y { b: Array[X] }\n\
        pub struct Z { c: Array[Z], w: W }\npub struct W { z: Array[Z] }\n";
    for first in ["X", "Y"] {
        let mut a = check(src);
        assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
        let [x, y, z, w] = ["X", "Y", "Z", "W"].map(|n| a.types.intern(Ty::Named(def(&a, n), vec![])));
        let order = if first == "X" { [x, y] } else { [y, x] };
        for t in order {
            assert!(holds_fn(&a, t), "{first} first: {}", a.display_type(t));
        }
        assert!(!holds_fn(&a, w) && !holds_fn(&a, z), "{first} first");
        let kept = a.known.summaries.borrow().fns.clone();
        assert_eq!((kept.get(&z), kept.get(&x)), (Some(&false), Some(&true)), "{first} first");
    }
}

/// Of a question that finds a function type, a type found to hold none is
/// kept when it rests on no declaration being entered (`C2`, `Level`), and
/// not when it does: `Z` reaches `X` again only through `Y`, left with a "no"
/// while `X` was being entered. Asked after, each is answered as first.
#[test]
fn a_question_that_finds_one_keeps_the_sure_noes() {
    let src = "pub struct C0 { k: F32 }\npub struct C1 { c: C0 }\npub struct C2 { c: C1 }\n\
        pub struct Level { k: F32 }\n\
        pub struct S { c: C2, l: Level, f: fn(F32) -> F32 }\n\
        pub struct X { a: Y, b: Z, f: fn(F32) -> F32 }\npub struct Y { x: Array[X] }\npub struct Z { y: Y }\n";
    let mut a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let ty = |a: &mut Analysis, n: &str| a.types.intern(Ty::Named(def(a, n), vec![]));
    let [s, c2, level, x, y, z] = ["S", "C2", "Level", "X", "Y", "Z"].map(|n| ty(&mut a, n));
    assert!(holds_fn(&a, s) && holds_fn(&a, x));
    let kept = a.known.summaries.borrow().fns.clone();
    assert_eq!([c2, level, y, z].map(|t| kept.get(&t).copied()), [Some(false), Some(false), None, None]);
    assert!(holds_fn(&a, z) && holds_fn(&a, y) && !holds_fn(&a, c2));
}

/// The note shows the first steps of a long chain and how many more.
#[test]
fn the_path_of_a_note_has_a_limit() {
    let mut src = String::from("pub struct C0 { f: fn(F32) -> F32 }\n");
    for k in 1..=11 {
        src.push_str(&format!("pub struct C{k} {{ c: C{} }}\n", k - 1));
    }
    let mut a = check(&src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let c11 = a.types.intern(Ty::Named(def(&a, "C11"), vec![]));
    let path = fn_in(&a, c11).expect("a function type in C11").path(&a);
    assert!(path.starts_with("the field `c` of `C11`, then the field `c` of `C10`"), "{path}");
    assert!(path.ends_with("the field `c` of `C4`, then 4 more steps"), "{path}");
    let c3 = a.types.intern(Ty::Named(def(&a, "C3"), vec![]));
    let path = fn_in(&a, c3).expect("a function type in C3").path(&a);
    assert!(path.ends_with("the field `c` of `C1`, then the field `f` of `C0`"), "{path}");
}
