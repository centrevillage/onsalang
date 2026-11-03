//! W5-18: a continued analysis leaves std's part of the base as it was (a
//! write there would change what std's bodies read, with no sign in the
//! diagnostics of the package unless it uses that part).

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::sync::{Arc, Mutex, OnceLock};

use onsa_diag::FileId;

use crate::flow_tests::std_package;
use crate::{Analysis, Base, DefId, Module, Package, analyze_on};

/// std and its base, made once for the tests of the crate.
fn base() -> &'static (Arc<Package>, Mutex<Base>) {
    static BASE: OnceLock<(Arc<Package>, Mutex<Base>)> = OnceLock::new();
    BASE.get_or_init(|| {
        let std = std_package();
        (std.clone(), Mutex::new(Base::new(std)))
    })
}

/// The entries of a table, in the order of their keys, as text.
fn sorted<K: Debug, V: Debug>(entries: impl Iterator<Item = (K, V)>) -> String {
    let map: BTreeMap<String, String> = entries.map(|(k, v)| (format!("{k:?}"), format!("{v:?}"))).collect();
    format!("{map:?}")
}

/// The base's part of `a`, whose first `n` defs, `t` types and `m`
/// modules are the base's: what the stages of std made, each table of its keys.
fn std_part(a: &Analysis, n: (usize, usize, usize)) -> Vec<(&'static str, String)> {
    let std = |d: &DefId| (d.0 as usize) < n.0;
    let inner = |t: &std::collections::HashMap<String, DefId>| sorted(t.iter());
    vec![
        ("defs", format!("{:?}", &a.defs[..n.0])),
        ("types", format!("{:?}", (0..n.1 as u32).map(|i| a.types.get(crate::TyId(i))).collect::<Vec<_>>())),
        ("modules.mods", format!("{:?}", &a.modules.mods[..n.2])),
        ("prims", sorted(a.prims.iter())),
        ("const_values", sorted(a.const_values.iter().filter(|e| std(e.0)))),
        ("bodies", sorted(a.bodies.iter().filter(|e| std(e.0)))),
        ("names", sorted(a.names.iter().filter(|e| std(e.0)))),
        ("assoc", sorted(a.modules.assoc.iter().filter(|e| std(e.0)).map(|(k, t)| (k, inner(t))))),
        ("assoc_builtin", sorted(a.modules.assoc_builtin.iter().map(|(k, t)| (k, inner(t))))),
        ("decls.heads", sorted(a.decls.heads.iter().filter(|e| std(e.0)))),
    ]
}

/// Packages that continue the base and read std in each stage.
const INPUTS: &[&str] = &[
    "pub fn f() -> I32 {\n  1\n}\n",
    "pub flow gain(x: F32 at sample, g: F32 at block) -> F32 at sample {\n  let y = prev~(x)\n  (x + y) * g\n}\n",
    "use std.test.{Gen}\n\npub struct S {\n  g: Gen[S],\n}\n\npub struct T {\n  t: Option[T],\n}\n",
    "pub const small: I32 = 1\n\npub fn f() -> I32 {\n  small + I32.MAX\n}\n",
    "use std.core.Result.{map_err}\n\npub fn f() -> I32 {\n  1\n}\n",
    "pub struct Show {\n  x: I32,\n}\n\npub fn panic() -> I32 {\n  1\n}\n",
    "pub const TAU: F32 = F32.PI * 2.0\n\npub fn f() -> F32 {\n  TAU + F32.EPSILON\n}\n",
    "use std.math.{sqrt}\n\npub fn f(x: F32) -> F32 {\n  let r: Result[F32, I32] = Ok(sqrt(x))\n  match r {\n    Ok(v) => v,\n    Err(_) => 0.0,\n  }\n}\n",
    "pub fn f(n: U32) -> U32 {\n  let b: Buf[F32] = Buf.zeroed(n)\n  let s: Str = \"ab\"\n  b.len() + s.len()\n}\n",
];

#[test]
fn a_continued_analysis_leaves_std_part_of_the_base() {
    let (std, base) = base();
    let guard = base.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let before = guard.analysis.as_ref().expect("std alone has no diagnostic");
    let n = (before.defs.len(), before.types.len(), before.modules.mods.len());
    assert!(n.0 > 0 && n.1 > 0 && n.2 > 0, "the base has std's defs, types and modules");
    let expected = std_part(before, n);
    drop(guard);
    for src in INPUTS {
        let parsed = onsa_syntax::parse(FileId(0), src);
        let module = Module { segments: vec!["main".into()], file: FileId(0), text: src.to_string(), parsed };
        let a = analyze_on(&Package::new("t", vec![module], vec![std.clone()]), base);
        assert!(a.continues(), "{src}");
        for ((what, was), (_, now)) in expected.iter().zip(std_part(&a, n)) {
            assert!(*was == now, "{what} of std changed by\n{src}");
        }
    }
}
