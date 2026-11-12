//! W5-18: a continued analysis leaves std's part of the base as it was (a
//! write there would change what std's bodies read, with no sign in the
//! diagnostics of the package unless it uses that part).

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::sync::{Arc, Mutex, OnceLock};

use onsa_diag::FileId;
use onsa_diag::hash::with_seed;
use onsa_diag::internal::InternalBug;

use crate::tests::std_package;
use crate::{Analysis, Base, BaseError, DefId, Module, Package, analyze, analyze_on};

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
    let inner = |t: &onsa_diag::hash::HashMap<String, DefId>| sorted(t.iter());
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
        let module = Module::new(vec!["main".into()], FileId(0), src.to_string(), parsed);
        let a = analyze_on(&Package::new("t", vec![module], vec![std.clone()]), base);
        assert!(a.continues(), "{src}");
        for ((what, was), (_, now)) in expected.iter().zip(std_part(&a, n)) {
            assert!(*was == now, "{what} of std changed by\n{src}");
        }
    }
}

/// The text of `{:?}` with the entries of each table and set in one order: a
/// table lists them in the order of its seed and of how it grew, and a read
/// back one was made another way. `{` is a table when no space follows it,
/// as a struct writes `Name { a: 1 }`. The strings are read whole.
fn canonical(debug: &str) -> String {
    /// Reads the entries to the `}` after `i` and returns the text and the place after it.
    fn table(s: &[u8], mut i: usize) -> (String, usize) {
        let mut entries = vec![String::new()];
        loop {
            let (text, next) = upto_end(s, i);
            entries.last_mut().unwrap().push_str(&text);
            i = next;
            match s.get(i) {
                Some(b',') => {
                    entries.push(String::new());
                    i += 2;
                }
                _ => break,
            }
        }
        entries.sort();
        (format!("{{{}}}", entries.join(", ")), i + 1)
    }
    /// Copies what is at depth 0 from `i` to a `,` or a closing bracket,
    /// whichever is first, the tables inside in order.
    fn upto_end(s: &[u8], mut i: usize) -> (String, usize) {
        let mut out = Vec::new();
        let mut depth = 0;
        while let Some(&c) = s.get(i) {
            match c {
                b'"' => {
                    let start = i;
                    i += 1;
                    while s[i] != b'"' {
                        i += if s[i] == b'\\' { 2 } else { 1 };
                    }
                    i += 1;
                    out.extend_from_slice(&s[start..i]);
                    continue;
                }
                b'\'' if s.get(i + 2) == Some(&b'\'') => {
                    out.extend_from_slice(&s[i..i + 3]);
                    i += 3;
                    continue;
                }
                b'{' if s.get(i + 1) != Some(&b' ') => {
                    let (text, next) = table(s, i + 1);
                    out.extend_from_slice(text.as_bytes());
                    i = next;
                    continue;
                }
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' if depth == 0 => break,
                b')' | b']' | b'}' => depth -= 1,
                b',' if depth == 0 => break,
                _ => {}
            }
            out.push(c);
            i += 1;
        }
        (String::from_utf8(out).expect("cut at ASCII"), i)
    }
    let s = debug.as_bytes();
    let (text, end) = upto_end(s, 0);
    assert_eq!(end, s.len(), "the text of `{{:?}}` ends at its one value");
    text
}

/// The first place the two texts part, with what is around it.
fn parting(a: &str, b: &str) -> String {
    let at = a.bytes().zip(b.bytes()).take_while(|(x, y)| x == y).count();
    let around =
        |s: &str| String::from_utf8_lossy(&s.as_bytes()[at.saturating_sub(150)..(at + 150).min(s.len())]).to_string();
    format!("at {at} of {} and {}:\n{}\n{}", a.len(), b.len(), around(a), around(b))
}

/// All of a base and of its std, in one order, but the trees, which are not
/// written ([`Module::tree`]): a field of [`onsa_syntax::ParsedAst`] is in it.
fn whole(std: &Package, base: &Base) -> String {
    let modules: Vec<_> = std.modules.iter().map(|m| (&m.segments, m.file, &m.text, &m.parsed)).collect();
    canonical(&format!("{:?}", (std.name.as_str(), std.role, std.deps.len(), modules, &base.analysis)))
}

#[test]
fn canonical_orders_the_tables_and_keeps_the_rest() {
    let a = "S { a: {2: [(1, \"}, \")], 1: {x, y}}, b: {b, a} }";
    let b = "S { a: {1: {y, x}, 2: [(1, \"}, \")]}, b: {a, b} }";
    assert_eq!(canonical(a), canonical(b));
    assert_ne!(canonical("[1, 2]"), canonical("[2, 1]"));
    assert_ne!(canonical("S { a: 1, b: 2 }"), canonical("S { b: 2, a: 1 }"));
    assert_ne!(canonical("{1: 2, 3: 4}"), canonical("{1: 4, 3: 2}"));
}

#[test]
fn a_base_read_back_is_the_base_written() {
    let std = std_package();
    // Written from tables of one seed and read into tables of another.
    let base = with_seed(1, || Base::new(std.clone()));
    let bytes = base.encode().expect("the base writes");
    let (read_std, read) = with_seed(2, || Base::decode(&bytes)).expect("the base reads back");
    assert!(read.usable(), "the base keeps its analysis");
    assert!(read_std.modules.iter().all(|m| m.tree.is_none()), "no tree is read back");
    let (was, now) = (whole(&std, &base), whole(&read_std, &read));
    assert!(was == now, "{}", parting(&was, &now));
}

#[test]
fn the_bytes_of_one_seed_are_one() {
    let std = std_package();
    let write = || with_seed(0, || Base::new(std.clone())).encode().expect("the base writes");
    assert!(write() == write(), "the same bytes from the same seed");
}

#[test]
fn bytes_that_are_no_base_are_an_error() {
    let (_, base) = self::base();
    let bytes = base.lock().unwrap().encode().expect("the base writes");
    for cut in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        assert!(matches!(Base::decode(&bytes[..cut]), Err(BaseError::Format(_))), "cut at {cut}");
    }
    let mut more = bytes.clone();
    more.extend([0, 0, 0]);
    assert!(matches!(Base::decode(&more), Err(BaseError::Trailing(3))));
}

/// The head of the bytes, and the bytes that are a head alone (W5-19).
#[test]
fn the_head_tells_another_compiler_and_no_base() {
    let mark = Base::unusable_bytes().expect("the head writes");
    assert!(matches!(Base::decode(&mark), Err(BaseError::Unusable)));
    let (_, base) = self::base();
    let bytes = base.lock().unwrap().encode().expect("the base writes");
    assert_eq!(bytes[..mark.len()], mark, "a base begins with the head");
    for i in 0..mark.len() {
        // The low bit of a byte of a varint: a head of another value.
        let mut other = bytes.clone();
        other[i] ^= 1;
        assert!(matches!(Base::decode(&other), Err(BaseError::OtherHead)), "byte {i}");
    }
}

#[test]
fn a_package_that_is_not_the_embedded_std_is_not_written() {
    let (std, _) = base();
    let module =
        |text: &str| Module::new(vec!["main".into()], FileId(0), text.to_string(), onsa_syntax::parse(FileId(0), text));
    let other = Base::new(Arc::new(Package::std(vec![module("pub fn f() -> I32 {\n  1\n}\n")])));
    assert!(matches!(other.encode(), Err(BaseError::NotEmbedded)));
    let dep = Base::new(Arc::new(Package::new("t", vec![module("pub fn f() -> I32 {\n  1\n}\n")], vec![std.clone()])));
    assert!(matches!(dep.encode(), Err(BaseError::NotEmbedded)));
}

#[test]
fn a_base_with_no_analysis_is_not_written() {
    let (std, _) = base();
    let unusable = Base { std: std.clone(), analysis: None };
    assert!(matches!(unusable.encode(), Err(BaseError::Unusable)));
}

/// Inputs with a diagnostic of each stage, which a continued analysis reports as a fresh one.
const WRONG: &[&str] = &[
    "pub fn f() -> I32 {\n  1\n",
    "pub fn f() -> I32 {\n  nothing\n}\n",
    "pub fn f() -> I32 {\n  true\n}\n",
    "use std.core.Option.{nothing}\n\npub fn f() -> I32 {\n  1\n}\n",
    "pub struct S {\n  s: S,\n}\n",
    "pub fn f(x: Option[I32]) -> I32 {\n  match x {\n    Some(v) => v,\n  }\n}\n",
    "pub fn f(x: Buf[F32]) -> Buf[F32] {\n  let y = x\n  let z = x\n  z\n}\n",
    "pub flow gain(x: F32 at sample, g: F32 at block) -> F32 at block {\n  x * g\n}\n",
];

/// Inputs that write in std's tables: the analysis falls back to a fresh one,
/// which runs every stage on the std it has, read back or parsed.
const FALLS_BACK: &[&str] = &[
    "impl I32 {\n  pub fn twice(self) -> I32 {\n    self * 2\n  }\n}\n\npub fn f() -> I32 {\n  let x: I32 = 3\n  x.twice()\n}\n",
    "use std.test.{Gen}\n\ntype G = Gen[I32]\n\nimpl G {\n  pub fn n(self) -> I32 {\n    1\n  }\n}\n",
];

#[test]
fn an_analysis_on_a_base_read_back_is_the_fresh_one() {
    // As a base made ahead: of the seed 0, and read with this process's.
    let parsed = std_package();
    let bytes = with_seed(0, || Base::new(parsed.clone())).encode().expect("the base writes");
    let (std, read) = Base::decode(&bytes).expect("the base reads back");
    let read = Mutex::new(read);
    for src in INPUTS.iter().chain(WRONG).chain(FALLS_BACK) {
        let module =
            || Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src));
        let continued = analyze_on(&Package::new("t", vec![module()], vec![std.clone()]), &read);
        assert_eq!(continued.continues(), !FALLS_BACK.contains(src), "the std read back is the base's\n{src}");
        let fresh = analyze(&Package::new("t", vec![module()], vec![parsed.clone()]));
        let on_read = analyze(&Package::new("t", vec![module()], vec![std.clone()]));
        let text = |a: &Analysis| format!("{:?}", (&a.diagnostics, &a.path_diagnostics));
        assert_eq!(text(&continued), text(&fresh), "{src}");
        assert_eq!(text(&on_read), text(&fresh), "{src}");
        let reported = !fresh.diagnostics.is_empty() || !module().parsed.diagnostics.is_empty();
        assert!(reported || !WRONG.contains(src), "no diagnostic of\n{src}");
    }
}

/// `src` as the module of a package on std: with its tree, or without it as a
/// module of a std read back.
fn on_std(src: &str, tree: bool) -> Analysis {
    let mut module = Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src));
    if !tree {
        module.tree = None;
    }
    analyze(&Package::new("t", vec![module], vec![std_package()]))
}

/// A module read back has `@mem` of a `let` on its AST: its E0200 is there
/// without the tree, in a fresh analysis too.
#[test]
fn a_module_without_its_tree_reports_the_storage_attribute() {
    let src = "pub flow g(x: F32 at sample) -> F32 at sample {\n  @mem(bulk) let d = delay~(x, 4800)\n  d\n}\n";
    let text = |a: &Analysis| format!("{:?}", a.diagnostics);
    let with_tree = on_std(src, true);
    assert!(with_tree.diagnostics.iter().any(|d| d.code == onsa_diag::Code::E0200), "{}", text(&with_tree));
    assert_eq!(text(&on_std(src, false)), text(&with_tree));
}

/// The candidate of an `@export` that is not `pub` reads the tree: without it
/// the analysis stops with an internal error at the name, and gives no
/// diagnostic with no candidate.
#[test]
fn a_module_without_its_tree_stops_at_what_reads_the_tree() {
    let src = "@export\nfn f() -> I32 {\n  1\n}\n";
    let with_tree = on_std(src, true);
    assert!(with_tree.diagnostics.iter().any(|d| d.code == onsa_diag::Code::E0303 && !d.fixes.is_empty()));
    let payload = std::panic::catch_unwind(|| on_std(src, false)).expect_err("an internal error");
    let bug = payload.downcast::<InternalBug>().expect("an internal error of the compiler");
    let span = bug.span.expect("at a position");
    assert_eq!(&src[span.start as usize..span.end as usize], "f", "{}", bug.message);
}
