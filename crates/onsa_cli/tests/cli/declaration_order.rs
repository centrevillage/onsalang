//! The order of the declarations does not change what the tools say (spec §11.6, §15.1, §18.1; R-273, S-710;
//! W4-03 U5a). The sweep moved here from the scripts of the break side (`sweep.py`, `sweepp.py`, `sc1.py` to
//! `sc3.py`, `scp.py`) that found, before U5a, eight programs whose output depended on the order of the
//! declarations (the generated items of a flow, `Out` and `Params` of another flow in a heading, an alias of
//! an alias with a constant length, `process_inplace`), which the gate had passed.
//!
//! What the spec fixes, and so what is checked:
//! - §11.6, §15.1: the items of a flow and the types of a heading are the same whichever declaration is
//!   written first. A module is one set of declarations, and `onsa check --json` and `onsa interface --json`
//!   print the same document for a text and for the same declarations in another order. The positions are
//!   left out (they move with the order), and so is the order of the diagnostics and of the items, which
//!   `diagnostics` fixes by position (§18.1) and `interface` by the source;
//! - §15.1: the modules of a package are the files, so the same modules under other file names (which
//!   change the order the files are read in) print the same, with the file names set back to the logical
//!   names;
//! - what is not asked: the order itself where the spec uses it (E0304, E0305 say which declaration is the
//!   later one, §11.2, §15.1), so no program here has two declarations of one name. The existing case files
//!   are not shuffled: thirteen of them depend on the order for those reasons.
//!
//! Each program is also checked in the order it was written in: the codes it must give (a clean program, or
//! the E0810 of a nested array or of a generated `Out` at the boundary, §11.6), so that a sweep of programs
//! that all end with the same internal error does not pass.
//!
//! The same is asked of a program that has errors (W6-04 U5, U6; R-464, R-462): which diagnostics there are
//! does not depend on the order either, because an error type that a failed declaration leaves is not judged
//! again where it is used (§18.1, "読めなかった部分は誤りの型として扱い、それを使う側には診断を出さない"),
//! and a recursion of `rt` functions is one E0903 for each set of functions that reach each other (§18.1,
//! "互いに辿り合う宣言の集まりごとに一つ"). Two kinds of program are checked apart:
//! - the E0416 of a field and the uses of the type before and after it (`FIELD_ERRORS`), and three programs of
//!   the break side of W5-23 U1 (`m4`, `m5`, `m19`, in `FIELD_ERRORS_OPEN`) whose number of E0416 and whose
//!   E0601 and E0901 changed with the order. For these the whole document is compared (the positions left
//!   out). For `m4`, `m5` and `m19` the spec does not fix which diagnostics stay (whether a use of a type whose
//!   field failed is judged by the other fields, §18.1), so the codes of the written order are not asked, only
//!   that the order changes nothing;
//! - the E0903 of `rt` functions that call each other (`RT_CYCLES`). Where the E0903 is reported is the first call
//!   of the set in the order of the source (§18.1), so the place, and with it the cycle the message names
//!   (§18.1 does not fix the wording), moves with the order. Only the codes are compared, and the codes of the
//!   written order are asked: one for each set.
//!
//! The two kinds are tests of their own (`field_errors_…`, `rt_cycles_…`), apart from the clean programs and from
//! the errors that share nothing (`INDEPENDENT`: the contrast of the two kinds), so that a form that is not through
//! yet does not hide a regression of the others (`tests/README.md`).
//!
//! Seeds: the orders of each program are drawn from `Rng::new(seed)`; the written order and five other
//! orders each (the program with fewer blocks takes fewer). The modules are all six orders. About 110 runs
//! of `onsa`, under a second in a debug build. The programs with errors take the written order and seven
//! other orders (all of them when there are fewer), from the seeds `0xE0 + i` and `0xF0 + i`.

use crate::test_support;

use std::path::Path;

use serde_json::Value;
use test_support::sweep::*;
use test_support::*;

/// A program: the blocks (declarations) that are put in every order, the tests that stay at the end, and
/// the codes the written order gives.
struct Program {
    name: &'static str,
    blocks: &'static [&'static str],
    tests: &'static str,
    codes: &'static [&'static str],
}

const PROGRAMS: [Program; 8] = [
    Program {
        name: "A: an output struct through two aliases and a constant length",
        blocks: &[
            "pub const N: U32 = 2",
            "pub struct St { a: F32, b: [F32; N] }",
            "pub type A = St",
            "pub type B = A",
            "pub flow f(x: F32 at sample) -> B at sample { St { a: x, b: [x, x] } }",
        ],
        tests: "test \"t\" {\n  let xs: [F32; 2] = [1.0, 2.0]\n  let o = f.render(f.Config {}, f.Params {}, xs, 8.0)\n  assert o.a[1] == 2.0\n  assert o.b[1][1] == 2.0\n}",
        codes: &[],
    },
    Program {
        name: "B: a chain of flows through the generated types",
        blocks: &[
            "pub flow f(x: F32 at sample, k: F32 at block) -> F32 at sample { x * k }",
            "pub flow g(c: F32 at init, x: F32 at sample) -> f.Params at sample { f.Params { k: x } }",
            "pub flow h(x: F32 at sample) -> g.Config at sample { g.Config { c: x } }",
        ],
        tests: "test \"t\" {\n  let xs: [F32; 2] = [1.0, 2.0]\n  let o = h.render(h.Config {}, h.Params {}, xs, 8.0)\n  assert o.c[1] == 2.0\n}",
        codes: &[],
    },
    Program {
        name: "C: process_inplace decided by the types of other declarations",
        blocks: &[
            "pub const N: U32 = 2",
            "pub type Samp = F32",
            "pub struct M { y: Samp }",
            "pub struct S2 { l: [F32; N], r: [F32; N] }",
            "pub flow a(x: Samp at sample) -> M at sample { M { y: x } }",
            "pub flow b(x: Samp at sample) -> S2 at sample { S2 { l: [x, x], r: [x, x] } }",
        ],
        tests: "test \"t\" {\n  var st = a.init(a.Config {}, 8.0)\n  var buf: [F32; 2] = [1.0, 2.0]\n  a.process_inplace(inout st, a.Params {}, inout buf)\n  assert buf[0] == 1.0\n}",
        codes: &[],
    },
    Program {
        name: "D: a nested array at the boundary and a generated Out as an input",
        blocks: &[
            "pub struct St { a: F32, b: [[F32; 2]; 2] }",
            "pub flow g(x: F32 at sample) -> St at sample { St { a: x, b: [[x, x], [x, x]] } }",
            "pub flow h(x: g.Out at sample, y: Str at block) -> F32 at sample { 0.0 }",
            "pub flow i(x: F32 at sample) -> g.Config at sample { g.Config {} }",
        ],
        tests: "",
        // `g.Out` as an input of `h` is the E0710 of the types stage (S-772).
        codes: &["E0710", "E0810"],
    },
    Program {
        name: "E: Params of a flow as the output of another and as an input",
        blocks: &[
            "pub struct St { a: F32, b: F32 }",
            "pub flow g(x: F32 at sample, k: F32 at block) -> St at sample { St { a: x, b: k } }",
            "pub flow h(x: F32 at sample, k: F32 at block) -> g.Params at sample { g.Params { k: k } }",
            "pub flow j(x: g.Params at block, y: F32 at sample) -> F32 at sample { y }",
        ],
        tests: "",
        codes: &[],
    },
    Program {
        name: "F: aliases of aliases with arrays and a nested array",
        blocks: &[
            "pub const N: U32 = 3",
            "pub type Row = [F32; N]",
            "pub type Grid = [Row; N]",
            "pub struct R { v: Row }",
            "pub struct G { v: Grid }",
            "pub flow a(x: Row at sample) -> R at sample { R { v: x } }",
            "pub flow b(x: Row at sample) -> G at sample { G { v: [x, x, x] } }",
        ],
        tests: "",
        codes: &["E0810"],
    },
    Program {
        name: "O: an alias of a generated type in the heading of flows",
        blocks: &[
            "pub flow g(x: F32 at sample, k: F32 at block) -> F32 at sample { x * k }",
            "pub type P = g.Params",
            "pub type PP = P",
            "pub flow h(x: F32 at sample) -> PP at sample { g.Params { k: x } }",
            "pub flow j(x: PP at block, y: F32 at sample) -> F32 at sample { y }",
        ],
        tests: "",
        codes: &[],
    },
    Program {
        name: "U: the pairing of process_inplace through a struct declared later and an alias of a length",
        blocks: &[
            "pub const N: U32 = 4",
            "pub type Buf4 = [F32; N]",
            "pub struct Quad { q: Buf4 }",
            "pub flow g(x: Buf4 at sample) -> Quad at sample { Quad { q: x } }",
            "pub flow h(x: [F32; 4] at sample) -> Buf4 at sample { x }",
            "pub flow j(x: [F32; 3] at sample) -> Quad at sample { Quad { q: [x[0], x[1], x[2], 0.0] } }",
        ],
        tests: "test \"t\" {\n  let _ = g.init(g.Config {}, 8.0)\n  let _: [[F32; 4]; 1] = [[0.0; 4]]\n}",
        codes: &[],
    },
];

/// Three modules that read each other's items (`L1` the flow `h` with `g.Params` of `L3`, an alias of `L2`),
/// and the tests of the package. `{lm1}` to `{lm3}` stand for the file names of the modules.
const MODULES: [(&str, &str); 3] = [
    (
        "L1",
        "use {lm2}.{Alias}\nuse {lm3}.{g, Big}\n\npub flow h(x: g.Params at block, y: F32 at sample) -> Alias at sample { Big { v: [y, y] } }\n",
    ),
    ("L2", "use {lm3}.{Big}\n\npub type Alias = Big\n"),
    (
        "L3",
        "pub const N: U32 = 2\n\npub struct Big { v: [F32; N] }\n\npub flow g(x: F32 at sample, k: F32 at block) -> F32 at sample { x * k }\n",
    ),
];
const MAIN: &str = "use {lm1}.{h}\nuse {lm3}.{g}\n\ntest \"t\" {\n  let xs: [F32; 2] = [1.0, 2.0]\n  let o = h.render(h.Config {}, h.Params { x: g.Params { k: 1.0 } }, xs, 8.0)\n  assert o.v[0][1] == 2.0\n}\n";

/// The file names the modules are given, one logical name to each; the order the files sort in is the
/// order the modules are read in.
const FILE_NAMES: [&str; 3] = ["mod_a", "mod_b", "mod_c"];

/// Keys that hold a place in the text, and the arrays that are in the order of the places or of the source.
const PLACES: [&str; 6] = ["span", "file", "line", "col", "end_line", "end_col"];
const UNORDERED: [&str; 3] = ["diagnostics", "items", "modules"];

/// The document without its places, and with the arrays of `UNORDERED` sorted.
fn normal(v: Value) -> Value {
    match v {
        Value::Object(m) => Value::Object(
            m.into_iter()
                .filter(|(k, _)| !PLACES.contains(&k.as_str()))
                .map(|(k, x)| {
                    let mut x = normal(x);
                    if let (true, Value::Array(a)) = (UNORDERED.contains(&k.as_str()), &mut x) {
                        a.sort_by_key(|e| e.to_string());
                    }
                    (k, x)
                })
                .collect(),
        ),
        Value::Array(a) => Value::Array(a.into_iter().map(normal).collect()),
        other => other,
    }
}

/// What `check --json` and `interface --json` print for the package in `root`, in the normal form, with
/// the file names `renames` (file name, logical name) set back. Both end as a check does.
fn outcome(root: &Path, renames: &[(&str, &str)]) -> (Vec<String>, String) {
    let mut text = String::new();
    let mut codes = Vec::new();
    for args in [["check", "--json", "."], ["interface", "--json", "."]] {
        let out = run(root, &args);
        assert!(out.code == 0 || out.code == 1, "onsa {args:?}: exit {} {}", out.code, out.stderr);
        assert!(!out.stderr.contains("internal error"), "onsa {args:?}: {}", out.stderr);
        let mut stdout = out.stdout.clone();
        for (file, logical) in renames {
            stdout = stdout.replace(file, logical);
        }
        let doc: Value = serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("onsa {args:?}: not JSON ({e})"));
        if args[0] == "check" {
            for d in doc["diagnostics"].as_array().expect("diagnostics") {
                codes.push(d["code"].as_str().expect("a code").to_string());
            }
        }
        text.push_str(&format!("{} {}\n{}\n", args[0], out.code, normal(doc)));
    }
    codes.sort();
    (codes, text)
}

/// The written order, and `want` other orders of `n` blocks drawn from the seed (all different).
fn orders(n: usize, seed: u64, want: usize) -> Vec<Vec<usize>> {
    let mut rng = Rng::new(seed);
    let written: Vec<usize> = (0..n).collect();
    let mut all = vec![written.clone()];
    for _ in 0..200 {
        if all.len() > want {
            break;
        }
        let mut p = written.clone();
        rng.shuffle(&mut p);
        if !all.contains(&p) {
            all.push(p);
        }
    }
    all
}

/// The written order of the blocks, and then `want` other orders drawn from the seed (all of them when the
/// program has so few blocks that there are no more), each given to `onsa` as one module. `codes` are the codes
/// the written order must give (`None` when only the sameness is asked), and `text` says that the whole document
/// is asked to be the same in every order (and not the codes only). Returns the number of orders run.
#[allow(clippy::too_many_arguments)]
fn sweep_orders(
    name: &str,
    blocks: &[&str],
    tests: &str,
    codes: Option<&[&str]>,
    text: bool,
    seed: u64,
    want: usize,
    problems: &mut Vec<String>,
) -> usize {
    let all = orders(blocks.len(), seed, want);
    let few = (1..=blocks.len()).product::<usize>().min(want + 1);
    assert!(all.len() >= few, "{name}: only {} orders of {few}", all.len());
    let mut written: Option<(Vec<String>, String)> = None;
    for order in &all {
        let joined: Vec<&str> = order.iter().map(|&k| blocks[k]).collect();
        let texts = Texts::from([("m.onsa".to_string(), format!("{}\n{}\n", joined.join("\n"), tests))]);
        let d = package("decl_order", "demo", &texts);
        let (got_codes, got) = outcome(d.root(), &[]);
        match &written {
            None => {
                if let Some(want_codes) = codes
                    && got_codes != want_codes
                {
                    problems.push(format!("{name}: the written order gives {got_codes:?}, want {want_codes:?}"));
                }
                written = Some((got_codes, got));
            }
            Some((first_codes, first)) => {
                let same = if text { *first == got } else { *first_codes == got_codes };
                if !same {
                    let heads: Vec<&str> = joined.iter().map(|b| b.lines().next().unwrap_or("")).collect();
                    problems.push(format!(
                        "{name}: the order {order:?} gives {got_codes:?}, the written order {first_codes:?} ({})",
                        heads.join(" | ")
                    ));
                }
            }
        }
    }
    all.len()
}

/// §11.6, §15.1: each program, with its declarations in the written order and in five other orders, gives the
/// same check and the same interface.
#[test]
fn programs_that_depended_on_the_order_give_the_same_check_and_interface_in_every_order() {
    let mut problems = Vec::new();
    let mut runs = 0;
    for (i, p) in PROGRAMS.iter().enumerate() {
        runs += sweep_orders(p.name, p.blocks, p.tests, Some(p.codes), true, 0xD0 + i as u64, 5, &mut problems);
    }
    assert!(runs >= 40, "{runs} runs");
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
}

/// A program with errors: the blocks that are put in every order, the codes the written order gives (`None`
/// when the spec does not fix them) and whether the whole document is asked to be the same.
struct Failing {
    name: &'static str,
    blocks: &'static [&'static str],
    codes: Option<&'static [&'static str]>,
    text: bool,
}

/// R-464 (W6-04 U5), §18.1, §4.5: a field that is an E0416 makes the field an error type, and the uses of the
/// type, written before or after it, give no diagnostic of their own. The type with the failed field is
/// `S3[T1: ?Dup] { w: Array[T1] }` (the elements of `Array` are `Dup`) or `B[T1] { w: Buf[T1] }` (the elements
/// of `Buf` are `Copy`), and the users ask `Copy` of it (`OC[T: Copy]`) in a field, in a variant and in a
/// signature.
const FIELD_ERRORS: [Failing; 9] = [
    Failing {
        name: "R-464 a: a struct, a signature and a struct that use the type of the failed field",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub fn g(x: OC[S3[F32]]) -> I32 { 0 }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub struct H { h: OC[S3[F32]] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 b: two structs and an enum that use the type of the failed field",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct H1 { h: OC[S3[F32]] }",
            "pub enum E { V(OC[S3[F32]]) }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub struct H2 { h: OC[S3[F32]] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 c: a struct with a Buf of a type that is not Copy, and its user",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct B[T1] { w: Buf[T1] }",
            "pub struct H { h: OC[B[F32]] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 d: a user that asks nothing of the type, and one that asks Copy",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct K { k: S3[F32] }",
            "pub struct S3[T1: ?Dup] { w: Array[T1], a: I32 }",
            "pub struct H { h: OC[S3[F32]] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 e: an alias of the type of the failed field, and its user",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub type AS = S3[F32]",
            "pub struct HS { h: OC[AS] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 f: the `Config` of a flow whose input is the type of the failed field",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub flow fa(x: F32 at sample, k: S3[F32] at init) -> F32 at sample { x }",
            "pub struct HQ { p: OC[fa.Config] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 g: the `Config` of a flow whose input is an alias in error",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub type AE = Array[Buf[F32]]",
            "pub flow fa(x: F32 at sample, k: AE at init) -> F32 at sample { x }",
            "pub struct HQ { p: OC[fa.Config] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 h: a flow whose input is the `Config` of such a flow",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub flow fb(x: F32 at sample, k: fa.Config at init) -> F32 at sample { x }",
            "pub flow fa(x: F32 at sample, k: S3[F32] at init) -> F32 at sample { x }",
            "pub struct HQ { p: OC[fb.Config] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-464 i: an `impl` of a user of the type of the failed field",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub struct H1 { h: OC[S3[F32]] }",
            "impl H1 {\n  fn m2(self) -> I32 { 0 }\n}",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
];

/// What does not depend on the order today, as the contrast of the two above (a form that fails is not mixed with
/// these, so that a regression of them shows): `H` is an E0416 of its own where the type has no error (`S3[T1]`
/// with `T1: Dup`, so `S3[F32]` is not `Copy`), and each cycle of `rt` functions that is a set of its own is one
/// E0903 (the codes only, as in `RT_CYCLES`).
const INDEPENDENT: [Failing; 3] = [
    Failing {
        name: "R-464 contrast: a type without an error is judged where it is used",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1] { a: I32, w: Array[T1] }",
            "pub struct H { h: OC[S3[F32]] }",
        ],
        codes: Some(&["E0416"]),
        text: true,
    },
    Failing {
        name: "R-462 contrast: two cycles that are sets of their own",
        blocks: &["pub rt fn a() { b() }", "pub rt fn b() { a() }", "pub rt fn x() { y() }", "pub rt fn y() { x() }"],
        codes: Some(&["E0903", "E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 contrast: two functions that call themselves and a caller of both",
        blocks: &["pub rt fn a() { a() }", "pub rt fn b() { b() }", "pub rt fn c() {\n  a()\n  b()\n}"],
        codes: Some(&["E0903", "E0903"]),
        text: false,
    },
];

/// The programs `m4`, `m5` and `m19` of the break side of W5-23 U1 (the number of E0416, and the E0601 and
/// E0901, changed with the order): which diagnostics stay is not fixed by the spec (whether the use of a type
/// whose field failed is judged by the other fields, §18.1), so only the sameness is asked.
const FIELD_ERRORS_OPEN: [Failing; 3] = [
    Failing {
        name: "W5-23 U1 m4: a failed type argument, an enum and an rt signature that use the type",
        blocks: &[
            "pub struct S0[T0: ?Dup, T1: Copy] { f0: Array[F32] }",
            "pub struct S1[T0: Copy] { f0: (T0, Str), f2: S0[F32, S0[F32, F32]] }",
            "pub enum S2 { V0(S1[Bytes]) }",
            "pub rt fn p0_0(move x: S1[S1[I32]]) -> I32 { 0 }",
        ],
        codes: None,
        text: true,
    },
    Failing {
        name: "W5-23 U1 m5: the same with an alias of a failed type in the place of the enum",
        blocks: &[
            "pub struct S0[T0: ?Dup, T1: Copy] { f0: Array[F32] }",
            "pub struct S1[T0: Copy] { f0: (T0, Str), f2: S0[F32, S0[F32, F32]] }",
            "pub type S4 = S0[S1[Str], F32]",
            "pub rt fn p0_0(move x: S1[S1[I32]]) -> I32 { 0 }",
        ],
        codes: None,
        text: true,
    },
    Failing {
        name: "W5-23 U1 m19: a struct, signatures, two rt signatures and a move twice of the failed type",
        blocks: &[
            "pub struct OC[T: Copy] { t: T }",
            "pub struct S3[T1: ?Dup] { a: I32, w: Array[T1] }",
            "pub struct H { h: OC[S3[F32]] }",
            "pub fn g(x: OC[S3[F32]]) -> I32 { 0 }",
            "pub fn k(move x: S3[Buf[F32]]) -> (S3[Buf[F32]], S3[Buf[F32]]) { (move x, move x) }",
            "pub rt fn r(move x: S3[F32]) -> I32 { 0 }",
            "pub rt fn r2(move x: S3[F32]) -> S3[F32] { x }",
        ],
        codes: None,
        text: true,
    },
];

/// R-462 (W6-04 U6), §10 rule 5, §18.1: `rt` functions that call each other by name are one E0903 for each set of
/// functions that reach each other, whatever the order of the declarations.
const RT_CYCLES: [Failing; 6] = [
    Failing {
        name: "R-462 a: two cycles that share a function",
        blocks: &["pub rt fn a() {\n  b()\n  c()\n}", "pub rt fn b() { a() }", "pub rt fn c() { a() }"],
        codes: Some(&["E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 b: three cycles that share a function",
        blocks: &[
            "pub rt fn a() {\n  b()\n  c()\n  d()\n}",
            "pub rt fn b() { a() }",
            "pub rt fn c() { a() }",
            "pub rt fn d() { a() }",
        ],
        codes: Some(&["E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 c: a function that calls itself and one that it makes a cycle with",
        blocks: &["pub rt fn a() {\n  a()\n  b()\n}", "pub rt fn b() { a() }"],
        codes: Some(&["E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 d: two sets that do not reach each other, two cycles in each",
        blocks: &[
            "pub rt fn a() {\n  b()\n  c()\n}",
            "pub rt fn b() { a() }",
            "pub rt fn c() { a() }",
            "pub rt fn x() {\n  y()\n  z()\n}",
            "pub rt fn y() { x() }",
            "pub rt fn z() { x() }",
        ],
        codes: Some(&["E0903", "E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 e: a cycle with a chord",
        blocks: &[
            "pub rt fn a() { b() }",
            "pub rt fn b() { c() }",
            "pub rt fn c() {\n  d()\n  a()\n}",
            "pub rt fn d() { a() }",
        ],
        codes: Some(&["E0903"]),
        text: false,
    },
    Failing {
        name: "R-462 f: a function outside the set that calls into it",
        blocks: &[
            "pub rt fn outer() { a() }",
            "pub rt fn a() {\n  b()\n  c()\n}",
            "pub rt fn b() { a() }",
            "pub rt fn c() { a() }",
        ],
        codes: Some(&["E0903"]),
        text: false,
    },
];

/// Every program of `programs` in the written order and in seven other orders, from the seeds `seed + i`.
fn sweep_failing(programs: &[&Failing], seed: u64) -> (usize, Vec<String>) {
    let mut problems = Vec::new();
    let mut runs = 0;
    for (i, p) in programs.iter().enumerate() {
        runs += sweep_orders(p.name, p.blocks, "", p.codes, p.text, seed + i as u64, 7, &mut problems);
    }
    (runs, problems)
}

/// R-464, R-462, §18.1: the errors that do not share a declaration with another error are the same in every
/// order (`INDEPENDENT`).
#[test]
fn errors_that_are_not_shared_give_the_same_codes_in_every_order() {
    let programs: Vec<&Failing> = INDEPENDENT.iter().collect();
    let (runs, problems) = sweep_failing(&programs, 0xE8);
    assert!(runs >= 15, "{runs} runs");
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
}

/// R-464 (W6-04 U5), §18.1, §4.5: the diagnostics of a type with a failed field and of its uses are the same in
/// every order of the declarations, and in the written order they are the one E0416 of the field.
#[test]
fn field_errors_give_the_same_diagnostics_in_every_order() {
    let programs: Vec<&Failing> = FIELD_ERRORS.iter().chain(FIELD_ERRORS_OPEN.iter()).collect();
    let (runs, problems) = sweep_failing(&programs, 0xE0);
    assert!(runs >= 40, "{runs} runs");
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
}

/// R-462 (W6-04 U6), §10 rule 5, §18.1: the E0903 of `rt` functions that call each other is one for each set of
/// functions that reach each other, in every order of the declarations.
#[test]
fn rt_cycles_give_one_e0903_for_each_set_in_every_order() {
    let programs: Vec<&Failing> = RT_CYCLES.iter().collect();
    let (runs, problems) = sweep_failing(&programs, 0xF0);
    assert!(runs >= 30, "{runs} runs");
    assert!(problems.is_empty(), "{} problems:\n{}", problems.len(), problems.join("\n"));
}

/// §15.1: three modules that use each other's items give the same check and the same interface under every
/// assignment of the file names, which changes the order the files are read in.
#[test]
fn modules_that_use_each_others_items_give_the_same_output_under_every_file_naming() {
    let mut names: Vec<[usize; 3]> = Vec::new();
    for a in 0..3 {
        for b in 0..3 {
            for c in 0..3 {
                if a != b && b != c && a != c {
                    names.push([a, b, c]);
                }
            }
        }
    }
    assert_eq!(names.len(), 6);
    let mut first: Option<(Vec<String>, String)> = None;
    for perm in names {
        let file = |k: usize| FILE_NAMES[perm[k]];
        let fill = |t: &str| t.replace("{lm1}", file(0)).replace("{lm2}", file(1)).replace("{lm3}", file(2));
        let mut texts = Texts::new();
        for (k, (_, text)) in MODULES.iter().enumerate() {
            texts.insert(format!("{}.onsa", file(k)), fill(text));
        }
        texts.insert("main.onsa".to_string(), fill(MAIN));
        let d = package("decl_order_modules", "demo", &texts);
        let renames: Vec<(&str, &str)> = (0..3).map(|k| (file(k), MODULES[k].0)).collect();
        let got = outcome(d.root(), &renames);
        match &first {
            None => {
                assert!(got.0.is_empty(), "the package is clean in the first naming: {:?}", got.0);
                first = Some(got);
            }
            Some(f) => assert_eq!(f.1, got.1, "the file naming {perm:?} differs from the first"),
        }
    }
}
