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
//! Seeds: the orders of each program are drawn from `Rng::new(seed)`; the written order and five other
//! orders each (the program with fewer blocks takes fewer). The modules are all six orders. About 110 runs
//! of `onsa`, under a second in a debug build.

mod test_support;

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
        codes: &["E0810", "E0810"],
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

/// §11.6, §15.1: each program, with its declarations in the written order and in five other orders, gives the
/// same check and the same interface.
#[test]
fn programs_that_depended_on_the_order_give_the_same_check_and_interface_in_every_order() {
    let mut problems = Vec::new();
    let mut runs = 0;
    for (i, p) in PROGRAMS.iter().enumerate() {
        let all = orders(p.blocks.len(), 0xD0 + i as u64, 5);
        assert!(all.len() >= 5, "{}: only {} orders", p.name, all.len());
        let mut written: Option<String> = None;
        for order in &all {
            let text: Vec<&str> = order.iter().map(|&k| p.blocks[k]).collect();
            let texts = Texts::from([("m.onsa".to_string(), format!("{}\n{}\n", text.join("\n"), p.tests))]);
            let d = package("decl_order", "demo", &texts);
            let (codes, got) = outcome(d.root(), &[]);
            runs += 1;
            match &written {
                None => {
                    if codes != p.codes {
                        problems.push(format!("{}: the written order gives {codes:?}, want {:?}", p.name, p.codes));
                    }
                    written = Some(got);
                }
                Some(first) if *first != got => {
                    problems.push(format!("{}: the order {order:?} differs from the written order", p.name));
                }
                Some(_) => {}
            }
        }
    }
    assert!(runs >= 40, "{runs} runs");
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
