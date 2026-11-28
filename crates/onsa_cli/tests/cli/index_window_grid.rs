//! The window of an index (spec §3.5, §5.2; S-1275; W8-03 U3b): a change in the index `i` of `xs[i]` of a place
//! that overlaps the base `xs` is E0702, and one that does not overlap it is no error. The grid moved here from a
//! script of the break side (`grid.py` of W8-03 U3b/b): bases (a local, the fields of a struct and of a tuple, the
//! elements of an array, a path of two fields) in three wrappings (the place itself, a tail of an `if`, a partial
//! view) against changes of the same places and of a root (an `inout` argument, or an assignment in a block).
//! The check runs once on one package of all the functions, in this process, with no file written
//! (`check_input`, X-16).
//!
//! The expected value comes from the places by the rule of §5.2, in this test: two places overlap when they have
//! one root and the steps of one are a prefix of the steps of the other, the indexes of one array overlapping
//! ("同じ配列の添字どうしは…重なるものとして扱う"), the fields of one value not ("異なるフィールドは重ならない").
//! What else each function reports is that none: every function is valid but for its E0702.

use crate::test_support;

use test_support::sweep::*;

const PRE: &str = "pub struct S { a: [U32; 3], b: [U32; 3] }
pub struct H { s: S, n: U32 }
pub fn reset3(inout x: [U32; 3]) -> U32 {
  x = [7, 8, 9]
  1
}
pub fn reset_h(inout x: H) -> U32 {
  x.n = 1
  1
}
";

/// A place: its text, its root and its steps (`[]` an index).
type At = (&'static str, &'static str, &'static [&'static str]);

/// The places of the bases, and of the changes.
const PLACES: [At; 9] = [
    ("a", "a", &[]),
    ("s.a", "s", &["a"]),
    ("s.b", "s", &["b"]),
    ("t.0", "t", &["0"]),
    ("t.1", "t", &["1"]),
    ("g[0]", "g", &["[]"]),
    ("g[1]", "g", &["[]"]),
    ("h.s.a", "h", &["s", "a"]),
    ("h.s.b", "h", &["s", "b"]),
];

/// The wrappings of a base, with `{B}` for it and `{I}` for the index.
const WRAPS: [&str; 3] = ["{B}[{I}]", "(if c { {B} } else { zz })[{I}]", "{B}.slice(0, 2)[{I}]"];

/// Whether the places `p` and `q` overlap (§5.2).
fn overlap(p: &At, q: &At) -> bool {
    let n = p.2.len().min(q.2.len());
    p.1 == q.1 && p.2[..n] == q.2[..n]
}

#[test]
fn a_change_in_an_index_is_e0702_where_it_overlaps_the_base() {
    // The changes: each place, by `inout` or by an assignment in a block in turn, and the root `h` whole.
    let mut changes: Vec<(At, String)> = (PLACES.iter().enumerate())
        .map(|(k, p)| match k % 2 {
            0 => (*p, format!("reset3(inout {})", p.0)),
            _ => (*p, format!("{{ {} = [7, 8, 9]\n    0 }}", p.0)),
        })
        .collect();
    changes.push((("h", "h", &[]), "reset_h(inout h)".to_string()));
    let (mut text, mut heads, mut expected) = (PRE.to_string(), Vec::new(), Vec::new());
    for base in &PLACES {
        for wrap in WRAPS {
            for (at, change) in &changes {
                let n = heads.len();
                heads.push(text.matches('\n').count() + 1);
                expected.push(overlap(base, at));
                let e = wrap.replace("{B}", base.0).replace("{I}", change);
                text.push_str(&format!(
                    "pub fn f{n}(c: Bool, inout a: [U32; 3], inout s: S, inout t: ([U32; 3], [U32; 3]), inout g: [[U32; 3]; 2], inout h: H, zz: [U32; 3]) -> U32 {{\n  {e}\n}}\n"
                ));
            }
        }
    }
    assert_eq!(expected.len(), PLACES.len() * WRAPS.len() * changes.len(), "every case written");
    let c = check_input(&input_of("grid", &Texts::from([("main.onsa".to_string(), text)])));
    assert!(c.code == 0 || c.code == 1, "exit {}: {}", c.code, c.stderr);
    // The function of a line: the last that starts at or before it.
    let mut found = vec![false; expected.len()];
    for d in &c.diags {
        let f = heads.partition_point(|&h| h as u64 <= d.line);
        assert!(f > 0, "a diagnostic before the functions: {} {}", d.code, d.message);
        assert_eq!(d.code, "E0702", "f{}: {}", f - 1, d.message);
        found[f - 1] = true;
    }
    let wrong: Vec<String> = (0..expected.len())
        .filter(|&k| found[k] != expected[k])
        .map(|k| format!("f{k}: E0702 expected {}", expected[k]))
        .collect();
    assert!(expected.iter().any(|&x| x) && expected.iter().any(|&x| !x), "both outcomes are in the grid");
    assert!(wrong.is_empty(), "{} of {}:\n{}", wrong.len(), expected.len(), wrong.join("\n"));
}
