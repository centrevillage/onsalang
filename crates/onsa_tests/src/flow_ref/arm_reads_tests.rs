//! The reads of the bindings of arms on the evaluator (W7-17 L5/e; §11.3, S-1247 (1), S-1197, §11.10): the table of values worked out by hand (`arm_reads_values.md`, the forms that the `case` files cannot hold: the guard of a
//! plain `match` is E0200 in this version), and the twins: a `match` on an event, wrapped in conditions at `sample` that are true or false at the events, gives at each frame the value of the `match` that is not wrapped
//! where the conditions hold and `x` where they do not (§11.3: "外の条件によらず"), whatever the body (a field, an element of a tuple, a `match` on a field of the binding). The outputs of the bodies not wrapped are by hand.

use super::expr_tests::{def_named, with_checked};
use super::flow::{Call, Instance, Outcome};
use super::par_arm_tests::report;
use super::sema_view::View;
use super::value::{IntKind, Value};

const TABLE: &str = include_str!("arm_reads_values.md");

#[test]
fn the_guards_the_pars_and_the_resets_of_the_reads_of_arm_bindings_run_with_the_values_written_by_hand() {
    let (passed, stopped, failed) = report(TABLE, &|_| true);
    assert!(failed.is_empty(), "{failed:#?}");
    assert!(stopped.is_empty(), "{stopped:#?}");
    assert_eq!(passed.len(), 6, "{passed:?}");
}

const PARTS: &str = "struct Pd2 { w: U32 }
enum W { N, S(Pd2) }
impl Default for W { rt fn default() -> W { W.N } }
struct Pd { vel: U32, k: W }
enum V { A, B(Pd) }
impl Default for V { rt fn default() -> V { V.B(Pd { vel: 50, k: W.S(Pd2 { w: 7 }) }) } }
flow src(y: U32 at sample) -> V at event {
  if y > 100 { Some(V.A) } else if y > 0 { Some(V.B(Pd { vel: y, k: if y % 2 == 0 { W.S(Pd2 { w: y * 2 }) } else { W.N } })) } else { None }
}
enum Tp { N, P((U32, U32)) }
impl Default for Tp { rt fn default() -> Tp { Tp.P((70, 80)) } }
flow srct(y: U32 at sample) -> Tp at event { if y > 0 { Some(Tp.P((y, y * 2))) } else { None } }
";

/// The bodies of the twins: the `match` (the event is `v`) and the outputs of it not wrapped, from the events `Y` (frame 2: `V.B(vel 3, k: W.N)`, 4: `V.B(2, W.S(4))`, 5: `V.A`, 6: `V.B(4, W.S(8))`; for the tuple the events `(y, 2y)` of the same `y`).
/// The field reads of the bindings are `U32.default()` (0) or `W.default()` (`W.N`) before the first event, not the fields of `V.default()` (50, `W.S(7)`) or `Tp.default()` (70, 80).
const BODIES: [(&str, &str, [i128; 8]); 4] = [
    ("src", "match v { V.B(q) => x + q.vel, V.A => x }", [1000, 1000, 1003, 1003, 1002, 1000, 1004, 1004]),
    (
        "src",
        "match v { V.B(q) => match q.k { W.S(r) => x + r.w, W.N => x }, V.A => x }",
        [1000, 1000, 1000, 1000, 1004, 1000, 1008, 1008],
    ),
    (
        "src",
        "match v { V.B(q) => match q { Pd { k: W.S(r), _ } => x + r.w, _ => x }, V.A => x }",
        [1000, 1000, 1000, 1000, 1004, 1000, 1008, 1008],
    ),
    ("srct", "match v { Tp.P(t) => x + t.0 + t.1, Tp.N => x }", [1000, 1000, 1009, 1009, 1006, 1006, 1012, 1012]),
];

const Y: [i128; 8] = [0, 0, 3, 0, 2, 101, 4, 0];
/// For the tuple, the same `y` without the `V.A` (101 would be an event `(101, 202)`): 0 at the frame 5.
const YT: [i128; 8] = [0, 0, 3, 0, 2, 0, 4, 0];

/// The wraps: how a body is written, and at which frames the conditions hold, for the values of `c` (0, 1, 2 at the frames of `C`).
const C: [i128; 8] = [1, 1, 0, 1, 2, 1, 1, 1];
type Wrap = (&'static str, fn(&str) -> String, fn(i128) -> bool);
const WRAPS: [Wrap; 4] = [
    ("not wrapped", |m| m.to_string(), |_| true),
    ("one condition", |m| format!("if c != 0 {{ {m} }} else {{ x }}"), |c| c != 0),
    (
        "two conditions",
        |m| format!("if c != 0 {{ if c != 2 {{ {m} }} else {{ x }} }} else {{ x }}"),
        |c| c != 0 && c != 2,
    ),
    ("a let", |m| format!("let z = {m}\nif c != 0 {{ z }} else {{ x }}"), |c| c != 0),
];

fn outputs(src: &str, columns: Vec<(&'static str, [i128; 8])>) -> Vec<i128> {
    with_checked(src, true, move |a| {
        let cols: Vec<(&str, Vec<Value>)> =
            columns.iter().map(|(n, v)| (*n, v.iter().map(|k| Value::int(IntKind::U32, *k)).collect())).collect();
        let ins: Vec<(&str, &[Value])> = cols.iter().map(|(n, v)| (*n, v.as_slice())).collect();
        match Instance::render(
            View::new(a),
            def_named(a, "top"),
            8.0,
            &Call { inputs: &ins, ..Default::default() },
            None,
        ) {
            Ok(Outcome::Ok(outs)) => outs.iter().map(|v| if let Value::Int(_, n, _) = v { *n } else { -1 }).collect(),
            Ok(Outcome::Panic { at, stop }) => panic!("panic {at:?} {:?}", stop.fault),
            Err(stop) => panic!("{:?}", stop.fault),
        }
    })
}

#[test]
fn a_match_on_an_event_wrapped_in_conditions_at_sample_gives_the_value_where_the_conditions_hold_whatever_the_event_did_where_they_did_not()
 {
    for (source, m, bare) in BODIES {
        for (what, wrap, holds) in WRAPS {
            let src = format!(
                "{PARTS}flow top(x: U32 at sample, y: U32 at sample, c: U32 at sample) -> U32 at sample {{\n  let v = {source}~(y)\n  {}\n}}\n",
                wrap(m)
            );
            let y = if source == "srct" { YT } else { Y };
            let got = outputs(&src, vec![("x", [1000; 8]), ("y", y), ("c", C)]);
            let want: Vec<i128> = (0..8).map(|i| if holds(C[i]) { bare[i] } else { 1000 }).collect();
            assert_eq!(got, want, "{what}: {m}");
        }
    }
}
