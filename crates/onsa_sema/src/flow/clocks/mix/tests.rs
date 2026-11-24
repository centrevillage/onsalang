//! The four places of an event value with no `at` and a periodic value
//! (§11.11, S-563): the places, what the value is followed through and what
//! stops it, and the candidates of a delay. The tables are of the letter.

use crate::tests::check;
use onsa_diag::Code;

const HEAD: &str = "pub struct Bent: Default {
  note: F32,
  vel: F32,
}
pub rt fn half(v: F32) -> F32 { v * 0.5 }
pub enum Mode {
  Off,
  On,
}
pub rt fn pick(m: Mode, x: F32) -> F32 {
  match m {
    Mode.Off => 0.0,
    Mode.On => x,
  }
}
pub flow lp(x: F32 at sample) -> F32 at sample {
  x * 0.5
}
pub flow ev(x: F32 at sample) -> F32 at event {
  if x > 0.5 { Some(x) } else { None }
}
";

/// The text of the flow `f` of the body `body`, of an event `v`, the `sample`
/// values `x` and `g` and the output `out`.
fn text(out: &str, body: &str) -> String {
    let inputs = "v: F32 at event, x: F32 at sample, g: Bool at sample, l4: F32 at (sample / 4), p: F32 at block, m: Mode at event, e: Bool at event";
    format!("{HEAD}pub flow f({inputs}) -> {out} {{\n  {body}\n}}\n")
}

/// Of each body, the place of the E0815 and the event value its note is at
/// (as they are written), none of one with no diagnostic.
fn expect(out: &str, rows: &[(&str, Option<(&str, &str)>)]) {
    for (body, want) in rows {
        let src = text(out, body);
        let a = check(&src);
        let got: Vec<_> = a
            .diagnostics
            .iter()
            .map(|d| {
                let notes = d.notes.iter().filter_map(|n| n.span).map(|s| s.text_in(&src)).collect::<Vec<_>>();
                (d.code, d.span.text_in(&src), notes)
            })
            .collect();
        let want: Vec<_> = want.iter().map(|&(place, at)| (Code::E0815, place, vec![at])).collect();
        assert_eq!(got, want, "{body}");
    }
}

#[test]
fn an_event_value_is_followed_to_the_place_and_an_at_or_a_flow_output_stops_it() {
    let sum = Some(("w + x", "w"));
    expect(
        "F32 at sample",
        &[
            ("prev~(v + x)", Some(("v + x", "v"))),
            ("prev~(half(v) + x)", Some(("half(v) + x", "half(v)"))),
            ("prev~(half(v + x))", Some(("half(v + x)", "v"))),
            ("let w = v * 2.0\n  prev~(w + x)", sum),
            ("let w = half(v)\n  prev~(w + x)", sum),
            ("let w = if v > 1.0 { v } else { 0.0 }\n  prev~(w + x)", sum),
            ("let w = v + x\n  prev~(w)", Some(("w", "v"))),
            ("let w = v + x\n  let u = w * 2.0\n  prev~(u)", Some(("u", "v"))),
            ("prev~(if g { v } else { x })", Some(("if g { v } else { x }", "v"))),
            ("prev~(if v > 1.0 { x } else { 0.0 })", Some(("if v > 1.0 { x } else { 0.0 }", "v > 1.0"))),
            (
                "prev~(match v > 1.0 { true => x, _ => 0.0 })",
                Some(("match v > 1.0 { true => x, _ => 0.0 }", "v > 1.0")),
            ),
            // Not apart by the fields.
            ("let t = (v, x)\n  prev~(t.1)", Some(("t.1", "v"))),
            ("let t = [v, x]\n  prev~(t[1])", Some(("t[1]", "v"))),
            ("let t = Bent { note: v, vel: x }\n  prev~(t.vel)", Some(("t.vel", "v"))),
            ("let (a, b) = (v, x)\n  prev~(b) + a", Some(("b", "v"))),
            ("match~ (v, x) { (a, b) => prev~(b) + a }", Some(("b", "v"))),
            ("match~ x { a if e => prev~(a), _ => lp~(x) }", Some(("a", "e"))),
            ("let t = par i in 0 ..< 2 { v + x }\n  prev~(t[0])", Some(("t[0]", "v"))),
            ("let t = par~ i in 0 ..< 2 { v + lp~(x) }\n  prev~(t[0])", Some(("t[0]", "v"))),
            ("let w = if~ g { v } else { lp~(x) }\n  prev~(w)", Some(("w", "v"))),
            ("prev~(ev~(x) + x)", Some(("ev~(x) + x", "ev~(x)"))),
            ("let d = prev~(^w)\n  let w = v + x\n  d + w", Some(("^w", "v"))),
            // What stops it, and what is no mix.
            ("prev~(v) + x", None),
            ("prev~((v at sample) + x)", None),
            ("prev~((v + x) at sample)", None),
            ("let w = v at sample\n  prev~(w + x)", None),
            ("prev~(lp~(v) + x)", None),
            ("prev~(prev~(v at sample) + x)", None),
            ("let w = v + x\n  prev~(lp~(w))", None),
            ("prev~(half(v) * p)", None),
            ("let t = (v, x)\n  prev~(x) + t.0", None),
            // `d` is no such place: read at the clock of the delay.
            ("vdelay~(x, v + x, 8)", None),
        ],
    );
}

#[test]
fn a_loop_a_reset_condition_and_an_event_output_are_places_and_a_when_condition_is_not() {
    let looped = "prev~(^n) + v + x";
    expect(
        "F32 at sample",
        &[
            ("let n = prev~(^n) + v + x\n  n", Some((looped, "v"))),
            ("let w = v + x\n  let n = prev~(^n) + w\n  n", Some(("prev~(^n) + w", "v"))),
            ("let n = prev~(^n) + v\n  n + x", None),
            ("let n = prev~(^n) + (v at sample) + x\n  n", None),
            ("let y = lp~(prev~(^y) + v)\n  y", None),
            ("lp~(x).reset_if~(v > 1.0 && g)", Some(("v > 1.0 && g", "v > 1.0"))),
            ("let r = v > 1.0\n  lp~(x).reset_if~(r && g)", Some(("r && g", "r"))),
            ("lp~(x).reset_if~(v > 1.0)", None),
            ("lp~(x).reset_if~(((v > 1.0) at sample) && g)", None),
            ("lp~(x).when~(v > 1.0 && g)", None),
            // §11.10: W of a delay of an event is its clock, below every periodic one.
            ("prev~(v).reset_if~(g)", Some(("g", "prev~(v)"))),
            ("prev~(v).reset_if~(v > 1.0)", None),
            ("prev~(v).reset_if~(p > 1.0)", None),
        ],
    );
    expect(
        "F32 at event",
        &[
            ("Some(v + x)", Some(("Some(v + x)", "v"))),
            ("if g { Some(v) } else { None }", Some(("if g { Some(v) } else { None }", "Some(v)"))),
            ("Some(v)", None),
            ("Some(lp~(v))", None),
            ("Some(x)", None),
            ("Some(v + x) at sample", None),
        ],
    );
}

/// The bodies after each candidate of the one diagnostic of `body`, with the
/// edits made from the last.
fn fixed(body: &str) -> Vec<String> {
    let src = text("F32 at sample", body);
    let a = check(&src);
    assert_eq!(a.diagnostics.len(), 1, "{body}");
    let after = |f: &onsa_diag::Fix| {
        let mut edits: Vec<_> = f.edits().to_vec();
        edits.sort_by_key(|e| std::cmp::Reverse((e.span.start, e.span.end)));
        edits.iter().fold(src.clone(), |mut s, e| {
            s.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
            s
        })
    };
    let (head, tail) = src.split_at(src.len() - body.len() - 3);
    assert!(tail.starts_with(body));
    let of = |s: String| s[head.len()..s.len() - 3].to_string();
    a.diagnostics[0].fixes.iter().map(|f| of(after(f))).collect()
}

#[test]
fn a_delay_has_the_candidates_that_keep_the_promise() {
    let rows: &[(&str, &[&str])] = &[
        ("prev~(v + x)", &["prev~(v) + x", "prev~((v at sample) + x)"]),
        ("prev~(x - v)", &["x - prev~(v)", "prev~(x - (v at sample))"]),
        ("2.0 * prev~(x + v)", &["2.0 * (x + prev~(v))", "2.0 * prev~(x + (v at sample))"]),
        ("2.0 * prev~(v + x)", &["2.0 * (prev~(v) + x)", "2.0 * prev~((v at sample) + x)"]),
        ("prev~(v * p + x)", &["prev~(v * p) + x", "prev~(((v * p) at sample) + x)"]),
        ("prev~(v + l4) at sample", &["(prev~(v) + l4) at sample", "prev~((v at (sample / 4)) + l4) at sample"]),
        // The first of no `init`, modifier, other delay or other root; nor where its value mixes
        // in another place; nor of a `^y`, which is in a delay only.
        ("prev~(v + x, 1.0)", &["prev~((v at sample) + x, 1.0)"]),
        ("delay~(v + x, 4)", &["delay~((v at sample) + x, 4)"]),
        ("prev~(v + x).when~(g)", &["prev~((v at sample) + x).when~(g)"]),
        ("prev~(half(v + x))", &["prev~(half((v at sample) + x))"]),
        ("prev~(prev~(v + x))", &["prev~(prev~((v at sample) + x))"]),
        ("let y = prev~(v + x)\n  prev~(y)", &["let y = prev~((v at sample) + x)\n  prev~(y)"]),
        ("let a = prev~(v + ^c)\n  let c = a + x\n  c", &["let a = prev~((v at sample) + ^c)\n  let c = a + x\n  c"]),
        (
            "let a = prev~(v + ^c)\n  let c = x * 2.0\n  a + c",
            &["let a = prev~((v at sample) + ^c)\n  let c = x * 2.0\n  a + c"],
        ),
        ("prev~(match (v, x) { (a, b) => a + b })", &["prev~(match (v at sample, x) { (a, b) => a + b })"]),
        // The second of what is written in the place only, of a type with `Default`.
        ("prev~(pick(m, x))", &[]),
        ("let w = v + x\n  prev~(w)", &[]),
        ("let w = v + x\n  prev~(v + w)", &["let w = v + x\n  prev~(v) + w"]),
        ("prev~(if g { half(v) } else { x })", &[]),
        ("prev~(if g { v } else { x })", &["prev~(if g { v at sample } else { x })"]),
        ("let n = prev~(^n) + v + x\n  n", &[]),
        ("lp~(x).reset_if~(v > 1.0 && g)", &[]),
        // §11.10: every `.when~` of a delay of an event.
        ("prev~(v).when~(g).reset_if~(v > 1.0)", &["prev~(v).reset_if~(v > 1.0)"]),
        ("prev~(v).when~(g).when~(v > 1.0)", &["prev~(v)"]),
    ];
    for (body, want) in rows {
        assert_eq!(fixed(body), *want, "{body}");
    }
}
