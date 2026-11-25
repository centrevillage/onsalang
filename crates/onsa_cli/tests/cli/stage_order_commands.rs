//! Which of two panics at one position `onsa test` reports, inside one stage of one flow (W7-11 U2b/t; spec §11.3 "一つの段の中では", §3.5 "panic しうる式が複数あるときは", §11.4, §11.5, §11.9, §11.10;
//! S-1233, S-1206, S-1159, S-1126, S-1154, S-1128, S-1241, S-1242, S-1221 (the second half)): the order of the work of a stage is seen by this report only (and by the ticks of an event, §11.11), so a case is a
//! flow with two divisions by 0 at one position and the line of the one that stops the run (`failure.span`, the line only).
//!
//! The order (§11.3): in a stage the `let`s from above, then the output expression, then what the delays store (in the order their names are written, an inner one after the one that holds it, §11.4).
//! Inside an expression it is §3.5 (§11.5 for `if~` and `match~`: the side that selects, then the bodies in the order written). A call of an instance does its work of the stage (its `init`, its `block`
//! stage, its ticks) where it is written, after its arguments and the conditions of its modifiers in the order written (a chain from the left), whether the output is read at that stage or not; in the first
//! argument of a built-in delay too, at any depth; what is left of that argument (its operations) is a store, after everything above (S-1126).
//!
//! One launch of `onsa test` reads a package with one module for each case (`<name>.onsa` with a test `stops`), so a group costs one run. The two divisions of a case are at the same frame (1 for `sample`, 4
//! for `sample / 4`, the first call for `block` and `init`). Each case was also run with its first division made safe: it then stops at the other one, so the line says which came first. The texts are
//! written from the spec; none is taken from the output of the compiler.
//!
//! The steps of W7-11 U2b that gave the order of a group: U2b-a is the order of the arguments and the conditions of a chain (`_u2b_a`), U2b-b is the rest (`_u2b_b`).

use crate::slow_stage_commands::line_of;
use crate::test_support::{Dir, diagnostics, failure_of, record, span_of, test_json};

const BLK: &str = "f.Params { p: 0 }, 5";
const INIT: &str = "f.Config { c: 0 }, 2";

/// A module with a flow `f` and two divisions; `first` is the text of the one that must stop the run (on one line of the module).
struct Case {
    name: String,
    src: String,
    first: &'static str,
}

/// (name, the division that stops the run, the parts of the module: the flows, then the text of `f`)
type Row<'a> = (&'a str, &'static str, &'a [&'a str]);

/// The module: the parts as written, and the test `stops` that renders `f` with `run`.
fn module(parts: &[&str], run: &str) -> String {
    format!("{}\ntest \"stops\" {{\n  let o = f.render({run}, 8.0)\n  assert o.out[0] == 0\n}}\n", parts.concat())
}

fn rows(rows: &[Row<'_>], run: &str) -> Vec<Case> {
    rows.iter().map(|(n, first, parts)| Case { name: n.to_string(), src: module(parts, run), first }).collect()
}

/// One launch of `onsa test` over the package of `cases`: each stops at the line of its `first`.
fn assert_first_stops(tag: &str, cases: &[Case]) {
    let d = Dir::pkg(tag);
    for c in cases {
        assert_eq!(c.src.lines().filter(|l| l.contains(c.first)).count(), 1, "`{}` is on one line: {}", c.first, c.src);
        d.write(&format!("{}.onsa", c.name), &c.src);
    }
    let (out, doc) = test_json(d.root(), &[]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(diagnostics(&doc).is_empty(), "{}", out.stdout);
    let mut wrong = Vec::new();
    for c in cases {
        let at = span_of(&failure_of(record(&doc, &c.name, "stops"))["span"]);
        let want = line_of(&c.src, c.first);
        if at.file != format!("{}.onsa", c.name) || at.line != want {
            wrong.push(format!("{}: want the line {want} (`{}`), stopped at {}:{}", c.name, c.first, at.file, at.line));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

// ----------------------------------------------------------------------------- the four stages: a call and a division

const KS: &str =
    "flow kc(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at sample, 1)\n  let q = 100 / d\n  q\n}\n\n";
const KQ: &str = "flow kc(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at (sample / 4), 1)\n  let q = 100 / d\n  q at sample\n}\n\n";
const KB: &str = "flow kc(d: I32 at block) -> I32 at sample {\n  let q = 100 / d\n  q at sample\n}\n\n";
const KI: &str = "flow kc(d: I32 at init) -> I32 at sample {\n  let q = 100 / d\n  q at sample\n}\n\n";
const FS: &str = "flow fb(x: I32 at sample, p: I32 at block) -> I32 at sample {\n  let d2 = prev~(p at sample, 1)\n  let q2 = 300 / d2\n  x + q2\n}\n\n";
const FQ: &str = "flow fb(x: I32 at sample, p: I32 at block) -> I32 at sample {\n  let d2 = prev~(p at (sample / 4), 1)\n  let q2 = 300 / d2\n  x + (q2 at sample)\n}\n\n";
const FB: &str = "flow fb(x: I32 at sample, d: I32 at block) -> I32 at sample {\n  let q2 = 300 / d\n  x + q2\n}\n\n";
const FI: &str = "flow fb(x: I32 at sample, d: I32 at init) -> I32 at sample {\n  let q2 = 300 / d\n  x + q2\n}\n\n";
const SIG: &str = "pub flow f(p: I32 at block) -> I32 at sample {\n";
const SIG_I: &str = "pub flow f(c: I32 at init) -> I32 at sample {\n";
const LET_E: &str = "  let e = prev~(p at sample, 1)\n";
const LET_E4: &str = "  let e = prev~(p at (sample / 4), 1)\n";

/// Per stage: the tag, the child `kc` that divides at the stage, `fb` that takes the child's output and divides at the stage too, the signature of `f` and its `let` of a value of the stage, the argument
/// of the child, the parent's own division, the same as a part of the output expression, the use of its `let r`, and the run. (The child's division is `100 / d`, `fb`'s is `300 / d2` or `300 / d`.)
#[rustfmt::skip]
const KITS: [[&str; 10]; 4] = [
    ["s", KS, FS, SIG, LET_E, "p", "200 / e", "(200 / e)", "r", BLK],
    ["q", KQ, FQ, SIG, LET_E4, "p", "200 / e", "((200 / e) at sample)", "(r at sample)", BLK],
    ["b", KB, FB, SIG, "", "p", "200 / p", "(200 / p)", "r", BLK],
    ["i", KI, FI, SIG_I, "", "c", "200 / c", "(200 / c)", "r", INIT],
];

/// The parent has a call of the child and a division of its own, in one of six shapes.
fn stage_case(tag: &str, shape: &str) -> Case {
    let [_, kid, outer, sig, pre, arg, own, own_out, r, run] = *KITS.iter().find(|k| k[0] == tag).expect("a kit");
    let call = format!("kc~({arg})");
    let (body, child_first) = match shape {
        "child_above" => (format!("  let k = {call}\n  let r = {own}\n  k + {r}\n"), true),
        "child_below" => (format!("  let r = {own}\n  let k = {call}\n  {r} + k\n"), false),
        "out_child_left" => (format!("  {call} + {own_out}\n"), true),
        "out_child_right" => (format!("  {own_out} + {call}\n"), false),
        "nested" => (format!("  fb~({call}, {arg})\n"), true),
        "unread" => (format!("  let _ = {call}\n  let r = {own}\n  {r}\n"), true),
        _ => unreachable!("{shape}"),
    };
    let (outer, pre) = if shape == "nested" { (outer, "") } else { ("", pre) };
    let first = if child_first { "100 / d" } else { own };
    Case { name: format!("{tag}_{shape}"), src: module(&[kid, outer, sig, pre, &body, "}\n"], run), first }
}

fn stage_cases(tags: &[&str], shapes: &[&str]) -> Vec<Case> {
    tags.iter().flat_map(|t| shapes.iter().map(move |s| stage_case(t, s))).collect()
}

/// §11.3 "一つの段の中では": the `let`s and the output expression go from above and from the left, and a call does its work where it is written (S-1233, S-1206, S-1159, S-1128). In the `sample` stage this
/// was so before in every shape; in the other three stages the shapes where the parent's division is written first (the call below the `let`, on the right in the output expression) were too.
#[test]
fn the_forms_that_stop_in_the_order_of_the_text_did_not_change_with_s1233() {
    let mut cases =
        stage_cases(&["s"], &["child_above", "child_below", "out_child_left", "out_child_right", "nested", "unread"]);
    cases.extend(stage_cases(&["q", "b", "i"], &["child_below", "out_child_right"]));
    assert_first_stops("stage_order_unchanged_stages", &cases);
}

/// S-1233 (table of the group 119: "`block` の段の子、`init` の段の子 … 親が先 → 子が先"; "入れ子 `fb~(kid4~(p), p)` の遅い段 外 → 内"; "出力の式 / `let` と、読まない子の `sample` の仕事 出力の式 / `let` → 子"):
/// in a stage of `sample / 4`, the `block` stage and the `init` stage, a call written above the division is run first: a child above a `let`, on the left in the output expression, as the argument of
/// another call (the inner before the outer's own work) and a child that nothing reads. Before the work the parent's own division came first in each.
#[test]
fn a_call_above_a_division_in_the_slower_tick_block_and_init_stages_stops_first_u2b_b() {
    assert_first_stops(
        "stage_order_stages_u2b_b",
        &stage_cases(&["q", "b", "i"], &["child_above", "out_child_left", "nested", "unread"]),
    );
}

// ----------------------------------------------------------------------------- `if~` and `match~`

const KS2: &str = "flow ks2(x: I32 at sample) -> I32 at sample {\n  let n = x + prev~(^n)\n  n\n}\n\n";
const KT: &str =
    "flow kt(p: I32 at block) -> I32 at sample {\n  let d = prev~(p at sample, 1)\n  let q = 300 / d\n  q\n}\n\n";
const IDL: &str = "flow idl(x: I32 at sample) -> I32 at sample {\n  x + prev~(x)\n}\n\n";

/// §11.5 "評価の順は、選ぶ側を先に、次に全ての枝と腕の本体を書いた順である": the bodies are all evaluated in the order written, whichever is taken (the second arm of `i_arms_in_order` is taken); the second
/// condition of a chain is before the first body; a `block` part of a body is after the condition. `match~` too: the binding of an arm that is not taken is `T.default()`, so `100 / (n + e)` divides by `e`.
/// A call in an arm is run where it is written, before the `let` below it (the stage of a slower tick is in the group of U2b-b).
#[test]
#[rustfmt::skip]
fn the_side_that_selects_is_first_and_then_the_bodies_in_the_order_written_in_if_tilde_and_match_tilde() {
    let mut cases = rows(&[
        ("i_select_first", "100 / e", &[KS2, SIG, LET_E, "  let y = if~ (\n    100 / e\n  ) == 1 {\n    ks2~(200 / e)\n  } else {\n    ks2~(300 / e)\n  }\n  y\n}\n"]),
        ("i_arms_in_order", "100 / e", &[KS2, SIG, LET_E, "  let y = if~ e == 5 {\n    ks2~(100 / e)\n  } else {\n    ks2~(200 / e)\n  }\n  y\n}\n"]),
        ("i_second_condition", "300 / e", &[KS2, SIG, LET_E, "  let y = if~ e == 7 {\n    ks2~(100 / e)\n  } else if (\n    300 / e) == 1 {\n    ks2~(400 / e)\n  } else {\n    ks2~(500 / e)\n  }\n  y\n}\n"]),
        ("i_call_in_arm", "100 / d", &[KS, SIG, LET_E, "  let y = if~ e == 5 { kc~(p) } else { 0 }\n  let r = 200 / e\n  y + r\n}\n"]),
        ("m_arms_in_order", "100 / (n + e)", &[KS2, SIG, LET_E, "  match~ e {\n    n if n > 7 => ks2~(100 / (n + e)),\n    _ => ks2~(200 / e),\n  }\n}\n"]),
        ("m_target_first", "100 / e", &[KS2, SIG, LET_E, "  match~ (\n    100 / e\n  ) {\n    n if n > 7 => ks2~(200 / e),\n    _ => ks2~(300 / e),\n  }\n}\n"]),
    ], BLK);
    cases.extend(rows(&[
        ("i_block_in_second_condition", "300 / p", &[KS2, "pub flow f(p: I32 at block, b: Bool at block) -> I32 at sample {\n", LET_E, "  let y = if~ b {\n    ks2~(e) + e * (100 / p)\n  } else if (\n    300 / p) == 1 {\n    ks2~(e)\n  } else {\n    ks2~(e)\n  }\n  y\n}\n"]),
    ], "f.Params { p: 0, b: false }, 5"));
    assert_first_stops("stage_order_if_match", &cases);
}

/// S-1233 (table: "`if~` の腕の中の呼び出しの遅い段と下の `let` 親の下の `let` → 呼び出し"): a call in an `if~` arm, in a stage of `sample / 4`, is run where it is written, before the `let` below it.
#[test]
fn a_call_in_an_arm_of_a_slower_tick_stops_before_the_let_below_it_u2b_b() {
    let src: &[&str] = &[
        KQ,
        SIG,
        LET_E4,
        "  let y = if~ (e at sample) == 5 { kc~(p) } else { 0 }\n  let r = 200 / e\n  y + (r at sample)\n}\n",
    ];
    assert_first_stops("stage_order_arm_slow", &rows(&[("i_call_in_slow_arm", "100 / d", src)], BLK));
}

// ----------------------------------------------------------------------------- the chain of modifiers

/// §11.3 "引数と修飾子の条件を字面の順に評価してから…" and §11.10 (S-1233, S-1221 second half; table: "頭の引数と修飾子の条件 条件が先 → 引数が先", "一つの連鎖の二つの修飾子の条件 外が先 → 字面の順"): the arguments of the
/// head are before the conditions, and the conditions are from the left of the chain, with `reset_if~` only, `when~` only, both, a `.down~(4)` that wraps the head (the arguments, the conditions inside it and
/// outside it); an argument that is an index (`XS[i]`, out of range at the frame 1 as `n` is 0) and the calls in the arguments and in the conditions are in the same order. The conditions went first before.
#[test]
#[rustfmt::skip]
fn the_arguments_of_a_chain_come_before_its_conditions_and_the_conditions_are_from_the_left_u2b_a() {
    let g = "const XS: [U32; 2] = [10, 20]\n\nflow g(x: U32 at sample) -> U32 at sample {\n  x + prev~(x)\n}\n\npub flow f(p: U32 at block) -> U32 at sample {\n  let n = prev~(p at sample, 1)\n  let i = 2 - n\n";
    let mut cases = rows(&[
        ("c_arg_reset", "200 / e", &[KS2, SIG, LET_E, "  ks2~(\n    200 / e\n  ).reset_if~(\n    (300 / e) == 7\n  )\n}\n"]),
        ("c_arg_when", "200 / e", &[KS2, SIG, LET_E, "  ks2~(\n    200 / e\n  ).when~(\n    (300 / e) == 7\n  )\n}\n"]),
        ("c_when_then_reset", "200 / e", &[KS2, SIG, LET_E, "  ks2~(1).when~(\n    (200 / e) == 7\n  ).reset_if~(\n    (300 / e) == 7\n  )\n}\n"]),
        ("c_reset_then_when", "200 / e", &[KS2, SIG, LET_E, "  ks2~(1).reset_if~(\n    (200 / e) == 7\n  ).when~(\n    (300 / e) == 7\n  )\n}\n"]),
        ("c_arg_call_and_cond_call", "100 / d", &[KS, KT, IDL, SIG, "  idl~(kc~(p)).reset_if~(kt~(p) == 7)\n}\n"]),
        ("c_two_cond_calls", "100 / d", &[KS, KT, KS2, SIG, "  ks2~(1).when~(kc~(p) == 7).reset_if~(kt~(p) == 7)\n}\n"]),
        ("c_down_arg_and_outer_cond", "200 / e", &[KS2, SIG, LET_E4, "  (ks2~(\n    200 / e\n  ).down~(4).reset_if~(\n    (300 / e) == 7\n  )) at sample\n}\n"]),
        ("c_down_inner_then_outer_cond", "200 / e", &[KS2, SIG, LET_E4, "  (ks2~(1).reset_if~(\n    (200 / e) == 7\n  ).down~(4).reset_if~(\n    (300 / e) == 7\n  )) at sample\n}\n"]),
    ], BLK);
    cases.extend(rows(&[("c_index_argument", "XS[i]", &[g, "  g~(\n    XS[i]\n  ).reset_if~(\n    (300 / n) == 7\n  )\n}\n"])], "f.Params { p: 0 }, 5"));
    assert_first_stops("stage_order_chain_u2b_a", &cases);
}

// ----------------------------------------------------------------------------- delays and their stores

/// §11.3 and §11.4 (S-1126, S-1154; table: "変わらない所"): what a delay stores is evaluated after the `let`s and the output expression of the stage (`d_store_after_*`), the delays in the order their names are
/// written, an inner one after the one that holds it (`outer_first`: the outer's `300 / e` before the inner's `100 / e` though it is written after; a name written above is first, `by_name`); the output is the value
/// stored before. A modifier on a delay has its condition evaluated where the delay is written (S-1241): the condition (`200 / e`) is before the first argument's operation (`100 / e`), a store.
#[test]
#[rustfmt::skip]
fn what_a_delay_stores_is_evaluated_after_the_lets_and_in_the_order_the_delays_are_written() {
    let cases = rows(&[
        ("d_store_after_let", "200 / e", &[SIG, LET_E, "  let a = prev~(100 / e)\n  let b = 200 / e\n  a + b\n}\n"]),
        ("d_store_after_output", "200 / e", &[SIG, LET_E, "  let a = prev~(100 / e)\n  a + 200 / e\n}\n"]),
        ("d_store_outer_first", "300 / e", &[SIG, LET_E, "  let a = prev~(prev~(\n    100 / e\n  ) + (\n    300 / e))\n  a\n}\n"]),
        ("d_store_outer_first_right", "300 / e", &[SIG, LET_E, "  let a = prev~((\n    300 / e\n  ) + prev~(\n    100 / e))\n  a\n}\n"]),
        ("d_store_two_delays_in_a_let", "100 / e", &[SIG, LET_E, "  let a = prev~(prev~(\n    100 / e\n  ) + 0) + prev~(\n    300 / e)\n  a\n}\n"]),
        ("d_store_two_lets_by_name", "300 / e", &[SIG, LET_E, "  let b = prev~(^a + (300 / e))\n  let a = prev~(100 / e)\n  a + b\n}\n"]),
        ("d_condition_before_store_reset", "200 / e", &[SIG, LET_E, "  let a = prev~(\n    100 / e\n  ).reset_if~(\n    (200 / e) == 7\n  )\n  a\n}\n"]),
        ("d_condition_before_store_when", "200 / e", &[SIG, LET_E, "  let a = prev~(\n    100 / e\n  ).when~(\n    (200 / e) == 7\n  )\n  a\n}\n"]),
    ], BLK);
    assert_first_stops("stage_order_delay_stores", &cases);
}

/// §11.3 "組込みの遅延の第 1 引数の中に書いたインスタンスの呼び出し（とその引数）も、書いた位置で行う" (S-1126, S-1241, S-1242, S-1233; table: "遅延の第 1 引数の中の呼び出し … 親の `let` → 呼び出し", "`prev~(x, 100 / c)` … 下の
/// `let` → 遅延の `init` の引数"): a call in the first argument of a delay, at any depth, is run where the delay is written, before the `let` below it (also with a condition after it); so is the condition of a modifier
/// of a delay in that argument; and the `init` argument of a delay is of the `init` stage where the delay is written, before a `let` of `init` below it. The stores came after the `let`s before.
#[test]
#[rustfmt::skip]
fn a_call_and_a_condition_in_the_first_argument_of_a_delay_and_its_init_are_where_they_are_written_u2b_b() {
    let mut cases = rows(&[
        ("d_call_in_argument", "100 / d", &[KS, SIG, LET_E, "  let a = prev~(kc~(p))\n  let r = 200 / e\n  a + r\n}\n"]),
        ("d_call_in_nested_argument", "100 / d", &[KS, SIG, LET_E, "  let a = prev~(prev~(kc~(p)) + 1)\n  let r = 200 / e\n  a + r\n}\n"]),
        ("d_modified_delay_in_argument", "100 / e", &[SIG, LET_E, "  let a = prev~(prev~(e).reset_if~(\n    (100 / e) == 7\n  ))\n  let r = 200 / e\n  a + r\n}\n"]),
        ("d_call_in_argument_and_condition", "100 / d", &[KS, SIG, LET_E, "  let a = prev~(\n    kc~(p)\n  ).reset_if~(\n    (200 / e) == 7\n  )\n  a\n}\n"]),
    ], BLK);
    cases.extend(rows(&[("d_init_argument", "100 / c", &[SIG_I, "  let a = prev~(c at sample, 100 / c)\n  let b = 200 / c\n  a + b\n}\n"])], INIT));
    assert_first_stops("stage_order_delay_arguments_u2b_b", &cases);
}

/// S-1244: a part of a slower stage with a `^name` in the first argument of a delay is evaluated at the end of its stage (§11.2, §11.3), after the `let` of it written below the delay: `200 / k` stops the run before
/// the part `100 / ^k` of `block`. Before the work the lowering of it was an internal error (R-520).
#[test]
#[rustfmt::skip]
fn a_part_of_block_with_a_name_below_is_evaluated_at_the_end_of_its_stage_u2b_b() {
    let cases = rows(&[
        ("d_back_part_block", "200 / k", &[SIG, "  let a = prev~((\n    100 / ^k) at sample)\n  let k = p\n  let r = 200 / k\n  a + r\n}\n"]),
    ], BLK);
    assert_first_stops("stage_order_back_part", &cases);
}

/// S-1244 (§11.2, §11.3): what reads a `^name` in the first argument of a delay is the part it is written in and the parts a plain condition with it selects; a `^name` in the first argument of a delay inside is the
/// output of that delay and does not count, and an arm of an `if~` is no conditional position. `q4` is a `let` of `sample / 4` below: where the part does not read it, the part is evaluated where it is written (`100 / d4`
/// before the `let` below), else at the end of its stage (`300 / d4` first). The mutants of the rule that move the part change the line (the break side of W7-11 U2b).
#[test]
#[rustfmt::skip]
fn a_part_waits_for_the_end_of_its_stage_only_where_it_reads_a_name_below() {
    let g = "flow g(x: I32 at sample) -> I32 at sample {\n  (x + prev~(x)) % 101\n}\n\n";
    let v = "enum V {\n  A(I32),\n  B,\n}\n\nimpl Default for V {\n  rt fn default() -> Self {\n    V.B\n  }\n}\n\n";
    let d4 = "  let d4 = prev~(p at (sample / 4), 1)\n";
    let below = "  let a = (300 / d4) at sample\n  let q4 = d4 + 1\n  (y + a + (q4 at sample)) % 101\n}\n";
    let cases = rows(&[
        ("b_condition_of_a_delay_inside", "100 / d4", &[SIG, d4, "  let y = prev~((p at sample) + ((if prev~(^q4) > -99 {\n    100 / d4\n  } else { 0 }) at sample))\n", below]),
        ("b_condition_of_the_name", "300 / d4", &[SIG, d4, "  let y = prev~((p at sample) + ((if ^q4 > -99 {\n    100 / d4\n  } else { 0 }) at sample))\n", below]),
        ("b_part_with_the_name", "300 / d4", &[SIG, d4, "  let y = prev~((p at sample) + (((^q4 + (\n    100 / d4)) % 101) at sample))\n", below]),
        ("b_arm_of_an_if_tilde", "100 / d4", &[g, SIG, d4, "  let y = prev~((p at sample) + (if~ (^q4 at sample) > -99 { g~(p at sample) + ((\n    100 / d4) at sample) } else { 0 }))\n", below]),
        ("b_guard_of_block", "300 / p", &[SIG, "  let y = prev~(if ^k > -99 { (p at sample) + (\n    100 / p) } else { 0 })\n  let a = 300 / p\n  let k = p + 1\n  y + a + k\n}\n"]),
        ("b_binding_of_an_arm", "300 / p", &[v, g, SIG, "  let y = prev~(match~ ^v { V.A(b) => g~(p at sample) + (\n    100 / (b - b + p)), V.B => 0 })\n  let a = 300 / p\n  let v: V = if p > -99 { V.A(p) } else { V.B }\n  y + a\n}\n"]),
    ], BLK);
    assert_first_stops("stage_order_waiting_parts", &cases);
}

// ----------------------------------------------------------------------------- `par~`

const KA: &str =
    "flow ka(d: U32 at init) -> U32 at sample {\n  let z = prev~(d at sample, 1)\n  let q = 100 / z\n  q\n}\n\n";
const KBU: &str =
    "flow kb(d: U32 at init) -> U32 at sample {\n  let z = prev~(d at sample, 1)\n  let q = 300 / z\n  q\n}\n\n";

/// §11.3 "`par~` は複製ごとに本体をこの順でたどる" (S-1233): the replicas in order, the body of each in order: A[0], B[0], A[1], B[1]. `ka~(1 - i)` stops at the frame 1 for i = 1 and `kb~(i)` for i = 0, so B[0]
/// is before A[1] and `300 / z` stops the run (all the A before all the B would give `100 / z`). A `par~` that nothing reads, and one of which a single element is read, run the same.
#[test]
#[rustfmt::skip]
fn the_replicas_of_a_par_tilde_are_run_one_at_a_time_in_order_read_or_not() {
    let sig = "pub flow f(p: U32 at block) -> U32 at sample {\n";
    let cases = rows(&[
        ("p_unread", "300 / z", &[KA, KBU, sig, "  let _ = par~ i in 0 ..< 2 { ka~(1 - i) + kb~(i) }\n  p at sample\n}\n"]),
        ("p_read_one", "300 / z", &[KA, KBU, sig, "  let zs = par~ i in 0 ..< 2 { ka~(1 - i) + kb~(i) }\n  zs[1]\n}\n"]),
    ], "f.Params { p: 0 }, 5");
    assert_first_stops("stage_order_par", &cases);
}

// ----------------------------------------------------------------------------- moving an expression into a flow

/// A moved expression: the tag, the child flow, the signature and lets of `f`, the expression of the `let`, the inputs and the arguments of the flow `g` that takes it, the division that stops, the run.
#[rustfmt::skip]
const MOVES: [[&str; 8]; 5] = [
    ["s_child_left", KS, "pub flow f(p: I32 at block) -> I32 at sample {\n  let e = prev~(p at sample, 1)\n", "kc~(p) + 200 / e", "p: I32 at block, e: I32 at sample", "p, e", "100 / d", BLK],
    ["s_own_left", KS, "pub flow f(p: I32 at block) -> I32 at sample {\n  let e = prev~(p at sample, 1)\n", "200 / e + kc~(p)", "p: I32 at block, e: I32 at sample", "p, e", "200 / e", BLK],
    ["q_child_left", KQ, "pub flow f(p: I32 at block) -> I32 at sample {\n  let e = prev~(p at (sample / 4), 1)\n", "kc~(p) + ((200 / e) at sample)", "p: I32 at block, e: I32 at (sample / 4)", "p, e", "100 / d", BLK],
    ["b_child_left", KB, SIG, "kc~(p) + 200 / p", "p: I32 at block", "p", "100 / d", BLK],
    ["i_child_left", KI, SIG_I, "kc~(c) + 200 / c", "c: I32 at init", "c", "100 / d", INIT],
];

/// For each name: the flow `f` with `let y = <expr>`, and the same with `<expr>` moved into `g` and `let y = g~(..)`. Both stop at the same division.
fn moves(names: &[&str]) -> Vec<Case> {
    let mut out = Vec::new();
    for [name, kid, head, expr, inputs, args, first, run] in MOVES.iter().filter(|m| names.contains(&m[0])) {
        let g = format!("flow g({inputs}) -> I32 at sample {{\n  {expr}\n}}\n\n");
        let orig = module(&[kid, head, &format!("  let y = {expr}\n  y\n}}\n")], run);
        let moved = module(&[kid, &g, head, &format!("  let y = g~({args})\n  y\n}}\n")], run);
        out.push(Case { name: format!("mv_{name}_orig"), src: orig, first });
        out.push(Case { name: format!("mv_{name}_moved"), src: moved, first });
    }
    out
}

/// §11.3 (S-1233): the expression of a `let` moved into a flow whose arguments are names (`let y = kc~(p) + 200 / e` into `g~(p, e)`) stops at the same division as before (a division of the `block` stage is not
/// passed as an input at `sample`, which would change its stage). The `sample` stage did not change.
#[test]
fn an_expression_moved_into_a_flow_of_names_stops_at_the_same_division_in_the_sample_stage() {
    assert_first_stops("stage_order_moves_s", &moves(&["s_child_left", "s_own_left"]));
}

/// The same for the stages of `sample / 4`, `block` and `init` (S-1233, S-1206, S-1128): the call written first stops in the flow with the expression and in the flow that it was moved into.
#[test]
fn an_expression_moved_into_a_flow_of_names_stops_at_the_same_division_in_the_other_stages_u2b_b() {
    assert_first_stops("stage_order_moves_other_u2b_b", &moves(&["q_child_left", "b_child_left", "i_child_left"]));
}
