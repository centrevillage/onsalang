//! The stages of the expressions (§11.3, S-1196, S-1161, S-1166): of the
//! values of the parameter kinds through `at`, of the clock of one that reads
//! a tick, of the clocks of the conditions, and of the `let`s.

use onsa_syntax::ast::ExprId;

use crate::clock::{Clock, Ratio};
use crate::flow::FlowInfo;
use crate::tests::check;

const S: Clock = Clock::SAMPLE;
const S4: Clock = Clock::Tick(Ratio(-2));

/// The flow `f` of `src`, with no diagnostic, and the stage and the clock of
/// the first expression written as each of `texts`.
fn stages(src: &str, texts: &[&str]) -> Vec<(Clock, Clock)> {
    let a = check(src);
    assert!(a.diagnostics.is_empty(), "{:?}", a.diagnostics);
    let id = crate::DefId(a.defs.iter().position(|d| d.name == "f").expect("the flow") as u32);
    let f: &FlowInfo = &a.flows[&id];
    let ast = onsa_syntax::parse(onsa_diag::FileId(0), src).ast;
    let at = |t: &str| {
        let e = ast.exprs.iter().position(|e| e.span.text_in(src) == t).unwrap_or_else(|| panic!("no `{t}`"));
        let e = ExprId(e as u32);
        (f.clocks.stage(e).expect("a stage"), f.clocks.exprs[&e])
    };
    texts.iter().map(|t| at(t)).collect()
}

#[test]
fn a_value_of_the_parameter_kinds_is_of_its_stage_through_at_and_one_that_reads_a_tick_of_its_clock() {
    let src = "pub flow f(x: F32 at sample, n: I32 at block, m: I32 at block, a: I32 at init, p: F32 at block) -> F32 at sample {
    let q = (n at sample) / m
    let l = prev~(x)
    let k = (a at block) / 2
    x * F32.round_from(q + k) + (((p at (sample / 4)) * 2.0) at sample) + (l at sample) * 2.0
}";
    let got =
        stages(src, &["(n at sample) / m", "(a at block) / 2", "(p at (sample / 4)) * 2.0", "(l at sample) * 2.0"]);
    let want = [(Clock::Block, S), (Clock::Init, Clock::Block), (Clock::Block, S4), (S, S)];
    assert_eq!(got, want);
}

#[test]
fn a_conditional_form_is_of_the_clock_of_its_conditions_and_a_let_of_its_stage() {
    let src = "pub flow f(x: F32 at sample, d: I32 at block, o: Option[I32] at block) -> F32 at sample {
    let g = (d != 0) at sample
    let y = if (d != 0) at sample { 100 / (d - 1) } else { 0 }
    let z = if g { 1 } else { 2 }
    let w = match (o at sample) { Some(v) => v, None => 0 }
    let t = ((d != 0) at sample) && d > 1
    x * F32.round_from(y + z + w) + (if t { 1.0 } else { 0.0 })
}";
    let got = stages(src, &["g", "d != 0", "if (d != 0) at sample { 100 / (d - 1) } else { 0 }", "100 / (d - 1)"]);
    assert_eq!(got, [(Clock::Block, S), (Clock::Block, Clock::Block), (S, S), (Clock::Block, Clock::Block)]);
    let got = stages(src, &["if g { 1 } else { 2 }", "match (o at sample) { Some(v) => v, None => 0 }"]);
    assert_eq!(got, [(S, S), (S, S)]);
    let got = stages(src, &["((d != 0) at sample) && d > 1"]);
    assert_eq!(got, [(S, S)]);
}
