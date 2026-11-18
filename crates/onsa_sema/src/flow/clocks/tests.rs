//! The clocks the walk gives (§11.3): the loops of the `let`s (S-567 P3),
//! a `^y` that is no loop, and the places whose clock is not their
//! operand's. The expectations are of §11.3 and of the table of the rules.

use onsa_diag::FileId;
use onsa_syntax::ast::Ast;

use super::{WALKED, Walked};
use crate::clock::Clock;
use crate::tests::check;
use crate::{Analysis, DefId};

const S: Clock = Clock::SAMPLE;

/// The walk of the flow `flow` of `src`, with the tree to find its
/// expressions by their text, and whether the flow had no diagnostic.
struct Found {
    src: String,
    ast: Ast,
    a: Analysis,
    flow: DefId,
    walked: Walked,
    complete: bool,
}

fn walk_of(src: &str, flow: &str) -> Found {
    WALKED.with(|w| w.borrow_mut().clear());
    let a = check(src);
    let id = DefId(a.defs.iter().position(|d| d.name == flow).expect("the flow") as u32);
    let (_, walked, complete) =
        WALKED.with(|w| w.borrow_mut().drain(..).find(|(d, ..)| *d == id)).expect("the walk of the flow");
    let ast = onsa_syntax::parse(FileId(0), src).ast;
    Found { src: src.into(), ast, a, flow: id, walked, complete }
}

impl Found {
    /// The clock of the first expression written `text`.
    fn expr(&self, text: &str) -> Clock {
        let span = |e: &onsa_syntax::ast::Expr| &self.src[e.span.start as usize..e.span.end as usize];
        let e = self.ast.exprs.iter().position(|e| span(e) == text).unwrap_or_else(|| panic!("no `{text}`"));
        self.walked.info.exprs[&onsa_syntax::ast::ExprId(e as u32)]
    }

    /// The clock of the `let` `name`, the same in the two stages.
    fn let_(&self, name: &str) -> Clock {
        let lets = &self.a.flows[&self.flow].lets;
        let k = lets.iter().position(|l| l.name.as_deref() == Some(name)).unwrap_or_else(|| panic!("no let {name}"));
        assert_eq!(self.walked.lets[k], self.walked.checked[k], "the two stages of {name}");
        self.walked.lets[k]
    }

    /// The code of the first diagnostic of the walk.
    fn code(&self) -> Option<onsa_diag::Code> {
        self.walked.diag.as_ref().map(|d| d.code)
    }

    fn local(&self, name: &str) -> Clock {
        let locals = &self.a.flows[&self.flow].body.locals;
        let l = locals.iter().position(|l| l.name == name).unwrap_or_else(|| panic!("no local {name}"));
        self.walked.info.locals[&crate::body::LocalId(l as u32)]
    }
}

#[test]
fn a_loop_with_no_tick_from_outside_is_the_sample_of_the_body() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {\n  let c = prev~(^c) + 1.0\n  let d = prev~(^d) + p\n  c + d + x\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("c"), f.let_("d")), (S, S));
    assert_eq!((f.expr("^c"), f.expr("prev~(^c)"), f.expr("1.0")), (S, S, Clock::Const));
    assert_eq!((f.expr("p"), f.expr("prev~(^d) + p")), (Clock::Block, S));
}

#[test]
fn two_lets_that_read_each_other_have_one_clock() {
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let a = prev~(^b) * g\n  let b = a + g\n  b\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("a"), f.let_("b")), (S, S));
    assert_eq!((f.expr("^b"), f.expr("a + g")), (S, S));
}

#[test]
fn a_feedback_to_a_later_let_with_no_loop_reads_its_clock() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, g: F32 at block) -> F32 at sample {\n  let a = prev~(^b)\n  let b = x * 2.0\n  let c = g * 2.0\n  a + b + c\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("a"), f.let_("b"), f.let_("c")), (S, S, Clock::Block));
    // A `block` read by `^` (E0813): the delay goes on at `sample` in stage
    // 1; in stage 2 it is in error (§18.1), and `b` after it is walked.
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let a = prev~(^b)\n  let b = g * 2.0\n  a\n}\n",
        "f",
    );
    assert!(!f.complete);
    assert_eq!(f.code(), Some(onsa_diag::Code::E0813));
    assert_eq!((f.walked.lets[0], f.walked.lets[1]), (S, Clock::Block));
    assert_eq!((f.local("a"), f.local("b"), f.expr("^b")), (Clock::Error, Clock::Block, Clock::Block));
}

#[test]
fn the_operand_of_at_is_no_read_of_its_let() {
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let bs = g at sample\n  let a = prev~(bs)\n  a\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("bs"), f.let_("a"), f.expr("g")), (S, S, Clock::Block));
    // §11.3: `a` is `sample` whatever the clock of `b` (E0200 of W7-05 here).
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let a = prev~(^b at sample)\n  let b = g\n  a + b\n}\n",
        "f",
    );
    assert_eq!(f.code(), Some(onsa_diag::Code::E0200));
    assert_eq!((f.walked.lets[0], f.walked.lets[1]), (S, Clock::Block));
    assert_eq!((f.expr("^b"), f.expr("^b at sample")), (Clock::Block, S));
}

#[test]
fn the_init_of_a_delay_has_its_own_clock() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, k: F32 at init) -> F32 at sample {\n  let k2 = k * 2.0\n  let c = prev~(x, k2)\n  c\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("k2"), f.let_("c")), (Clock::Init, S));
    assert_eq!((f.expr("k2"), f.expr("prev~(x, k2)")), (Clock::Init, S));
}

#[test]
fn a_call_of_a_flow_has_the_clock_of_its_output_not_of_its_arguments() {
    let f = walk_of(
        "pub flow g(y: F32 at block) -> F32 at sample { y * 2.0 }\npub flow f(c: F32 at block) -> F32 at sample {\n  let a = g~(c)\n  a\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.let_("a"), f.expr("c"), f.expr("g~(c)")), (S, Clock::Block, S));
}

#[test]
fn the_bindings_of_a_match_and_the_index_of_a_par() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let p = par~ i in 0..<2 { x }\n  let m = match Some(c) {\n    Some(v) => v,\n    None => 0.0,\n  }\n  p[0] + m\n}\n",
        "f",
    );
    assert!(f.complete);
    assert_eq!((f.local("x"), f.local("c")), (S, Clock::Block));
    assert_eq!((f.local("p"), f.local("i")), (S, Clock::Init));
    assert_eq!((f.local("m"), f.local("v")), (Clock::Block, Clock::Block));
}

/// §18.1 (M-5): the output of the callee has its clock in error, so the call
/// is in error, and no place of the caller that reads it has a diagnostic.
#[test]
fn a_call_of_a_flow_whose_output_clock_is_in_error_is_in_error_and_quiet() {
    let callee = "pub flow g(y: F32 at sample) -> F32 at nope { y }\n";
    let callers = [
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = g~(x) at block\n  x\n}\n",
        "fn half(v: F32) -> F32 { v * 0.5 }\npub flow f(x: F32 at sample) -> F32 at sample {\n  let a = half(g~(x))\n  x\n}\n",
        "pub flow h(c: F32 at block) -> F32 at sample { c }\npub flow f(x: F32 at sample) -> F32 at sample {\n  let a = h~(g~(x))\n  x + a\n}\n",
        "pub flow f(x: F32 at sample) -> F32 at sample {\n  let a = prev~(x, g~(x))\n  a\n}\n",
    ];
    for caller in callers {
        let f = walk_of(&format!("{callee}{caller}"), "f");
        assert!(f.complete, "{caller}");
        assert_eq!(f.expr("g~(x)"), Clock::Error, "{caller}");
        assert_eq!(f.walked.diag, None, "{caller}");
    }
}

/// The codes of the diagnostics of `src` and the text each is at.
fn reported(src: &str) -> Vec<(onsa_diag::Code, String)> {
    let a = check(src);
    let at = |d: &onsa_diag::Diagnostic| src[d.span.start as usize..d.span.end as usize].to_string();
    a.diagnostics.iter().map(|d| (d.code, at(d))).collect()
}

/// Stage 2 walks on past an error and keeps the first diagnostic in the
/// order of the file (§18.1), of two errors in either order, an outer one
/// before an inner one; and the walk records the clocks and the nodes after
/// an error.
#[test]
fn the_walk_keeps_the_first_diagnostic_by_position() {
    let head = "pub fn noisy(v: F32) -> F32 uses {Alloc} { v }\npub flow f(x: F32 at sample, g: F32 at block) -> F32 at sample {\n";
    let cases = [
        ("  let a = x at block\n  let b = prev~(g)\n  x\n}\n", onsa_diag::Code::E0815, "x at block"),
        ("  let b = prev~(g)\n  let a = x at block\n  x\n}\n", onsa_diag::Code::E0813, "g"),
        ("  let s = (noisy(x), \"a\")\n  x\n}\n", onsa_diag::Code::E0810, "let s = (noisy(x), \"a\")"),
        // E0805 reads no clock: the outer call is reported.
        ("  let a = noisy(noisy(x))\n  x\n}\n", onsa_diag::Code::E0805, "noisy(noisy(x))"),
    ];
    for (body, code, at) in cases {
        let src = format!("{head}{body}");
        assert_eq!(reported(&src), vec![(code, at.to_string())], "{body}");
    }
    let f = walk_of(&format!("{head}{}", cases[0].0), "f");
    assert_eq!(f.walked.node_of.len(), 1);
    assert_eq!((f.local("a"), f.local("b")), (Clock::Block, Clock::Error));
    // `vdelay~` of no float (E0416, §11.4) before a later `let` of no Copy
    // (E0810).
    let src =
        "pub flow f(x: I32 at sample) -> I32 at sample {\n  let a = vdelay~(x, 1, 8)\n  let s = \"text\"\n  a\n}\n";
    assert_eq!(reported(src), vec![(onsa_diag::Code::E0416, "vdelay~(x, 1, 8)".to_string())]);
    // An E0713 held is the first by position too, and behind an error of the
    // flow checks (§18.1).
    let inout = "pub struct Pt { x: F32 }\nimpl Pt {\n  pub rt fn bump(inout self, v: F32) -> F32 { v }\n}\npub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let p = Pt { x: 1.0 }\n";
    let src = format!("{inout}  let k = p.bump(p.bump(x))\n  x + k\n}}\n");
    assert_eq!(reported(&src), vec![(onsa_diag::Code::E0713, "p.bump(p.bump(x))".to_string())]);
    let f = walk_of(&format!("{inout}  let k = p.bump(x)\n  let a = prev~(c)\n  x + k\n}}\n"), "f");
    assert_eq!(f.code(), Some(onsa_diag::Code::E0813));
    assert!(f.walked.inout_call.is_some());
}

/// §18.1: an expression whose rule of the clock rests on a check that fails
/// is in error (the E0813 of a delay, the E0805 and the E0815 of a call of a
/// function), and the places that read it have no diagnostic; an error that
/// leaves the clock known (the E0815 of `at`) does not quiet them.
#[test]
fn a_part_in_error_gives_no_diagnostic_to_its_users() {
    let head = "pub fn slow(v: F32) -> F32 { v }\npub fn noisy(v: F32) -> F32 uses {Alloc} { v }\npub flow f(x: F32 at sample, c: F32 at init, p: F32 at block) -> F32 at sample {\n";
    let cases = [
        // The `at` of a computed expression (E0200) and a function that is
        // not `rt` (E0815) read a delay in error.
        ("  let a = (prev~(p) + 1.0) at sample\n  x\n}\n", onsa_diag::Code::E0813, "p"),
        ("  let a = slow(prev~(p))\n  x\n}\n", onsa_diag::Code::E0813, "p"),
        // The E0200 of the marking at a call of `slow` at `init` read at
        // `sample` is before the E0813 after it.
        ("  x * slow(c) + prev~(p)\n}\n", onsa_diag::Code::E0200, "slow(c)"),
        // The calls with E0805 and E0815 are in error.
        ("  let a = slow(slow(x) + c)\n  x\n}\n", onsa_diag::Code::E0815, "slow(x)"),
        ("  let a = slow(noisy(x))\n  x\n}\n", onsa_diag::Code::E0805, "noisy(x)"),
        ("  let a = (noisy(x)) at block\n  x\n}\n", onsa_diag::Code::E0805, "noisy(x)"),
        // `e at k` is at `k` with its E0815: the E0813 of the delay over it
        // is at the same place, and first by its code (§18.1).
        ("  let a = prev~(x at block)\n  x\n}\n", onsa_diag::Code::E0813, "x at block"),
    ];
    for (body, code, at) in cases {
        let src = format!("{head}{body}");
        assert_eq!(reported(&src), vec![(code, at.to_string())], "{body}");
    }
    let f = walk_of(&format!("{head}{}", cases[0].0), "f");
    assert_eq!((f.expr("prev~(p)"), f.expr("(prev~(p) + 1.0) at sample"), f.local("a")), (Clock::Error, S, S));
}
