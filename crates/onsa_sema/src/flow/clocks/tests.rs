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
/// expressions by their text.
struct Found {
    src: String,
    ast: Ast,
    a: Analysis,
    flow: DefId,
    walked: Walked,
    compared: bool,
}

fn walk_of(src: &str, flow: &str) -> Found {
    WALKED.with(|w| w.borrow_mut().clear());
    let a = check(src);
    let id = DefId(a.defs.iter().position(|d| d.name == flow).expect("the flow") as u32);
    let (_, walked, compared) =
        WALKED.with(|w| w.borrow_mut().drain(..).find(|(d, ..)| *d == id)).expect("the walk of the flow");
    let ast = onsa_syntax::parse(FileId(0), src).ast;
    Found { src: src.into(), ast, a, flow: id, walked, compared }
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
    assert!(f.compared);
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
    assert!(f.compared);
    assert_eq!((f.let_("a"), f.let_("b")), (S, S));
    assert_eq!((f.expr("^b"), f.expr("a + g")), (S, S));
}

#[test]
fn a_feedback_to_a_later_let_with_no_loop_reads_its_clock() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, g: F32 at block) -> F32 at sample {\n  let a = prev~(^b)\n  let b = x * 2.0\n  let c = g * 2.0\n  a + b + c\n}\n",
        "f",
    );
    assert!(f.compared);
    assert_eq!((f.let_("a"), f.let_("b"), f.let_("c")), (S, S, Clock::Block));
    // A `block` read by `^` (E0813): the delay goes on at `sample`.
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let a = prev~(^b)\n  let b = g * 2.0\n  a\n}\n",
        "f",
    );
    assert!(!f.compared);
    assert_eq!((f.local("a"), f.local("b"), f.expr("^b")), (S, Clock::Block, Clock::Block));
}

#[test]
fn the_operand_of_at_is_no_read_of_its_let() {
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let bs = g at sample\n  let a = prev~(bs)\n  a\n}\n",
        "f",
    );
    assert!(f.compared);
    assert_eq!((f.let_("bs"), f.let_("a"), f.expr("g")), (S, S, Clock::Block));
    // §11.3: `a` is `sample` whatever the clock of `b` (E0200 of W7-05 here).
    let f = walk_of(
        "pub flow f(g: F32 at block) -> F32 at sample {\n  let a = prev~(^b at sample)\n  let b = g\n  a + b\n}\n",
        "f",
    );
    assert_eq!((f.local("a"), f.local("b")), (S, Clock::Block));
    assert_eq!((f.expr("^b"), f.expr("^b at sample")), (Clock::Block, S));
}

#[test]
fn the_init_of_a_delay_has_its_own_clock() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, k: F32 at init) -> F32 at sample {\n  let k2 = k * 2.0\n  let c = prev~(x, k2)\n  c\n}\n",
        "f",
    );
    assert!(f.compared);
    assert_eq!((f.let_("k2"), f.let_("c")), (Clock::Init, S));
    assert_eq!((f.expr("k2"), f.expr("prev~(x, k2)")), (Clock::Init, S));
}

#[test]
fn a_call_of_a_flow_has_the_clock_of_its_output_not_of_its_arguments() {
    let f = walk_of(
        "pub flow g(y: F32 at block) -> F32 at sample { y * 2.0 }\npub flow f(c: F32 at block) -> F32 at sample {\n  let a = g~(c)\n  a\n}\n",
        "f",
    );
    assert!(f.compared);
    assert_eq!((f.let_("a"), f.expr("c"), f.expr("g~(c)")), (S, Clock::Block, S));
}

#[test]
fn the_bindings_of_a_match_and_the_index_of_a_par() {
    let f = walk_of(
        "pub flow f(x: F32 at sample, c: F32 at block) -> F32 at sample {\n  let p = par~ i in 0..<2 { x }\n  let m = match Some(c) {\n    Some(v) => v,\n    None => 0.0,\n  }\n  p[0] + m\n}\n",
        "f",
    );
    assert!(f.compared);
    assert_eq!((f.local("x"), f.local("c")), (S, Clock::Block));
    assert_eq!((f.local("p"), f.local("i")), (S, Clock::Init));
    assert_eq!((f.local("m"), f.local("v")), (Clock::Block, Clock::Block));
}
