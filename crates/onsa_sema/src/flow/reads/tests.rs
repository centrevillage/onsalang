use onsa_diag::{Code, Diagnostic, Span};

use crate::names::body::{Binding, BodyNames, unused_binding};
use onsa_syntax::ast::Ast;

thread_local! {
    /// Every E0309 of the flows a test checked, of which [`super::unused`]
    /// makes the first.
    static UNUSED: std::cell::RefCell<Vec<Diagnostic>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Keeps every E0309 of the flow [`super::unused`] reads, for [`unused`].
pub(super) fn record(names: &BodyNames, unreached: &dyn Fn(&Binding) -> Option<Vec<Span>>, ast: &Ast) {
    let all = crate::names::body::unused(names, unreached).map(|(b, r)| unused_binding(b, ast, r));
    UNUSED.with(|u| u.borrow_mut().extend(all));
}

/// Every E0309 of the flow `f` with the body `body` (its input `x`), in
/// order: the name, whether it has the candidate `_`, and its notes. The
/// flow makes the first only, which the unit reports (§18.1).
fn unused(body: &str) -> Vec<(String, bool, usize)> {
    let src = format!("pub flow f(x: F32 at sample) -> F32 at sample {{\n{body}\n}}\n");
    UNUSED.with(|u| u.borrow_mut().clear());
    let a = crate::tests::check(&src);
    let all = UNUSED.with(|u| u.take());
    let first = all.iter().min_by_key(|d| d.order_in_file());
    assert_eq!(a.diagnostics.iter().collect::<Vec<_>>(), first.into_iter().collect::<Vec<_>>());
    let one = |d: &onsa_diag::Diagnostic| {
        assert_eq!(d.code, Code::E0309, "{d:?}");
        (d.found.clone().unwrap_or_default(), !d.fixes.is_empty(), d.notes.len())
    };
    all.iter().map(one).collect()
}

fn names(body: &str) -> Vec<String> {
    unused(body).into_iter().map(|(n, _, _)| n).collect()
}

#[test]
fn a_chain_nobody_reads_is_unused_and_its_head_has_no_candidate() {
    let chain = unused("  let a = x * 2.0\n  let b = a + 1.0\n  x");
    assert_eq!(chain, vec![("a".to_string(), false, 1), ("b".to_string(), true, 0)]);
    assert_eq!(names("  let a = x * 2.0\n  let b = a + 1.0\n  b"), Vec::<String>::new());
}

#[test]
fn a_diamond_is_reached_through_both_sides() {
    let diamond = "  let a = x * 2.0\n  let b = a + 1.0\n  let c = a - 1.0\n";
    assert_eq!(names(&format!("{diamond}  b * c")), Vec::<String>::new());
    assert_eq!(names(&format!("{diamond}  let d = b * c\n  x")), ["a", "b", "c", "d"]);
}

#[test]
fn a_ring_of_feedback_is_reached_only_from_the_output_or_a_root() {
    let ring = "  let a = prev~(^b)\n  let b = a + x\n";
    assert_eq!(names(&format!("{ring}  x")), ["a", "b"]);
    assert_eq!(names(&format!("{ring}  b")), Vec::<String>::new());
    assert_eq!(names(&format!("{ring}  let _ = a\n  x")), Vec::<String>::new());
}

#[test]
fn a_let_that_binds_no_name_is_a_root() {
    assert_eq!(names("  let a = x * 2.0\n  let _ = a\n  x"), Vec::<String>::new());
    assert_eq!(names("  let a = x * 2.0\n  let (_, _) = (a, x)\n  x"), Vec::<String>::new());
    // A part of a destructuring nothing reached reads.
    assert_eq!(names("  let (a, b) = (x, x * 2.0)\n  a"), ["b"]);
}

#[test]
fn a_read_in_the_body_of_a_par_is_a_read_of_its_let() {
    let par = "  let a = x * 2.0\n  let ys = par~ i in 0 ..< 2 {\n    a\n  }\n";
    assert_eq!(names(&format!("{par}  ys[0]")), Vec::<String>::new());
    assert_eq!(names(&format!("{par}  x")), ["a", "ys"]);
}

/// R-17, §11.5, S-1157: a call of a function that is not `rt` evaluated
/// after `init` is E0815 when a value is not a constant and a condition
/// decided after `init` selects its place (one at `init` hoists it there);
/// E0200 of constants only (W9-03), of a result that is not Copy (S-1160)
/// and in the body of a `par~` (W7-05 U3).
#[test]
fn a_call_that_is_not_rt_after_init_is_e0815_in_a_late_branch_and_e0200_else() {
    let head = "pub fn make(v: F32) -> F32 { v * 2.0 }
pub fn name_of(n: I32) -> Option[Str] { if n > 0 { Some(\"on\") } else { None } }
pub rt fn pick(o: Option[Str], x: F32) -> F32 { match o { Some(_) => x, None => 0.0 } }
pub flow f(x: F32 at sample, a: F32 at init, b: F32 at init, n: I32 at block, i: I32 at init) -> F32 at sample {\n";
    let cases = [
        ("if n != 0 { x * make(a) } else { x }", Some(Code::E0815)),
        ("if x > 0.0 { x * make(a) } else { x }", Some(Code::E0815)),
        ("if n != 0 && make(a) > 1.0 { x } else { 0.0 }", Some(Code::E0815)),
        ("if b > 0.0 { x * make(a) } else { x }", None),
        ("if n != 0 { x * make(2.0) } else { x }", Some(Code::E0200)),
        ("pick(name_of(i), x)", Some(Code::E0200)),
        ("(par~ k in 0 ..< 2 { x * make(a) })[0]", Some(Code::E0200)),
    ];
    for (body, code) in cases {
        let a = crate::tests::check(&format!("{head}  {body}\n}}\n"));
        let got: Vec<Code> = a.diagnostics.iter().map(|d| d.code).collect();
        assert_eq!(got, code.into_iter().collect::<Vec<_>>(), "{body}: {:?}", a.diagnostics);
    }
}
