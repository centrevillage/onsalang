//! Tests of the lift into a `let` (§11.5, S-1172): the name of the new
//! `let`, which no name of the body, of the heading or of the module has;
//! where it is inserted (right before the statement, at the indent of its
//! first line); and the forms where it is not made (a binding of an arm
//! read, the body of a `par` / `par~`).

use onsa_diag::{Code, Diagnostic};

use crate::tests::check;

const HEAD: &str = "pub flow acc(x: F32 at sample) -> F32 at sample {\n  let y = x + prev~(^y)\n  y\n}\n\n\
pub rt fn pair_sum(xs: [F32; 2]) -> F32 {\n  xs[0] + xs[1]\n}\n\n";

/// The one diagnostic of `HEAD` and `src`, and the text of both.
fn the_error(src: &str) -> (Diagnostic, String) {
    let text = format!("{HEAD}{src}");
    let a = check(&text);
    let [d] = &a.diagnostics[..] else { panic!("one diagnostic expected: {:?}\n{text}", a.diagnostics) };
    (d.clone(), text)
}

/// Whether a candidate is the lift into a `let` (the one that inserts a
/// `let`).
fn is_lift(fix: &onsa_diag::Fix) -> bool {
    fix.edits().iter().any(|e| e.replace.starts_with("let "))
}

/// The text after the lift candidate of the one error of `src`, which has
/// the code `code`; and that text has no diagnostic.
fn lifted(src: &str, code: Code) -> String {
    let (d, text) = the_error(src);
    assert_eq!(d.code, code, "{src}");
    let [fix] = &d.fixes.iter().filter(|f| is_lift(f)).collect::<Vec<_>>()[..] else {
        panic!("one lift expected: {:?}", d.fixes)
    };
    let after = onsa_diag::apply_text(&text, &fix.edits().iter().collect::<Vec<_>>()).expect("the candidate applies");
    let again = check(&after);
    assert!(again.diagnostics.is_empty(), "{:?}\n{after}", again.diagnostics);
    after
}

/// The candidates of the one error of `src`: its code, the number of its
/// candidates and of its lifts.
fn kinds(src: &str) -> (Code, usize, usize) {
    let (d, _) = the_error(src);
    (d.code, d.fixes.len(), d.fixes.iter().filter(|f| is_lift(f)).count())
}

#[test]
fn the_name_is_none_of_the_body_the_heading_and_the_module() {
    // `prev_0` a parameter, `prev_1` a `let`, `prev_2` a function of the
    // module, `prev_3` the index of a `par~`, `prev_4` a binding of an arm
    let src = "pub fn prev_2(v: F32) -> F32 { v }

pub flow f(prev_0: F32 at sample, c: Bool at sample) -> F32 at sample {
  let prev_1 = prev_0 * 2.0
  let ys = par~ prev_3 in 0 ..< 2 { prev~(prev_0 * F32.round_from(prev_3)) }
  let o: Option[F32] = if prev_0 > 2.0 { Some(prev_0) } else { None }
  let z = match o { Some(prev_4) => prev_4, None => 0.0 }
  if c { prev~(prev_1) } else { ys[0] + z }
}
";
    let want = src.replace("  if c { prev~(prev_1) }", "  let prev_5 = prev~(prev_1)\n  if c { prev_5 }");
    assert_eq!(lifted(src, Code::E0811), format!("{HEAD}{want}"));
}

#[test]
fn the_name_is_of_the_kind_of_the_node() {
    // a flow instance is named after its flow, a `par~` is `par`
    let src = "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  if c { acc~(x) } else { 0.0 }
}
";
    let want = src.replace("  if c { acc~(x) }", "  let acc_0 = acc~(x)\n  if c { acc_0 }");
    assert_eq!(lifted(src, Code::E0811), format!("{HEAD}{want}"));
    let src = "pub flow f(x: F32 at sample) -> Bool at sample {
  x > 0.0 && pair_sum(par~ i in 0 ..< 2 { prev~(x * F32.round_from(i)) }) > 1.0
}
";
    let want = "pub flow f(x: F32 at sample) -> Bool at sample {
  let par_0 = par~ i in 0 ..< 2 { prev~(x * F32.round_from(i)) }
  x > 0.0 && pair_sum(par_0) > 1.0
}
";
    assert_eq!(lifted(src, Code::E0806), format!("{HEAD}{want}"));
}

#[test]
fn the_let_stands_right_before_the_statement_at_the_indent_of_its_first_line() {
    // the output of several lines, at an indent of 4: the thing is on a
    // later line of the statement, which alone changes
    let src = "pub flow f(x: F32 at sample, k: U32 at sample) -> F32 at sample {
    let a = x * 2.0
    match k {
      0 => a + prev~(x),
      _ => a,
    }
}
";
    let want =
        src.replace("    match k {", "    let prev_0 = prev~(x)\n    match k {").replace("a + prev~(x)", "a + prev_0");
    assert_eq!(lifted(src, Code::E0811), format!("{HEAD}{want}"));
    // a `let` of several lines, after another `let`: before it, not before
    // the first statement
    let src = "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let b = x * 2.0
  let a = if c {
    acc~(x)
  } else {
    b
  }
  a + b
}
";
    let want = src.replace("  let a = if c {\n    acc~(x)", "  let acc_0 = acc~(x)\n  let a = if c {\n    acc_0");
    assert_eq!(lifted(src, Code::E0811), format!("{HEAD}{want}"));
}

#[test]
fn a_thing_that_reads_a_previous_value_is_moved() {
    // `^y` is read before its `let` too (§11.2)
    let src = "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  let y = if c { prev~(^y) } else { x }
  y
}
";
    let want = src.replace("  let y = if c { prev~(^y) }", "  let prev_0 = prev~(^y)\n  let y = if c { prev_0 }");
    assert_eq!(lifted(src, Code::E0811), format!("{HEAD}{want}"));
}

#[test]
fn no_lift_where_the_let_would_not_see_what_the_thing_reads_or_would_leave_a_replication() {
    let opt = "let o: Option[F32] = if x > 2.0 { Some(x) } else { None }";
    // a branch that reads a binding of its arm: the `~` only
    let arm = format!(
        "pub flow f(x: F32 at sample) -> F32 at sample {{\n  {opt}\n  match o {{\n    Some(v) => prev~(v),\n    None => 0.0,\n  }}\n}}\n"
    );
    assert_eq!(kinds(&arm), (Code::E0811, 1, 0));
    // a guard that reads one: no candidate
    let guard = format!(
        "pub flow f(x: F32 at sample) -> F32 at sample {{\n  {opt}\n  match o {{\n    Some(v) if prev~(v) > 0.5 => v,\n    _ => 0.0,\n  }}\n}}\n"
    );
    assert_eq!(kinds(&guard), (Code::E0811, 0, 0));
    // in the body of a `par~`: a branch has the `~` only, a right of `&&`
    // nothing, though they read no index
    let branch = "pub flow f(x: F32 at sample, c: Bool at sample) -> [F32; 2] at sample {
  par~ i in 0 ..< 2 { if c { acc~(x) } else { F32.round_from(i) } }
}
";
    assert_eq!(kinds(branch), (Code::E0811, 1, 0));
    let right = "pub flow f(x: F32 at sample) -> [Bool; 2] at sample {
  par~ i in 0 ..< 2 { x > F32.round_from(i) && acc~(x) > 1.0 }
}
";
    assert_eq!(kinds(right), (Code::E0806, 0, 0));
    // in the body of a `par`, which is itself the E0811 of a `par` with
    // state (§11.5), the first by place (§18.1): its one candidate the `~`
    let par = "pub flow f(x: F32 at sample, c: Bool at sample) -> [F32; 2] at sample {
  par i in 0 ..< 2 { if c { acc~(x) } else { F32.round_from(i) } }
}
";
    assert_eq!(kinds(par), (Code::E0811, 1, 0));
}

#[test]
fn under_a_replication_are_its_body_and_its_range() {
    // of the AST alone: the walk reports the E0811 of a `par` with state
    // before the things of its body
    let text = "pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {
  wrap(prev~(x), par i in 0 ..< acc~(x) { acc~(x) }, par~ j in 0 ..< 2 { lp~(x) })
}
";
    let parsed = onsa_syntax::parse(onsa_diag::FileId(0), text);
    let ast = &parsed.ast;
    let find = |src: &str, nth: usize| {
        let ids = (0..ast.exprs.len() as u32).map(onsa_syntax::ast::ExprId);
        let mut ids = ids.filter(|&e| ast.expr(e).span.text_in(text) == src);
        ids.nth(nth).unwrap_or_else(|| panic!("no {src} {nth}"))
    };
    let root = find(&text[text.find("wrap(").unwrap()..text.find(" })\n").unwrap() + 3], 0);
    assert_eq!(super::under_par(ast, root, find("prev~(x)", 0)), Some(false));
    assert_eq!(super::under_par(ast, root, find("acc~(x)", 0)), Some(true), "the range of a `par`");
    assert_eq!(super::under_par(ast, root, find("acc~(x)", 1)), Some(true), "the body of a `par`");
    assert_eq!(super::under_par(ast, root, find("lp~(x)", 0)), Some(true), "the body of a `par~`");
    let par = find(&text[text.find("par~ j").unwrap()..text.find(" })\n").unwrap() + 2], 0);
    assert_eq!(super::under_par(ast, root, par), Some(false), "a `par~` itself is not under it");
}

#[test]
fn the_name_of_a_flow_that_ends_with_an_underscore_has_no_double_underscore() {
    // `foo__0` would be E0320 (§2.3), a name-stage error left by the fix
    let src = "pub flow foo_(x: F32 at sample) -> F32 at sample {\n  x\n}\n\n\
pub flow f(x: F32 at sample, c: Bool at sample) -> F32 at sample {\n  if c { foo_~(x) } else { 0.0 }\n}\n";
    let after = lifted(src, Code::E0811);
    assert!(after.contains("let foo_0 = foo_~(x)"), "{after}");
}

/// The lift of a chain out of a branch computes it on the ticks of its
/// frame (§11.9), which its title names; of the `sample` of the body, as
/// of a call with no modifier, `every sample`.
#[test]
fn the_lift_of_a_chain_names_the_tick_it_runs_on() {
    for (chain, per) in [
        ("lp~(p).down~(2) at sample", "tick of `sample / 2`"),
        ("lp~(p).up~(2).down~(4) at sample", "tick of `sample / 2`"),
        ("lp~(p).down~(2).up~(2)", "sample"),
        ("lp~(p)", "sample"),
    ] {
        let src = format!(
            "pub flow lp(x: F32 at sample) -> F32 at sample {{\n  x\n}}\n\n\
pub flow f(p: F32 at block, c: Bool at sample) -> F32 at sample {{\n  if c {{ {chain} }} else {{ 0.0 }}\n}}\n"
        );
        let (d, _) = the_error(&src);
        assert_eq!(d.code, Code::E0811, "{chain}");
        let title = format!("compute it on every {per} in a new `let lp_0`");
        assert!(d.fixes.iter().any(|f| f.title().starts_with(&title)), "{chain}: {:?}", d.fixes);
    }
}

/// A delay counts the ticks of its first argument (§11.4), not walked when
/// it is in error (S-1189): its lift names no tick.
#[test]
fn the_lift_of_a_delay_names_no_tick() {
    let src = "pub flow f(p: F32 at block, c: Bool at sample) -> F32 at sample {\n  if c { prev~(p at (sample / 4)) at sample } else { 0.0 }\n}\n";
    let (d, _) = the_error(src);
    assert_eq!(d.code, Code::E0811);
    let title = "compute it in a new `let prev_0` before this statement";
    assert!(d.fixes.iter().any(|f| f.title() == title), "{:?}", d.fixes);
}
