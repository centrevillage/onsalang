//! The table of values of the events in `par~`, `par`, `if~` and `match~` (`par_arm_values.md`; §11.5, §11.11, §11.3, §11.10, §11.4): each case is the body of a flow `top` of three `sample` inputs (`x`, `y`, `c`) with the shared parts
//! before it, and the output by hand from the text (`手で出した期待`). The evaluator runs each; a case it stops at (`Unavailable`) is counted, never dropped, and one that gives other values fails.

use super::expr_tests::{def_named, with_checked};
use super::flow::{Instance, Outcome};
use super::sema_view::View;
use super::value::{IntKind, Value};

const TABLE: &str = include_str!("par_arm_values.md");
/// The table of the chains (W7-17 U4: `when~` and `reset_if~` on a call with events, the ratios, the blocks, several events in one stage, the order of the receivers, the twins, the readings S-1251 decides), the same form.
const CHAINS: &str = include_str!("chain_event_values.md");

struct Case {
    id: String,
    body: String,
    inputs: Vec<(String, Vec<i128>)>,
    want: Vec<i128>,
}

fn numbers(s: &str) -> Vec<i128> {
    s.split_whitespace().map(|w| w.parse().unwrap_or_else(|_| panic!("not a number: {w}"))).collect()
}

/// The shared parts, and the cases of the `###` sections: the block of code, the line `- 入力: x = .., c = ..` and the line `- 手で出した期待: ..`.
fn cases(text: &str) -> (String, Vec<Case>) {
    let code = |s: &str| s.split("```onsa\n").nth(1).and_then(|c| c.split("```").next()).unwrap_or("").to_string();
    let common = code(text.split("## 共通の部品").nth(1).unwrap_or(""));
    let mut out = Vec::new();
    for part in text.split("\n### ").skip(1) {
        let (id, rest) = part.split_once('\n').unwrap_or((part, ""));
        let line = |key: &str| rest.lines().find(|l| l.starts_with(key)).map(|l| l[key.len()..].trim().to_string());
        let inputs = line("- 入力: ")
            .unwrap_or_default()
            .split("、")
            .filter(|w| !w.is_empty())
            .map(|w| {
                let (n, v) = w.split_once('=').unwrap_or_else(|| panic!("an input without `=`: {w}"));
                (n.trim().to_string(), numbers(v))
            })
            .collect();
        let want = numbers(line("- 手で出した期待: ").expect("an expectation").trim_matches('`'));
        let id = id.split('（').next().unwrap_or(id).trim().to_string();
        out.push(Case { id, body: code(rest), inputs, want });
    }
    (common, out)
}

/// The outputs of `top` over the columns, or why the evaluator did not run it.
fn run(common: &str, case: &Case) -> Result<Vec<i128>, String> {
    let src = format!(
        "{common}\nflow top(x: U32 at sample, y: U32 at sample, c: U32 at sample) -> U32 at sample {{\n{}\n}}\n",
        case.body
    );
    let frames = case.want.len();
    let given: Vec<(String, Vec<i128>)> = ["x", "y", "c"]
        .iter()
        .map(|n| {
            let col = case.inputs.iter().find(|(m, _)| m == n).map(|(_, v)| v.clone());
            (n.to_string(), col.unwrap_or_else(|| vec![0; frames]))
        })
        .collect();
    with_checked(&src, false, move |a| {
        let view = View::new(a);
        let cols: Vec<(String, Vec<Value>)> =
            given.iter().map(|(n, v)| (n.clone(), v.iter().map(|k| Value::int(IntKind::U32, *k)).collect())).collect();
        let ins: Vec<(&str, &[Value])> = cols.iter().map(|(n, v)| (n.as_str(), v.as_slice())).collect();
        match Instance::render(
            view,
            def_named(a, "top"),
            8.0,
            &super::flow::Call { inputs: &ins, ..Default::default() },
            None,
        ) {
            Ok(Outcome::Ok(outs)) => Ok(outs
                .iter()
                .map(|v| match v {
                    Value::Int(_, n, _) => *n,
                    _ => -1,
                })
                .collect()),
            Ok(Outcome::Panic { at, stop }) => Err(format!("panic {at:?} {:?}", stop.fault)),
            Err(stop) => Err(format!("{:?}", stop.fault)),
        }
    })
}

/// The cases that agree, those the evaluator does not run (with why), and those that differ.
pub(super) fn report(table: &str, take: &dyn Fn(&str) -> bool) -> (Vec<String>, Vec<(String, String)>, Vec<String>) {
    let (common, all) = cases(table);
    let (mut passed, mut stopped, mut failed) = (Vec::new(), Vec::new(), Vec::new());
    for case in all.iter().filter(|c| take(&c.id)) {
        match run(&common, case) {
            Ok(got) if got == case.want => passed.push(case.id.clone()),
            Ok(got) => failed.push(format!("{}: got {got:?}, want {:?}", case.id, case.want)),
            Err(why) => stopped.push((case.id.clone(), why)),
        }
    }
    (passed, stopped, failed)
}

#[test]
fn the_cases_of_par_par_and_the_arms_run_on_the_evaluator_with_the_values_written_by_hand() {
    let (passed, stopped, failed) = report(TABLE, &|_| true);
    assert!(failed.is_empty(), "{failed:#?}");
    // P1-3 is a `.when~` on a call that takes events (M1, W7-17 U4): it runs with the others.
    assert!(stopped.is_empty(), "{stopped:#?}");
    assert_eq!(passed.len(), 22, "{passed:?}");
}

#[test]
fn the_cases_of_the_chains_run_on_the_evaluator_with_the_values_written_by_hand() {
    let (passed, stopped, failed) = report(CHAINS, &|_| true);
    assert!(failed.is_empty(), "{failed:#?}");
    assert!(stopped.is_empty(), "{stopped:#?}");
    assert_eq!(passed.len(), 72, "{passed:?}");
}
