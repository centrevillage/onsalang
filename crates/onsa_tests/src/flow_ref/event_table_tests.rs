//! The reader of the table of values of the events (`event_values.md`) and the run of each case on the evaluator (`Instance::process_events`), for `event_tests.rs`.

use super::expr_tests::{def_named, with_checked};
use super::flow::Instance;
use super::scalar::Fault;
use super::sema_view::View;
use super::value::{IntKind, Value};

/// What a run of the cases came to: their ids by what happened (`count` is all of them).
#[derive(Default)]
pub(super) struct Report {
    pub count: usize,
    pub passed: Vec<String>,
    pub gap: Vec<String>,
    pub unavailable: Vec<(String, &'static str)>,
    pub failed: Vec<String>,
}

struct Case {
    id: String,
    code: String,
    lines: Vec<String>,
}

/// The cases of the table: the `###` sections with their block of code and their lines `- name: value`.
fn cases(text: &str) -> (String, Vec<Case>) {
    let (mut common, mut out) = (String::new(), Vec::new());
    for part in text.split("\n### ").skip(1) {
        let (id, rest) = part.split_once('\n').unwrap_or((part, ""));
        let code = rest.split("```onsa\n").nth(1).and_then(|c| c.split("```").next()).unwrap_or("");
        let lines = rest.lines().filter(|l| l.starts_with("- ")).map(str::to_string).collect();
        out.push(Case { id: id.trim().to_string(), code: code.to_string(), lines });
    }
    if let Some(head) = text.split("## 共通の部品").nth(1) {
        common = head.split("```onsa\n").nth(1).and_then(|c| c.split("```").next()).unwrap_or("").to_string();
    }
    (common, out)
}

fn ints(s: &str) -> Vec<i128> {
    s.split_whitespace().map(|w| w.parse().unwrap_or_else(|_| panic!("not a number: {w}"))).collect()
}

/// The value of the type named `ty` that the integer `n` stands for (`Bool` is 0 and 1 in the table).
fn value(ty: &str, n: i128) -> Value {
    match ty {
        "Bool" => Value::Bool(n != 0),
        _ => Value::int(IntKind::U32, n),
    }
}

fn text(v: &Value) -> String {
    match v {
        Value::Int(_, n, _) => n.to_string(),
        Value::Bool(b) => u8::from(*b).to_string(),
        Value::Tuple(vs, _) => format!("({})", vs.iter().map(text).collect::<Vec<_>>().join(",")),
        other => format!("{other:?}"),
    }
}

/// The value of a line: what is between the backticks.
fn field<'l>(lines: &'l [String], key: &str) -> Option<&'l str> {
    let line = lines.iter().find(|l| l.starts_with(key))?;
    line.split_once(": ").map(|(_, v)| v.trim().trim_matches('`'))
}

/// The inputs of the flow `name` of the code: `(name, type, clock)`.
fn heading(code: &str, name: &str) -> Vec<(String, String, String)> {
    let head =
        code.lines().find(|l| l.starts_with(&format!("flow {name}("))).unwrap_or_else(|| panic!("no flow {name}"));
    let args = head.split_once('(').and_then(|(_, r)| r.split_once(')')).map_or("", |(a, _)| a);
    let one = |a: &str| {
        let (n, rest) = a.split_once(':')?;
        let (ty, clock) = rest.split_once(" at ")?;
        Some((n.trim().to_string(), ty.trim().to_string(), clock.trim().to_string()))
    };
    args.split(", ").filter_map(one).collect()
}

/// `(position,'name',value)` triples of the table.
fn events(line: &str) -> Vec<(usize, String, i128)> {
    line.split(") (")
        .map(|t| t.trim_matches(|c: char| "() ".contains(c)).to_string())
        .map(|t| {
            let parts: Vec<&str> = t.split(',').collect();
            (parts[0].parse().unwrap(), parts[1].trim_matches('\'').to_string(), parts[2].parse().unwrap())
        })
        .collect()
}

fn run_one(common: &str, case: &Case) -> Result<Result<(), String>, Fault> {
    // The flow the case runs is the last one its code declares.
    let name = case
        .code
        .lines()
        .filter_map(|l| l.strip_prefix("flow "))
        .filter_map(|l| l.split('(').next())
        .next_back()
        .expect("a flow")
        .to_string();
    let src = format!("{common}\n{}", case.code);
    let given = heading(&case.code, &name);
    let line = |key: &str| field(&case.lines, key).map(str::to_string);
    let key = |k: &str| format!("- 入力 `{k}`");
    let frames: usize = field(&case.lines, "- フレーム").and_then(|f| f.trim().parse().ok()).expect("frames");
    let ev = line("- イベント（位置, 入力, 値。境界が渡す順）").map(|l| events(&l)).unwrap_or_default();
    let mut columns = Vec::new();
    for (n, ty, clock) in &given {
        if clock == "sample" {
            let col = line(&key(n)).expect("a column");
            columns.push((n.clone(), ints(&col).into_iter().map(|v| value(ty, v)).collect::<Vec<_>>()));
        }
    }
    let params: Vec<(String, Value)> = given
        .iter()
        .filter(|(_, _, c)| c == "block")
        .map(|(n, ty, _)| (n.clone(), value(ty, ints(&line("- `block` の入力 `").expect("a block input"))[0])))
        .collect();
    let events_in: Vec<(usize, String, Value)> = ev
        .iter()
        .map(|(p, n, v)| (*p, n.clone(), value(&given.iter().find(|g| g.0 == *n).expect("an input").1, *v)))
        .collect();
    let want_out = line("- 期待の出力: ");
    let want_events = line("- 期待の出力（位置, 値）: ");
    let id = case.id.clone();
    with_checked(&src, true, move |a| {
        let view = View::new(a);
        let params: Vec<(&str, Value)> = params.iter().map(|(n, v)| (n.as_str(), v.clone())).collect();
        let cols: Vec<(&str, &[Value])> = columns.iter().map(|(n, c)| (n.as_str(), c.as_slice())).collect();
        let mut me = match Instance::init(view, def_named(a, &name), 8.0, &[], None) {
            Ok(me) => me,
            Err(stop) => return Err(stop.fault),
        };
        let (outs, gave) = match me.process_events(&params, &cols, frames, &events_in, None) {
            Ok(r) => r,
            Err(stop) => return Err(stop.fault),
        };
        let mut bad = Vec::new();
        if let Some(w) = &want_out {
            let got = outs.iter().map(text).collect::<Vec<_>>().join(" ");
            (got != w.trim()).then(|| bad.push(format!("{id}: out {got} (want {})", w.trim())));
        }
        if let Some(w) = &want_events {
            let got = gave.iter().map(|(p, v)| format!("({p},{})", text(v))).collect::<Vec<_>>().join(" ");
            (got != w.trim()).then(|| bad.push(format!("{id}: events {got} (want {})", w.trim())));
        }
        Ok(if bad.is_empty() { Ok(()) } else { Err(bad.join("; ")) })
    })
}

/// Runs the cases of the table that `take` chooses.
pub(super) fn run_cases(text: &str, take: &dyn Fn(&str) -> bool) -> Report {
    let (common, all) = cases(text);
    let mut r = Report::default();
    for case in all.iter().filter(|c| take(&c.id)) {
        r.count += 1;
        if case.lines.iter().any(|l| l.contains("【字で決まらない】")) {
            r.gap.push(case.id.clone());
            continue;
        }
        if case.lines.iter().any(|l| l.contains(": `[")) {
            r.unavailable.push((case.id.clone(), "a case of arrays of inputs"));
            continue;
        }
        match run_one(&common, case) {
            Ok(Ok(())) => r.passed.push(case.id.clone()),
            Ok(Err(m)) => r.failed.push(m),
            Err(Fault::Unavailable(why)) => r.unavailable.push((case.id.clone(), why)),
            Err(other) => r.failed.push(format!("{}: {other:?}", case.id)),
        }
    }
    r
}
