//! The data of `tests/flow_ref/` (W7-19 U2c): what the evaluator gave on each `test` of a case of W1-09, written as text
//! (the form is `tests/flow_ref/FORMAT.md`). The data is made from the evaluator's output and compared with it at each run,
//! so a number or a reason that changes is a failure, never a silent drop (the head counts, the lines of skipped and
//! unavailable tests); the interpreter is compared with it later (U3). Floats are bits, a result that is a NaN is `nan`.

use std::fmt::Write;

use super::flow::PanicAt;
use super::value::Value;
use super::walk::{CaseRun, Event, Named, Panic, Run, TestRun, Verdict};

/// The numbers of the head of a file, and (added) of the `MANIFEST`: a case that is waiting counts 1.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    pub tests: usize,
    pub evaluated: usize,
    pub unavailable: usize,
    pub skipped: usize,
    pub waiting: usize,
}

impl Counts {
    pub fn add(&mut self, o: &Counts) {
        self.tests += o.tests;
        self.evaluated += o.evaluated;
        self.unavailable += o.unavailable;
        self.skipped += o.skipped;
        self.waiting += o.waiting;
    }

    fn show(&self) -> String {
        let Counts { tests, evaluated, unavailable, skipped, waiting } = self;
        format!("tests={tests} evaluated={evaluated} unavailable={unavailable} skipped={skipped} waiting={waiting}")
    }
}

/// The text of the file of the case read from `source` (its path), and its counts; `waiting` is whether the case is in
/// the list of things pending.
pub fn case_text(source: &str, run: &CaseRun, waiting: bool) -> (String, Counts) {
    let mut counts = Counts { tests: run.tests.len(), waiting: usize::from(waiting), ..Counts::default() };
    let mut body = String::new();
    for t in &run.tests {
        match t.verdict {
            Verdict::Ok => counts.evaluated += 1,
            Verdict::Unavailable(_) => counts.unavailable += 1,
            _ => counts.skipped += usize::from(matches!(t.verdict, Verdict::Skipped(_))),
        }
        body += &test_text(t);
    }
    (format!("# flow_ref 1 source={source} {}\n{body}", counts.show()), counts)
}

/// The `MANIFEST`: the lines and the counts of each file (by name, in order), and their sum. Not a hash: the data is
/// compared with the evaluator's output at each run.
pub fn manifest(files: &[(String, String, Counts)]) -> String {
    let mut sum = Counts::default();
    let mut out = String::from("# flow_ref MANIFEST, format 1 (made by UPDATE_GOLDEN=1, not by hand)\n");
    for (name, text, counts) in files {
        _ = writeln!(out, "file {name}.tsv rows={} {}", text.lines().count(), counts.show());
        sum.add(counts);
    }
    let rows: usize = files.iter().map(|(_, t, _)| t.lines().count()).sum();
    _ = writeln!(out, "total files={} rows={rows} {}", files.len(), sum.show());
    out
}

fn test_text(t: &TestRun) -> String {
    let name = t.name.replace(['\n', '\t'], " ");
    let mut s = match &t.verdict {
        Verdict::Unavailable(why) => return format!("? {name}\tunavailable {why}\n"),
        Verdict::Skipped(why) => return format!("- {name}\tskipped {}\n", why.name()),
        Verdict::Failed(m) => return format!("! {name}\tfailed {m}\n"),
        Verdict::Ok => format!("@ {name}\n"),
    };
    t.events.iter().for_each(|e| s += &event_text(e));
    match t.panic {
        Some(Panic::Eval) => s += "panic eval\n",
        Some(Panic::Call(PanicAt::Init)) => s += "panic init\n",
        Some(Panic::Call(PanicAt::Start)) => s += "panic start\n",
        Some(Panic::Call(PanicAt::Block)) => s += "panic block\n",
        Some(Panic::Call(PanicAt::Sample(n))) => _ = writeln!(s, "panic sample {n}"),
        None => {}
    }
    s
}

fn event_text(e: &Event) -> String {
    let rate = |sr: &f32| val(&Value::F32(*sr), false);
    match e {
        Event::Init { state, flow, sample_rate, config } => {
            format!("init {state} {flow} sr={}{}\n", rate(sample_rate), named(" cfg", config))
        }
        Event::Reset { state } => format!("reset {state}\n"),
        Event::Process { state, run } => format!("process {state}{}\n{}", run_text(run), out_rows(run)),
        Event::Render { flow, sample_rate, run } => {
            format!("render {flow} sr={}{}\n{}", rate(sample_rate), run_text(run), out_rows(run))
        }
    }
}

/// ` cfg k=v params k=v frames=n in x=[..]`: what a call is given, a part left out when it has none.
fn run_text(run: &Run) -> String {
    let frames = run.frames.map_or(String::new(), |n| format!(" frames={n}"));
    let columns = run.inputs.iter().map(|(n, c)| format!(" {n}=[{}]", list(c, false))).collect::<String>();
    let ins = if columns.is_empty() { String::new() } else { format!(" in{columns}") };
    format!("{}{}{frames}{ins}", named(" cfg", &run.config), named(" params", &run.params))
}

fn named(key: &str, items: &Named<Value>) -> String {
    let fields = items.iter().map(|(n, v)| format!(" {n}={}", val(v, false))).collect::<String>();
    if fields.is_empty() { String::new() } else { format!("{key}{fields}") }
}

/// A line for each leaf of the outputs (`run.shape`, so that a call of no frames has them too): `out=[..]` for a scalar,
/// `out[k]=` for a channel of an array, `out.f=` and `out.f[k]=` for a field of a struct output; a call that panicked
/// gave none.
fn out_rows(run: &Run) -> String {
    let Some(outs) = &run.outs else { return String::new() };
    let mut rows = String::new();
    for (i, (path, channels)) in run.shape.iter().enumerate() {
        let column: Vec<&Value> =
            if path.is_empty() { outs.iter().collect() } else { outs.iter().filter_map(|o| part(o, i)).collect() };
        let leaves = (0..channels.unwrap_or(1)).map(|k| match channels {
            Some(_) => (format!("{path}[{k}]"), column.iter().filter_map(|v| part(v, k)).collect::<Vec<_>>()),
            None => (path.clone(), column.clone()),
        });
        leaves.for_each(|(p, vs)| _ = writeln!(rows, "out{p}=[{}]", list(vs, true)));
    }
    rows
}

/// The field or the element `i` of a struct or an array.
fn part(v: &Value, i: usize) -> Option<&Value> {
    match v {
        Value::Struct(vs) | Value::Array(vs) => vs.get(i),
        _ => None,
    }
}

fn list<'v>(vs: impl IntoIterator<Item = &'v Value>, result: bool) -> String {
    vs.into_iter().map(|v| val(v, result)).collect::<Vec<_>>().join(" ")
}

/// A value as the data writes it: a float by its bits (`nan` for a result that is a NaN, §13.4), an integer in decimal,
/// `c<code point>`, `()`, `[..]`, `(..)`, `{..}` and `#<variant>(..)`.
fn val(v: &Value, result: bool) -> String {
    match v {
        Value::Int(_, n, _) => n.to_string(),
        Value::F32(x) if result && x.is_nan() => "nan".into(),
        Value::F32(x) => format!("{:#010x}", x.to_bits()),
        Value::F64(x) if result && x.is_nan() => "nan".into(),
        Value::F64(x) => format!("{:#018x}", x.to_bits()),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => format!("c{}", *c as u32),
        Value::Unit => "()".into(),
        Value::Tuple(vs, _) => format!("({})", list(vs, result)),
        Value::Array(vs) => format!("[{}]", list(vs, result)),
        Value::Struct(vs) => format!("{{{}}}", list(vs, result)),
        Value::Enum { tag, fields } => format!("#{tag}({})", list(fields, result)),
    }
}
