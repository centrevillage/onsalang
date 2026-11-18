//! The calls a test made on the reference evaluator, written as a `test` of Onsa (W7-19 U3): the input of a call by the
//! bits of its floats (`F32.from_bits(..)`), and after it an `assert` for each leaf and each frame of what it gave (the
//! bits of a float by `to_bits()`, a NaN by `x != x` of §3.4, an integer or a `Bool` by `==`). A call that panicked has
//! none: the printed test ends there, and the interpreter has to panic at that call. The line of each statement is kept
//! with the call and the leaf it is of, so that a failure of the interpreter goes back to them (`Origin`).
//!
//! The names are written as the test writes them (the last word of the name of the flow: the test is appended to the file
//! of the original, where that name is in scope).

use onsa_tests::flow_ref::data::leaves;
use onsa_tests::flow_ref::value::Value;
use onsa_tests::flow_ref::walk::{Event, Named, Panic, Run, TestRun};

/// The call (`#2 process 0`) and, for an `assert`, the leaf and the frame of the output it is about (`out[1] frame 3`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Origin {
    pub call: String,
    pub assert: Option<String>,
}

/// A printed test: its name, its text, the origin of each line of the text, and the call it has to panic at (the last,
/// when a call of the original panicked).
#[derive(Debug)]
pub struct Printed {
    pub name: String,
    pub text: String,
    pub lines: Vec<Origin>,
    pub panic_call: Option<String>,
}

/// The prefix of the names of the printed tests: the filter that selects them from the tests of the original.
pub const PREFIX: &str = "flow_ref#";

#[derive(Default)]
struct Writer {
    text: String,
    lines: Vec<Origin>,
}

impl Writer {
    fn line(&mut self, text: String, call: &str, assert: Option<String>) {
        self.text += &text;
        self.text.push('\n');
        self.lines.push(Origin { call: call.to_string(), assert });
    }
}

/// The test `t` (the `index`-th of the case) written as a test of Onsa, or why it is not (a form no literal writes).
pub fn print_test(index: usize, t: &TestRun) -> Result<Printed, String> {
    let name = format!("{PREFIX}{index:04} {}", t.name.replace(['"', '\\'], "_"));
    let mut w = Writer::default();
    w.line(format!("test \"{name}\" {{"), "", None);
    let mut flows: Vec<&str> = Vec::new();
    // A state no later call reads is bound to `_` (E0309, §5.1).
    let read = |state: usize, from: usize| {
        t.events[from..]
            .iter()
            .any(|ev| matches!(ev, Event::Process { state: s, .. } | Event::Reset { state: s } if *s == state))
    };
    for (e, ev) in t.events.iter().enumerate() {
        let call = label(e, ev);
        match ev {
            Event::Init { state, flow, sample_rate, config } => {
                let f = last(flow);
                let mut args = if config.is_empty() { Vec::new() } else { vec![literal(f, "Config", config)?] };
                args.push(value(&Value::F32(*sample_rate))?);
                let binding = if read(*state, e) { format!("var s{state}") } else { "let _".into() };
                w.line(format!("{binding} = {f}.init({})", args.join(", ")), &call, None);
                flows.push(f);
            }
            Event::Reset { state } => {
                let f = flows.get(*state).ok_or("a state that was not made")?;
                w.line(format!("{f}.reset(inout s{state})"), &call, None);
            }
            Event::Process { state, run } => {
                let f = flows.get(*state).ok_or("a state that was not made")?;
                process(&mut w, (e, &call), (f, *state), run)?;
            }
            Event::Render { flow, sample_rate, run } => render(&mut w, (e, &call), last(flow), *sample_rate, run)?,
        }
    }
    w.line("}".into(), "", None);
    let panic_call =
        t.events.last().filter(|_| matches!(t.panic, Some(Panic::Call(_)))).map(|ev| label(t.events.len() - 1, ev));
    Ok(Printed { name, text: w.text, lines: w.lines, panic_call })
}

/// The call of an event as the report names it: its place in the test and what it is.
fn label(e: usize, ev: &Event) -> String {
    match ev {
        Event::Init { state, flow, .. } => format!("#{e} init {state} {flow}"),
        Event::Reset { state } => format!("#{e} reset {state}"),
        Event::Process { state, .. } => format!("#{e} process {state}"),
        Event::Render { flow, .. } => format!("#{e} render {flow}"),
    }
}

/// The name of a flow as a test writes it: the last word of its path.
fn last(flow: &str) -> &str {
    flow.rsplit('.').next().unwrap_or(flow)
}

/// A `Config` or a `Params` of the flow `f`: `f.Config { k: v, .. }`.
fn literal(f: &str, ty: &str, items: &Named<Value>) -> Result<String, String> {
    let fields = items.iter().map(|(n, v)| Ok(format!("{n}: {}", value(v)?))).collect::<Result<Vec<_>, String>>()?;
    Ok(format!("{f}.{ty} {{ {} }}", fields.join(", ")))
}

/// A scalar as the program writes it: a float by its bits, an integer or a `Bool` as it is.
fn value(v: &Value) -> Result<String, String> {
    match v {
        Value::F32(x) => Ok(format!("F32.from_bits({:#010x})", x.to_bits())),
        Value::F64(x) => Ok(format!("F64.from_bits({:#018x})", x.to_bits())),
        Value::Int(_, n, _) if *n > i64::MIN as i128 => Ok(n.to_string()),
        Value::Bool(b) => Ok(b.to_string()),
        _ => Err("a value that is no float, integer or Bool".into()),
    }
}

/// The zero of the type of a leaf, as the buffer of an output starts.
fn zero(ty: &str) -> Result<&'static str, String> {
    match ty {
        "F32" | "F64" => Ok("0.0"),
        "Bool" => Ok("false"),
        t if t.len() <= 3 && (t.starts_with('I') || t.starts_with('U')) => Ok("0"),
        _ => Err(format!("an output of the type {ty}")),
    }
}

/// The `let` of the columns the call is given and the argument they make (none, the column, or an `In`).
fn inputs(w: &mut Writer, (e, call): (usize, &str), f: &str, run: &Run) -> Result<Vec<String>, String> {
    let mut names = Vec::new();
    for (k, (_, column)) in run.inputs.iter().enumerate() {
        let ty = run.types.inputs.get(k).ok_or("an input with no type")?;
        let items = column.iter().map(value).collect::<Result<Vec<_>, _>>()?;
        w.line(format!("let i{e}_{k}: [{ty}; {}] = [{}]", items.len(), items.join(", ")), call, None);
        names.push(format!("i{e}_{k}"));
    }
    Ok(match &run.inputs[..] {
        [] => Vec::new(),
        [_] => names,
        many => {
            let fields = many.iter().zip(&names).map(|((n, _), v)| format!("{n}: {v}")).collect::<Vec<_>>();
            vec![format!("{f}.In {{ {} }}", fields.join(", "))]
        }
    })
}

fn process(w: &mut Writer, (e, call): (usize, &str), (f, state): (&str, usize), run: &Run) -> Result<(), String> {
    let mut args = vec![format!("inout s{state}")];
    if !run.params.is_empty() {
        args.push(literal(f, "Params", &run.params)?);
    }
    args.extend(inputs(w, (e, call), f, run)?);
    let frames = run.frames.ok_or("a process with no frames")?;
    let mut buffers = Vec::new();
    for (field, ((path, channels), ty)) in run.shape.iter().zip(&run.types.leaves).enumerate() {
        let (zero, n) = (zero(ty)?, frames);
        let (shape, init) = match channels {
            Some(k) => (format!("[[{ty}; {n}]; {k}]"), format!("[[{zero}; {n}]; {k}]")),
            None => (format!("[{ty}; {n}]"), format!("[{zero}; {n}]")),
        };
        w.line(format!("var o{e}_{field}: {shape} = {init}"), call, None);
        buffers.push(format!("{}: o{e}_{field}", path.trim_start_matches('.')));
    }
    args.push(match &run.shape[..] {
        [(path, _)] if path.is_empty() => format!("inout o{e}_0"),
        _ => format!("inout {f}.Out {{ {} }}", buffers.join(", ")),
    });
    w.line(format!("{f}.process({})", args.join(", ")), call, None);
    for l in leaves(run) {
        let channel = l.channel.map(|k| format!("[{k}]")).unwrap_or_default();
        for (i, v) in l.frames.iter().enumerate() {
            let place = format!("o{e}_{}{channel}[{i}]", l.field);
            w.line(format!("assert {}", expect(&place, v)?), call, Some(format!("out{} frame {i}", l.path)));
        }
    }
    Ok(())
}

fn render(w: &mut Writer, (e, call): (usize, &str), f: &str, sample_rate: f32, run: &Run) -> Result<(), String> {
    let mut args = Vec::new();
    if !run.config.is_empty() {
        args.push(literal(f, "Config", &run.config)?);
    }
    if !run.params.is_empty() {
        args.push(literal(f, "Params", &run.params)?);
    }
    args.extend(inputs(w, (e, call), f, run)?);
    args.extend(run.frames.map(|n| n.to_string()));
    args.push(value(&Value::F32(sample_rate))?);
    let mut asserts = Vec::new();
    for l in leaves(run) {
        let path = if l.path.starts_with('.') { l.path.clone() } else { format!(".out{}", l.path) };
        for (i, v) in l.frames.iter().enumerate() {
            let place = format!("o{e}{path}[{i}]");
            asserts.push((format!("assert {}", expect(&place, v)?), format!("out{} frame {i}", l.path)));
        }
    }
    let binding = if asserts.is_empty() { "let _".to_string() } else { format!("let o{e}") };
    w.line(format!("{binding} = {f}.render({})", args.join(", ")), call, None);
    asserts.into_iter().for_each(|(text, at)| w.line(text, call, Some(at)));
    Ok(())
}

/// What the evaluator gave at `place`, as the condition of an `assert`.
fn expect(place: &str, v: &Value) -> Result<String, String> {
    Ok(match v {
        Value::F32(x) if x.is_nan() => format!("{place} != {place}"),
        Value::F64(x) if x.is_nan() => format!("{place} != {place}"),
        Value::F32(x) => format!("{place}.to_bits() == {:#010x}", x.to_bits()),
        Value::F64(x) => format!("{place}.to_bits() == {:#018x}", x.to_bits()),
        v => format!("{place} == {}", value(v)?),
    })
}
