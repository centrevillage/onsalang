//! The data a walk of the tests of a case gives (W7-19 U2a): the reasons a test is not run, its verdict, the calls it made
//! as events (what `data.rs` writes and the interpreter is compared with), and the tests of a case.

use super::flow::PanicAt;
use super::value::Value;

/// Why a test is not run on the evaluator: the one list of the reasons, which the data counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Skip {
    /// Views, buffers and the channels of an `In`, `Out` or `process_inplace` (W7-12): the layout of the C API.
    Layout,
    /// A statement that is no `let`, `var` or `assert` of this unit's forms.
    Statement,
    /// A test that calls no function a flow generated: nothing of the evaluator is compared.
    NoCall,
}

impl Skip {
    /// The word of the data (`tests/flow_ref/FORMAT.md`).
    pub fn name(self) -> &'static str {
        match self {
            Skip::Layout => "layout",
            Skip::Statement => "statement",
            Skip::NoCall => "nocall",
        }
    }
}

/// The panic of a test: of a call (its stage), or of the evaluation of a plain expression of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Panic {
    Call(PanicAt),
    Eval,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// What the test says holds (its asserts, or its panic when it is marked).
    Ok,
    /// A form the evaluator does not evaluate yet (the text of its `Fault::Unavailable`).
    Unavailable(&'static str),
    Skipped(Skip),
    /// The evaluator and the test disagree, or the evaluator made a mistake of its own (`Internal`).
    Failed(String),
}

#[derive(Debug)]
pub struct TestRun {
    pub name: String,
    pub asserts: usize,
    pub panic: Option<Panic>,
    pub verdict: Verdict,
    /// The calls of generated functions the test made before it stopped, in order (the data of `tests/flow_ref/`).
    pub events: Vec<Event>,
}

/// Values by the name of the input they are given to: the fields of a `Config` or `Params`, or the columns of `sample` inputs.
pub type Named<T> = Vec<(String, T)>;

/// The leaves of the output of a call, from its type (a call of no frames has no value to tell them by): the path of each
/// (`.l` or empty) and its channels.
pub type Shape = Vec<(String, Option<usize>)>;

/// What a call of `process` or `render` was given (`frames` only of a flow with no `sample` input) and gave, a value for
/// each frame; a call that panicked gave nothing.
#[derive(Debug)]
pub struct Run {
    /// The leaves of one output frame: for each field of a struct output (`.l`, else none) its channels, when it is an array.
    pub shape: Shape,
    pub config: Named<Value>,
    pub params: Named<Value>,
    pub frames: Option<usize>,
    pub inputs: Named<Vec<Value>>,
    pub outs: Option<Vec<Value>>,
}

/// A call of a generated function; a state is named by its place in the order the test made them.
#[derive(Debug)]
pub enum Event {
    Init { state: usize, flow: String, sample_rate: f32, config: Named<Value> },
    Process { state: usize, run: Run },
    Render { flow: String, sample_rate: f32, run: Run },
    Reset { state: usize },
}

/// The tests of a case, and what its lowering did: a case that does not lower is waiting (the list of §8.5).
#[derive(Debug)]
pub struct CaseRun {
    pub tests: Vec<TestRun>,
    pub lowered: bool,
    pub e0200: bool,
}
