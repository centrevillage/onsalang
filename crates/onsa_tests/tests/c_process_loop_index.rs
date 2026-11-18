//! The indices of the sample loop of the generated `process` (spec §11.6, §14.2, §9.2; W7-08 U2/t: S-196).
//!
//! Written from the spec before the implementation (plan §8.5): the expected values are the ones the
//! spec fixes, never an output of the compiler. What the spec fixes, and so what is checked here:
//!
//! - §11.6: the lengths of all the `sample` inputs and outputs are compared once, at the start of
//!   `process`, before any state moves; and "サンプルループの中の入出力の `Span` への添字には検査を置かない
//!   （最初の比較が、それらの添字が範囲内であることを保証する）". So the sample loop of the generated
//!   `<name>__process` reads and writes the `Span`s with no checked index (`onsa_idx(`), for a single
//!   `Span`, for the channels of a planar `[Span[F32]; 2]` (a constant index of an array of two
//!   channels is in range by its type) and for the fields of a struct `In` and `Out`;
//! - §11.6: "サンプルの段から呼ぶ関数の中の添字は §9.2 のとおり検査する": the one-sample function
//!   `<name>__tick` and a user's `rt fn` that a flow calls keep their checked indices;
//! - the comparison of the lengths is still there, and before the loop.
//!
//! What the shape of the loop is (fixed by the task ticket and not by the spec): the inputs are read and
//! the outputs written through `<span>.ptr[<index>]` in a `for` loop whose variable is `i`, the index
//! being made from `i` (today `onsa_idx(i, <span>.len, ..)`, after S-196 `i` itself). The main property
//! (no `onsa_idx(` in the loop) does not depend on it; the positive controls do, so that an empty
//! extraction cannot pass.
//!
//! The text is made in memory (`onsa_driver::build_analyzed`), no file is written and no C compiler runs.
//! Not written here, because the spec does not say: where in the C file the functions are, the names of
//! the temporaries, whether the comparison is one condition or one per `Span` (only that a comparison is
//! before the loop).

use std::sync::OnceLock;

/// One package (`m`) with the three forms and the two controls: the flow bodies and `pick` index an
/// array at a run-time index, so that `tick` and the user's `rt fn` have a checked index that stays.
const SOURCE: &str = "\
pub struct Pair {
  l: F32,
  r: F32,
}

pub rt fn pick(xs: [F32; 4], i: U32) -> F32 {
  xs[i]
}

@export
pub flow mono(x: F32 at sample) -> F32 at sample {
  let a = [x, x * 2.0, x * 3.0, x * 4.0]
  a[U32.trunc_sat_from(x)] + pick(a, U32.trunc_sat_from(prev~(x)))
}

@export
pub flow planar(x: [F32; 2] at sample) -> [F32; 2] at sample {
  let a = [x[0], x[1], x[0] + x[1], x[0] - x[1]]
  [a[U32.trunc_sat_from(x[0])] + prev~(x[1]), pick(a, U32.trunc_sat_from(x[1])) + x[0]]
}

@export
pub flow duo(a: F32 at sample, b: F32 at sample) -> Pair at sample {
  let t = [a, b, a + b, a - b]
  Pair { l: t[U32.trunc_sat_from(a)] + prev~(b), r: pick(t, U32.trunc_sat_from(b)) }
}
";

const MANIFEST: &str = "[package]\nname = \"m\"\nedition = \"2026\"\n\n[export]\nprefix = \"t_\"\n\n\
    [targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"poison\"\nprovides = []\n";

/// What a form is: the name of its flow in the C file, the number of `Span` reads and writes of one
/// sample (the scalar channels of the inputs and of the outputs), and a name for the messages.
struct Form {
    what: &'static str,
    flow: &'static str,
    reads: usize,
    writes: usize,
}

const ONE_SPAN: Form = Form { what: "one Span in and one out", flow: "m__mono", reads: 1, writes: 1 };
const PLANAR: Form = Form { what: "planar [Span[F32]; 2] in and out", flow: "m__planar", reads: 2, writes: 2 };
const STRUCT_IO: Form =
    Form { what: "struct In (two fields) and Out (two fields)", flow: "m__duo", reads: 2, writes: 2 };

/// The generated C file of the package (host target, `panic = "poison"`), made once.
fn generated_c() -> &'static str {
    static C: OnceLock<String> = OnceLock::new();
    C.get_or_init(|| {
        let input = onsa_driver::PackageInput {
            manifest: Some(onsa_driver::ManifestSource {
                path: "onsa.toml".into(),
                text: MANIFEST.into(),
                form: onsa_driver::ManifestForm::File,
            }),
            files: vec![onsa_driver::SourceFile { path: "m.onsa".into(), text: SOURCE.into() }],
            ..Default::default()
        };
        let mut loaded = onsa_driver::Loaded::from_input(input).unwrap();
        let analyzed = onsa_driver::analyze_loaded(&mut loaded).unwrap();
        assert!(analyzed.diagnostics.is_empty(), "the source of the test is wrong: {:?}", analyzed.diagnostics);
        let out =
            onsa_driver::build_analyzed(&loaded, &analyzed, "host").unwrap_or_else(|_| panic!("the build failed"));
        let cs: Vec<&(String, String)> = out.files.iter().filter(|(n, _)| n.ends_with(".c")).collect();
        assert_eq!(cs.len(), 1, "one .c file expected in {:?}", out.files.iter().map(|f| &f.0).collect::<Vec<_>>());
        cs[0].1.clone()
    })
}

/// The definition of the C function `name`: from its first line (not indented, ends with `{`, has
/// ` name(`) to the closing line `}`. A prototype (ends with `;`), a call, and a function whose name only
/// starts with `name` (`name__guarded`) are not it.
fn definition<'a>(c: &'a str, name: &str) -> &'a str {
    let needle = format!(" {name}(");
    let mut found: Option<usize> = None;
    let mut offset = 0;
    for line in c.split_inclusive('\n') {
        if !line.starts_with(' ') && line.contains(&needle) && line.trim_end().ends_with('{') {
            assert!(found.is_none(), "two definitions of `{name}` in the C file");
            found = Some(offset);
        }
        offset += line.len();
    }
    let start = found.unwrap_or_else(|| panic!("no definition of `{name}` in the C file"));
    let rest = &c[start..];
    let end = rest.find("\n}\n").unwrap_or_else(|| panic!("the definition of `{name}` does not end"));
    &rest[..end + 2]
}

/// The lines of the body of the first `for` loop of the function at its own indentation (two spaces),
/// without the `for` line and the closing `}`.
fn loop_body(function: &str) -> String {
    let mut lines = function.lines().skip_while(|l| !l.starts_with("  for ("));
    assert!(lines.next().is_some(), "no `for` loop in:\n{function}");
    let body: Vec<&str> = lines.take_while(|l| *l != "  }").collect();
    assert!(!body.is_empty(), "the loop is empty in:\n{function}");
    body.join("\n")
}

/// The text of the sample loop of `<flow>__process` of a form.
fn process_loop(form: &Form) -> String {
    loop_body(definition(generated_c(), &format!("{}__process", form.flow)))
}

fn assert_unchecked(form: &Form) {
    let body = process_loop(form);
    let checked: Vec<&str> = body.lines().filter(|l| l.contains("onsa_idx(")).collect();
    assert!(
        checked.is_empty(),
        "the sample loop of `process` of the form `{}` has a checked index (§11.6: none inside the loop, the lengths \
         are compared at the start):\n{}\n\nthe loop:\n{body}",
        form.what,
        checked.join("\n")
    );
}

/// The `Span` accesses `<span>.ptr[<index>]` of a text: the index expression (up to the matching `]`) and
/// whether the access is the target of an assignment.
fn pointer_accesses(body: &str) -> Vec<(String, bool)> {
    let mut found = Vec::new();
    let mut rest = body;
    while let Some(at) = rest.find(".ptr[") {
        let after = &rest[at + ".ptr[".len()..];
        let mut depth = 1;
        let mut end = None;
        for (k, ch) in after.char_indices() {
            match ch {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(k);
                        break;
                    }
                }
                _ => {}
            }
        }
        let end = end.unwrap_or_else(|| panic!("an unbalanced `.ptr[` in:\n{body}"));
        let tail = &after[end + 1..];
        found.push((after[..end].to_string(), tail.starts_with(" =") && !tail.starts_with(" ==")));
        rest = tail;
    }
    found
}

fn assert_through_the_pointer(form: &Form) {
    let body = process_loop(form);
    let accesses = pointer_accesses(&body);
    let writes = accesses.iter().filter(|(_, w)| *w).count();
    let reads = accesses.len() - writes;
    assert!(
        reads >= form.reads && writes >= form.writes,
        "the loop of the form `{}` reads {reads} and writes {writes} through `.ptr[..]` (expected at least {} and {}):\n{body}",
        form.what,
        form.reads,
        form.writes
    );
    // The index is made from the variable of the loop (`i`), whatever else is in it.
    for (index, _) in &accesses {
        assert!(
            index.split(|ch: char| !(ch.is_alphanumeric() || ch == '_')).any(|word| word == "i"),
            "the form `{}`: the index `{index}` of an access of the loop is not made from the loop variable `i`:\n{body}",
            form.what
        );
    }
}

fn assert_tick_is_checked(form: &Form) {
    let tick = definition(generated_c(), &format!("{}__tick", form.flow));
    assert!(
        tick.contains("onsa_idx("),
        "`tick` of the form `{}` must keep the checked indices of the sample stage (§11.6, §9.2):\n{tick}",
        form.what
    );
}

fn assert_compared_before_the_loop(form: &Form) {
    let process = definition(generated_c(), &format!("{}__process", form.flow));
    let at_loop = process.find("  for (").unwrap_or_else(|| panic!("no loop in:\n{process}"));
    let compare = process.find("span lengths differ");
    assert!(
        compare.is_some_and(|c| c < at_loop),
        "the form `{}`: the comparison of the lengths (a panic `span lengths differ`) must be before the loop:\n{process}",
        form.what
    );
}

// ---------------------------------------------------------------------------------------------
// The main property: no checked index in the sample loop of `process`
// ---------------------------------------------------------------------------------------------

#[test]
fn the_sample_loop_of_one_span_in_and_out_has_no_checked_index() {
    assert_unchecked(&ONE_SPAN);
}

#[test]
fn the_sample_loop_of_a_planar_input_and_output_has_no_checked_index() {
    assert_unchecked(&PLANAR);
}

#[test]
fn the_sample_loop_of_a_struct_in_and_out_has_no_checked_index() {
    assert_unchecked(&STRUCT_IO);
}

// ---------------------------------------------------------------------------------------------
// The positive controls: the loop reads and writes through `.ptr[i]` (so the extraction is not empty)
// ---------------------------------------------------------------------------------------------

#[test]
fn the_sample_loop_of_one_span_in_and_out_reads_and_writes_through_the_pointer() {
    assert_through_the_pointer(&ONE_SPAN);
}

#[test]
fn the_sample_loop_of_a_planar_input_and_output_reads_and_writes_through_the_pointer() {
    assert_through_the_pointer(&PLANAR);
}

#[test]
fn the_sample_loop_of_a_struct_in_and_out_reads_and_writes_through_the_pointer() {
    assert_through_the_pointer(&STRUCT_IO);
}

// ---------------------------------------------------------------------------------------------
// The negative controls: what the sample stage calls keeps its checked indices
// ---------------------------------------------------------------------------------------------

#[test]
fn tick_of_one_span_in_and_out_keeps_its_checked_index() {
    assert_tick_is_checked(&ONE_SPAN);
}

#[test]
fn tick_of_a_planar_flow_keeps_its_checked_index() {
    assert_tick_is_checked(&PLANAR);
}

#[test]
fn tick_of_a_struct_in_and_out_flow_keeps_its_checked_index() {
    assert_tick_is_checked(&STRUCT_IO);
}

#[test]
fn a_user_rt_fn_that_a_flow_calls_keeps_its_checked_index() {
    // `pick` reads an array at an index that is not a constant (§9.2: checked).
    let pick = definition(generated_c(), "m__pick");
    assert!(pick.contains("onsa_idx("), "the checked index of the user's `rt fn` is gone:\n{pick}");
    // And `process` of each form reaches it only through `tick`, which calls it (the flow is not changed).
    for form in [&ONE_SPAN, &PLANAR, &STRUCT_IO] {
        let tick = definition(generated_c(), &format!("{}__tick", form.flow));
        assert!(tick.contains("m__pick("), "`tick` of the form `{}` does not call `pick`:\n{tick}", form.what);
    }
}

// ---------------------------------------------------------------------------------------------
// The comparison of the lengths stays, before the loop
// ---------------------------------------------------------------------------------------------

#[test]
fn the_lengths_are_compared_before_the_sample_loop() {
    for form in [&ONE_SPAN, &PLANAR, &STRUCT_IO] {
        assert_compared_before_the_loop(form);
    }
}
