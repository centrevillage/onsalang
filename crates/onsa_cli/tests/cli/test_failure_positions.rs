//! The position of a failure that `onsa test` reports, for the forms the test
//! ticket of W2-10 did not cover (spec §18.1: `span` is the position of the
//! expression that panicked).

use crate::test_support;

use test_support::*;

/// R-185: an index out of range in the target of an assignment panics at the
/// target `xs[i]`, not at the whole statement; the value's own panic is at the
/// value. The text line has the same line.
#[test]
fn an_index_out_of_range_in_an_assignment_is_at_the_target() {
    let src = "test \"write\" {
  var xs: [I32; 2] = [1, 2]
  let i: U32 = 2
  xs[i] = 3
  assert xs[0] == 1
}

test \"value\" {
  var xs: [I32; 2] = [1, 2]
  let i: U32 = 5
  xs[0] = xs[i] + 1
  assert xs[0] == 1
}
";
    let d = Dir::pkg("assign_target");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let f = failure_of(record(&doc, "m", "write"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 4, 3, 4, 8), "{f}");
    assert!(array_of(f, "calls").is_empty(), "{f}");
    let f = failure_of(record(&doc, "m", "value"));
    assert_eq!(span_of(&f["span"]), span("m.onsa", 11, 11, 11, 16), "{f}");

    let text = run(d.root(), &["test", &d.arg()]);
    assert!(
        result_lines(&text).iter().any(|l| l.starts_with("test m \"write\" failed at m.onsa:4: ")),
        "{}",
        text.stdout
    );
}

/// R-188: in a chain of indices the panic is at the element that is out of
/// range: the inner `xs[i]` of `xs[i][0]`, read or written, and the whole
/// `xs[0][i]` when the outer index is the one out of range. A written `xs` is
/// read after the write (an unread binding is an E0309, §5.1), with no blank
/// line before the last test, so that the lines below stay.
#[test]
fn an_index_out_of_range_in_a_chain_is_at_its_own_element() {
    let src = "test \"read\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  let y = xs[i][0]
  assert y == 0
}

test \"write\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  xs[i][0] = 1
  assert xs[0][0] == 1
}
test \"write outer\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  xs[0][i] = 1
  assert xs[0][0] == 1
}
";
    let d = Dir::pkg("index_chain");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    for (name, want) in [
        ("read", span("m.onsa", 4, 11, 4, 16)),
        ("write", span("m.onsa", 11, 3, 11, 8)),
        ("write outer", span("m.onsa", 17, 3, 17, 11)),
    ] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]), want, "{name}: {f}");
    }
}

/// The result line of the test `name` of the module `m`, with its `failed at <file>:<line>:` head.
fn failed_at(text: &Out, name: &str) -> String {
    let head = format!("test m \"{name}\" failed at ");
    let lines = result_lines(text);
    let line = lines.iter().find(|l| l.starts_with(&head));
    let line = line.unwrap_or_else(|| panic!("no failed line of {name}: {}", text.stdout));
    line[head.len()..].to_string()
}

/// S-893: the panic of `unwrap` is the `panic` in the body of std. The JSON has it as it is, with
/// the call first in `calls`; the text shows the innermost position out of std (`spec/tools.md`
/// §4). The lines of std are not fixed here.
#[test]
fn a_failed_unwrap_is_in_std_in_the_json_and_at_the_call_in_the_text() {
    let src = "fn get(o: Option[I32]) -> I32 {
  o.unwrap()
}

fn id[T](move o: Option[T]) -> T {
  o.unwrap()
}

fn nested() -> Option[Option[I32]] {
  Some(None)
}

test \"none\" {
  let o: Option[I32] = None
  assert o.unwrap() == 0
}

test \"err\" {
  let r: Result[I32, U32] = Err(1)
  assert r.unwrap() == 0
}

test \"helper\" {
  assert get(None) == 0
}

test \"generic\" {
  let o: Option[U32] = None
  assert id(o) == 0
}

test \"chain\" {
  assert nested().unwrap().unwrap() == 0
}
";
    let d = Dir::pkg("unwrap_std");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = run(d.root(), &["test", &d.arg()]);
    // The test, the message, the line of the text, and the start of each of `calls`.
    let none = "called `unwrap()` on `None`";
    let err = "called `unwrap()` on `Err`";
    let cases = [
        ("none", none, 15, &[(15u64, 10u64)][..]),
        ("err", err, 20, &[(20, 10)]),
        ("helper", none, 2, &[(2, 3), (24, 10)]),
        ("generic", none, 6, &[(6, 3), (29, 10)]),
        ("chain", none, 33, &[(33, 10)]),
    ];
    for (name, message, line, calls) in cases {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]).file, "std/core.onsa", "{name}: {f}");
        assert_eq!(str_of(f, "kind"), "panic", "{name}: {f}");
        let got: Vec<_> = call_spans(f).iter().map(|c| (c.file.clone(), c.line, c.col)).collect();
        let want: Vec<_> = calls.iter().map(|&(l, c)| ("m.onsa".to_string(), l, c)).collect();
        assert_eq!(got, want, "{name}: {f}");
        assert_eq!(failed_at(&text, name), format!("m.onsa:{line}: {message}"), "{name}");
    }
}

/// S-893: a failed `assert` in the Onsa body of std is shown at the call too, and of a helper
/// that calls std, at the call in the helper. The position in std stays in the JSON.
#[test]
fn a_failed_assert_in_the_body_of_std_is_shown_at_the_call() {
    let src = "use std.dsp.test.{impulse, energy}

fn past() -> F64 uses {Alloc} {
  let b = impulse(4)
  energy(b, 0, 9)
}

test \"direct\" {
  let b = impulse(4)
  assert energy(b, 0, 9) == 1.0
}

test \"helper\" {
  assert past() == 1.0
}
";
    let d = Dir::pkg("energy_std");
    d.write("m.onsa", src);
    let (out, doc) = test_json(d.root(), &[&d.arg()]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let text = run(d.root(), &["test", &d.arg()]);
    for (name, line) in [("direct", 10), ("helper", 5)] {
        let f = failure_of(record(&doc, "m", name));
        assert_eq!(span_of(&f["span"]).file, "std/dsp/test.onsa", "{name}: {f}");
        let shown = failed_at(&text, name);
        assert!(shown.starts_with(&format!("m.onsa:{line}: ")), "{name}: {shown}");
    }
}

/// S-893: what is out of std is told by the file, not by its name: a file of the user's in a
/// directory `std` (a package cannot have that module, E0304, but a file alone can be there) is
/// out of std, and the failure is shown there and not at the `panic` in `std/core.onsa`.
#[test]
fn a_file_in_a_directory_named_std_is_out_of_std() {
    let d = Dir::bare("own_std_dir");
    d.write("std/m.onsa", "test \"mine\" {\n  let o: Option[I32] = None\n  assert o.unwrap() == 0\n}\n");
    let text = run(d.root(), &["test", "std/m.onsa"]);
    assert_eq!(text.code, 1, "{}{}", text.stdout, text.stderr);
    assert_eq!(failed_at(&text, "mine"), "std/m.onsa:3: called `unwrap()` on `None`");
}
