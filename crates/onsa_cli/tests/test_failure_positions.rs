//! The position of a failure that `onsa test` reports, for the forms the test
//! ticket of W2-10 did not cover (spec §18.1: `span` is the position of the
//! expression that panicked).

mod test_support;

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
/// `xs[0][i]` when the outer index is the one out of range.
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
}

test \"write outer\" {
  var xs: [[I32; 2]; 2] = [[0, 0], [0, 0]]
  let i: U32 = 3
  xs[0][i] = 1
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
