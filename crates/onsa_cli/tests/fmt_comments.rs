//! Where `onsa fmt` leaves the comments, by the whole text of the output (W3-11/t, unit U4;
//! `spec/tools.md` §3.2 and §3.4, spec §2.1, §2.5 and §18.2; plan S-58, S-496, S-497, S-502, S-507,
//! S-528, S-529, S-530 and the reviews R-70, R-199, R-201, R-212).
//!
//! The rule (§3.4): `fmt` leaves a comment on the line it was written on. A comment at the end of a line
//! stays after the element of that line (after the `,` that `fmt` adds in the block form), a line of a
//! comment stays before the next element, or before the closing bracket when no element follows, in a list
//! and in the middle of an expression. A pair of braces that holds a comment is not put on one line. The
//! closing bracket and a `let` are not moved up before a comment at the end of a line, and a line break
//! after such a comment is not removed at any place (§3.2). The comments at the end of consecutive lines
//! are in one column, one space after the longest code, also inside a list (§3.2).
//!
//! Every test has the whole text of the input and of the expected output. The expected texts are written
//! from the rules above and from §3.2, not taken from the output of `fmt`. The output must also be a fixed
//! point (`fmt --check` ends with 0 and another `fmt` changes nothing), and neither the input nor the
//! expected text has a diagnostic of the syntax stage (a file with one is not rewritten, `onsa fmt` ends
//! with 2, §18.2). `expect_fmt` checks all of it.
//!
//! The places of the comments in every kind of list are generated, so that one rule is asked of every
//! kind (the same kinds as in `fmt_lines_lists.rs`, and the arguments of a call): the arguments of a call
//! and of a declaration, the elements of an array and of a tuple, the fields of a struct literal and of a
//! struct, the variants of an enum and the elements of a variant, the arms of a `match`, the patterns
//! (tuple, struct, variant), the inputs of a flow, the arguments of an attribute, the type arguments of a
//! type and of an expression, the type parameters, the tuple type, the arguments of a function type, an
//! effect row and a `use` list. The shapes:
//! - the block form with a comment after every element and none written after the last;
//! - the block form with a comment after the last element only, and with one element;
//! - a line of a comment before every element and before the closing bracket, at the column of the elements
//!   and at other columns;
//! - a comment at the end of the line of the opening bracket, and the block form with a comment in every
//!   place;
//! - the one-line form with a comment after the last element and the closing bracket on the next line
//!   (S-507), with and without the `,` after the last element;
//! - the continuation with a comment after every element.
//!
//! The other tests are written by hand: the comments in the middle of an expression (a continuation with a
//! binary operator, `=`, `->`, a range symbol, the `|` of a pattern, and a `.` at the start of the next
//! line, R-199; the line break after a comment inside an element, R-201), the comments round an attribute
//! (R-212), the enclosures that hold only a comment (S-496) and the blank lines round it (S-502), the doc
//! comments, the columns of the comments, the text of a comment, the 17 forms of R-70, a file with the
//! forms nested, and the files that are refused because of a comment (E0002, E0003, E0004 and E0020).
//! The decisions S-528, S-529 and S-530 (2026-10-14) have their own tests: a comment after the closing
//! bracket of the block form that is on the line of the last element (`b)  // c`) stays after the last code
//! of its line, which fmt splits (`b,` and `) // c`), also for `]`, `}` and the `}` of a block; the comment
//! of a line that holds only a `,` and a comment (`[1 // c1` and `, // c2` and `2]`) stays in its place as a
//! line of a comment; a line of a comment between an element and its `,` stays before the next element.
//!
//! What is not here, and why:
//! - the places that the text of §3.2 and §3.4 does not decide yet (S-523, S-531, S-532; no expectation is
//!   written): a line of a comment before the closing bracket in the one-line form and in the continuation,
//!   a line of a comment between the elements of a continuation (S-529 and S-530 in these forms too), the
//!   width of the characters that are wider than one column in the columns of the comments, and the spaces
//!   at the end of the text of a comment;
//! - the fixed points of the case files (`tests/spec/fmt/comments_places.onsa`), and what `fmt_lines_lists.rs`
//!   has already (S-497 (β) in five forms, `@mem(bulk)` and a comment, a comment inside the empty braces of a
//!   function, the blank lines at the start and the end of a block);
//! - S-526 and S-527 (the `let` that is continued, the comment between the attribute of a `let` and the
//!   `let`, the arguments of an attribute over many lines), the rewrites of the tree (W3-12) and the check
//!   before writing (U5).
//!
//! The texts of `fmt` are made by the function `onsa fmt` calls (`test_support::fmt`, no file written), the
//! refused files by the binary.

mod test_support;

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // The counter makes the directory the test's own even when two tests use the same tag.
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_u4_{}_{n}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn onsa(args: &[&str]) -> Output {
    Command::new(ONSA).args(args).output().expect("run onsa")
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap_or_else(|| panic!("ended by a signal: {out:?}"))
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// The lines joined, with one line break at the end of the file.
fn src(lines: &[&str]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

fn src_s(lines: &[String]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

/// A file before and after `onsa fmt`: the whole text of each.
struct Case {
    what: String,
    input: String,
    expected: String,
}

/// A case from the lines of a file before and after.
fn case(what: impl Into<String>, input: &[&str], expected: &[&str]) -> Case {
    Case { what: what.into(), input: src(input), expected: src(expected) }
}

/// A case from the whole text of a file before and after.
fn text(what: impl Into<String>, input: &str, expected: &str) -> Case {
    Case { what: what.into(), input: input.to_string(), expected: expected.to_string() }
}

/// `onsa fmt` on every input gives the expected text, which is a fixed point (`test_support::fmt`).
fn expect_fmt(tag: &str, cases: &[Case]) {
    let cases: Vec<_> = cases.iter().map(|c| (c.what.as_str(), c.input.as_str(), c.expected.as_str())).collect();
    test_support::fmt::expect_fmt(tag, &cases);
}

/// Every input is refused: `onsa fmt` ends with 2, names `diag` in its output (diagnostics go to the
/// standard output, `spec/tools.md` §3.1) and does not touch the file.
fn expect_refused(tag: &str, diag: &str, inputs: &[(&str, String)]) {
    assert!(!inputs.is_empty(), "no case to run");
    let d = Dir::new(tag);
    for (i, (what, input)) in inputs.iter().enumerate() {
        let path = d.file(&format!("r{i}.onsa"), input);
        let out = onsa(&["fmt", &path]);
        assert_eq!(code(&out), 2, "{what}: onsa fmt must refuse it: {out:?}");
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        assert!(text.contains(diag), "{what}: expected {diag} in the output, got:\n{text}");
        assert_eq!(&read(&path), input, "{what}: a refused file must stay as it was");
    }
}

/// The lines of one function around a body (the body lines are written with their own indentation).
fn in_fn(body: &[&str]) -> Vec<String> {
    let mut v = vec!["fn f(a: I32, b: I32) -> I32 {".to_string()];
    v.extend(body.iter().map(|s| s.to_string()));
    v.push("}".to_string());
    v
}

/// A case whose input and output are one function with the given body lines.
fn body(what: impl Into<String>, input: &[&str], expected: &[&str]) -> Case {
    Case { what: what.into(), input: src_s(&in_fn(input)), expected: src_s(&in_fn(expected)) }
}

/// The same for the body of a flow.
fn in_flow(body: &[&str]) -> Vec<String> {
    let mut v = vec!["flow g(x: F32 at sample, p: F32 at block) -> F32 at sample {".to_string()];
    v.extend(body.iter().map(|s| s.to_string()));
    v.push("}".to_string());
    v
}

fn flow_body(what: impl Into<String>, input: &[&str], expected: &[&str]) -> Case {
    Case { what: what.into(), input: src_s(&in_flow(input)), expected: src_s(&in_flow(expected)) }
}

/// One list in a file: the lines before, the line of the opening bracket (up to and including the bracket,
/// with its indentation), the elements, the closing bracket, the text that follows it on its line, and the
/// lines after. `pad` is a list whose braces have a space inside when it is on one line.
#[derive(Clone, Copy)]
struct Kind {
    name: &'static str,
    head: &'static [&'static str],
    pre: &'static str,
    pad: bool,
    elems: &'static [&'static str],
    close: &'static str,
    post: &'static str,
    tail: &'static [&'static str],
}

const K_ATTR_ARGS: Kind = Kind {
    name: "the arguments of an attribute",
    head: &["flow g("],
    pre: "  @param(",
    pad: false,
    elems: &["min: 0.0", "max: 1.0", "default: 0.5"],
    close: ")",
    post: "",
    tail: &["  level: F32 at block,", ") -> F32 at sample {", "  level", "}"],
};

const K_VARIANT: Kind = Kind {
    name: "the elements of a variant",
    head: &["enum E {", "  A,"],
    pre: "  B(",
    pad: false,
    elems: &["I32", "F32", "U8"],
    close: ")",
    post: ",",
    tail: &["}"],
};

const K_EFFECT_ROW: Kind = Kind {
    name: "an effect row",
    head: &[],
    pre: "fn g() -> I32 uses {",
    pad: false,
    elems: &["Alloc", "Fs", "Io"],
    close: "}",
    post: " {",
    tail: &["  1", "}"],
};

const K_USE: Kind = Kind {
    name: "a use list",
    head: &[],
    pre: "use std.math.{",
    pad: false,
    elems: &["sin", "cos", "tan"],
    close: "}",
    post: "",
    tail: &[],
};

const K_TYPE_ARGS: Kind = Kind {
    name: "the type arguments of a type",
    head: &["fn g(a: I32) -> I32 {"],
    pre: "  let r: Result[",
    pad: false,
    elems: &["I32", "F32"],
    close: "]",
    post: " = f(a)",
    tail: &["  1", "}"],
};

const K_EXPR_TYPE_ARGS: Kind = Kind {
    name: "the type arguments of an expression",
    head: &["fn g(a: I32) -> I32 {"],
    pre: "  let r = h::[",
    pad: false,
    elems: &["I32", "F32", "U8"],
    close: "]",
    post: "(a)",
    tail: &["  1", "}"],
};

const K_TYPE_PARAMS: Kind = Kind {
    name: "the type parameters",
    head: &[],
    pre: "fn g[",
    pad: false,
    elems: &["T", "U", "V"],
    close: "]",
    post: "(a: T, b: U) -> T {",
    tail: &["  a", "}"],
};

const K_TUPLE_TYPE: Kind = Kind {
    name: "a tuple type",
    head: &["fn g() -> I32 {"],
    pre: "  let t: (",
    pad: false,
    elems: &["I32", "F32", "U8"],
    close: ")",
    post: " = (1, 2.0, 3)",
    tail: &["  1", "}"],
};

const K_FN_TYPE: Kind = Kind {
    name: "the arguments of a function type",
    head: &[],
    pre: "type Op = fn(",
    pad: false,
    elems: &["I32", "F32", "U8"],
    close: ")",
    post: " -> I32",
    tail: &[],
};

// The kinds that were in the plan before (unit U2): the forms that `fmt_spaces_lists.rs` does not place.

const K_PARAMS: Kind = Kind {
    name: "the parameters of a declaration",
    head: &[],
    pre: "fn g(",
    pad: false,
    elems: &["a: I32", "b: I32", "c: I32"],
    close: ")",
    post: " -> I32 {",
    tail: &["  a", "}"],
};

const K_ARRAY: Kind = Kind {
    name: "the elements of an array",
    head: &["fn g() -> I32 {"],
    pre: "  let xs = [",
    pad: false,
    elems: &["1", "2", "3"],
    close: "]",
    post: "",
    tail: &["  xs[0]", "}"],
};

const K_TUPLE: Kind = Kind {
    name: "the elements of a tuple",
    head: &["fn g() -> I32 {"],
    pre: "  let t = (",
    pad: false,
    elems: &["1", "2.0", "a"],
    close: ")",
    post: "",
    tail: &["  1", "}"],
};

const K_STRUCT_LIT: Kind = Kind {
    name: "the fields of a struct literal",
    head: &["fn g() -> P {"],
    pre: "  let p = P {",
    pad: true,
    elems: &["x: 1.0", "y: 2.0", "z: 3.0"],
    close: "}",
    post: "",
    tail: &["  p", "}"],
};

const K_FLOW_INPUTS: Kind = Kind {
    name: "the inputs of a flow",
    head: &[],
    pre: "flow g(",
    pad: false,
    elems: &["x: F32 at sample", "p: F32 at block", "q: F32 at init"],
    close: ")",
    post: " -> F32 at sample {",
    tail: &["  x", "}"],
};

const K_STRUCT_DECL: Kind = Kind {
    name: "the fields of a struct",
    head: &[],
    pre: "struct P {",
    pad: true,
    elems: &["x: F32", "y: F32", "z: F32"],
    close: "}",
    post: "",
    tail: &[],
};

const K_ENUM_DECL: Kind = Kind {
    name: "the variants of an enum",
    head: &[],
    pre: "pub enum E {",
    pad: true,
    elems: &["A", "B(F32)", "C(I32, F32)"],
    close: "}",
    post: "",
    tail: &[],
};

const K_MATCH: Kind = Kind {
    name: "the arms of a match",
    head: &["fn g(o: Option[I32]) -> I32 {"],
    pre: "  match o {",
    pad: true,
    elems: &["Some(v) if v > 0 => v", "Some(v) => -v", "None => 0"],
    close: "}",
    post: "",
    tail: &["}"],
};

const K_TUPLE_PATTERN: Kind = Kind {
    name: "a tuple pattern",
    head: &["fn g(t: (I32, I32, I32)) -> I32 {"],
    pre: "  let (",
    pad: false,
    elems: &["a", "b", "c"],
    close: ")",
    post: " = t",
    tail: &["  a", "}"],
};

const K_STRUCT_PATTERN: Kind = Kind {
    name: "a struct pattern",
    head: &["fn g(p: P) -> I32 {"],
    pre: "  let P {",
    pad: true,
    elems: &["x: a", "y: b", "z: c"],
    close: "}",
    post: " = p",
    tail: &["  a", "}"],
};

const K_VARIANT_PATTERN: Kind = Kind {
    name: "the payload of a variant pattern",
    head: &["fn g(s: S) -> I32 {", "  match s {"],
    pre: "    S.R(",
    pad: false,
    elems: &["w", "z", "u"],
    close: ")",
    post: " => w,",
    tail: &["    _ => 0,", "  }", "}"],
};

// ---- the places of the comments in every kind of list ---------------------------------------------------

/// The calls (the other kinds are the lists of the declarations, the patterns and the types).
const K_CALL: Kind = Kind {
    name: "the arguments of a call",
    head: &["fn g(a: I32) -> I32 {"],
    pre: "  let r = h(",
    pad: false,
    elems: &["a", "b + 1", "c"],
    close: ")",
    post: "",
    tail: &["  r", "}"],
};

const K_ALL: &[&Kind] = &[
    &K_CALL,
    &K_PARAMS,
    &K_ARRAY,
    &K_TUPLE,
    &K_STRUCT_LIT,
    &K_STRUCT_DECL,
    &K_ENUM_DECL,
    &K_VARIANT,
    &K_MATCH,
    &K_TUPLE_PATTERN,
    &K_STRUCT_PATTERN,
    &K_VARIANT_PATTERN,
    &K_FLOW_INPUTS,
    &K_ATTR_ARGS,
    &K_TYPE_ARGS,
    &K_EXPR_TYPE_ARGS,
    &K_TYPE_PARAMS,
    &K_TUPLE_TYPE,
    &K_FN_TYPE,
    &K_EFFECT_ROW,
    &K_USE,
];

/// The lines of the expected text may hold a TAB between the code and a comment at the end of a line: the
/// comments of the consecutive lines that hold one are put in one column, one space after the longest code
/// (spec/tools.md §3.2). The other lines stay as they are.
fn cols(lines: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if !lines[i].contains('\t') {
            out.push(lines[i].clone());
            i += 1;
            continue;
        }
        let mut j = i;
        while j < lines.len() && lines[j].contains('\t') {
            j += 1;
        }
        let w = lines[i..j].iter().map(|l| l.split('\t').next().unwrap().chars().count()).max().unwrap() + 1;
        for l in &lines[i..j] {
            let (code, c) = l.split_once('\t').unwrap();
            out.push(format!("{code:<w$}{c}"));
        }
        i = j;
    }
    out
}

fn strs(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

/// A case of one kind: the lines of the list in the input and in the expected text, inside the lines
/// before and after the list.
fn in_kind(k: &Kind, shape: &str, input: Vec<String>, expected: Vec<String>) -> Case {
    let wrap = |mid: Vec<String>| {
        let mut v: Vec<String> = k.head.iter().map(|l| l.to_string()).collect();
        v.extend(mid);
        v.extend(k.tail.iter().map(|l| l.to_string()));
        src_s(&v)
    };
    Case { what: format!("{}: {shape}", k.name), input: wrap(input), expected: wrap(cols(&expected)) }
}

fn indent_of(k: &Kind) -> String {
    " ".repeat(k.pre.len() - k.pre.trim_start().len())
}

/// The block form: a comment at the end of the line of every element, and the last element has no `,`.
fn block_trailing(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![k.pre.to_string()];
    let mut expected = vec![k.pre.to_string()];
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        // the spaces before the comment are of three kinds in the input
        let gap = ["   ", "", " "][i % 3];
        input.push(format!("{ind}  {e}{comma}{gap}// c{i}"));
        expected.push(format!("{ind}  {e},\t// c{i}"));
    }
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, a comment after every element, none written after the last", input, expected)
}

/// The block form: only the last element, which has no `,`, has a comment.
fn block_last_trailing(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![k.pre.to_string()];
    let mut expected = vec![k.pre.to_string()];
    for (i, e) in k.elems.iter().enumerate() {
        if i + 1 < n {
            input.push(format!("{ind}  {e},"));
            expected.push(format!("{ind}  {e},"));
        } else {
            input.push(format!("{ind}  {e}   // c"));
            expected.push(format!("{ind}  {e}, // c"));
        }
    }
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, a comment after the last element only", input, expected)
}

/// The block form: a line of a comment before an element and before the closing bracket.
fn block_leading(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![k.pre.to_string()];
    let mut expected = vec![k.pre.to_string()];
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        input.push(format!("{ind}  // before {i}"));
        expected.push(format!("{ind}  // before {i}"));
        input.push(format!("{ind}  {e}{comma}"));
        expected.push(format!("{ind}  {e},"));
    }
    input.push(format!("{ind}  // last"));
    expected.push(format!("{ind}  // last"));
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, a line of a comment before every element and before the closing bracket", input, expected)
}

/// The same with the lines of the comments at the wrong columns: they go to the column of the elements.
fn block_leading_misplaced(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![k.pre.to_string()];
    let mut expected = vec![k.pre.to_string()];
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        let wrong = ["", "          ", "     "][i % 3];
        input.push(format!("{wrong}// before {i}"));
        expected.push(format!("{ind}  // before {i}"));
        input.push(format!("{ind}  {e}{comma}"));
        expected.push(format!("{ind}  {e},"));
    }
    input.push(format!("{ind}      // last"));
    expected.push(format!("{ind}  // last"));
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, the lines of the comments are at other columns than the elements", input, expected)
}

/// The block form: a comment at the end of the line of the opening bracket.
fn block_open_line(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![format!("{}   // open", k.pre)];
    let mut expected = vec![format!("{} // open", k.pre)];
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        input.push(format!("{ind}  {e}{comma}"));
        expected.push(format!("{ind}  {e},"));
    }
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, a comment at the end of the line of the opening bracket", input, expected)
}

/// The block form with every place of a comment: the line of the opening bracket, before an element, after
/// an element, after the last element (no `,` written) and before the closing bracket. The first element
/// has a line of a comment before it, so the comment of the opening bracket and the comment after the
/// first element are not on consecutive lines.
fn block_all(k: &Kind) -> Case {
    let ind = indent_of(k);
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = vec![format!("{} // open", k.pre), format!("{ind}  // lead")];
    let mut expected = input.clone();
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        if i == 0 {
            input.push(format!("{ind}  {e}, // c0"));
            expected.push(format!("{ind}  {e}, // c0"));
        } else if i + 1 < n {
            input.push(format!("{ind}  {e},"));
            expected.push(format!("{ind}  {e},"));
        } else {
            input.push(format!("{ind}  {e}{comma} // c{i}"));
            expected.push(format!("{ind}  {e}, // c{i}"));
        }
    }
    input.push(format!("{ind}  // end"));
    expected.push(format!("{ind}  // end"));
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "block form, a comment in every place", input, expected)
}

/// The one-line form: the closing bracket goes on after a comment at the end of the line (S-507).
fn one_line_comment(k: &Kind) -> Case {
    let (ind, e) = (indent_of(k), k.elems);
    let sp = if k.pad { " " } else { "" };
    let close = format!("{ind}{}{}", k.close, k.post);
    let input = vec![format!("{}{sp}{}   // c", k.pre, e.join(", ")), close.clone()];
    let expected = vec![format!("{}{sp}{} // c", k.pre, e.join(", ")), close];
    in_kind(k, "one line, a comment after the last element, the closing bracket on the next line", input, expected)
}

/// The one-line form with a `,` after the last element: the `,` goes (the form has none).
fn one_line_comment_trailing_comma(k: &Kind) -> Case {
    let (ind, e) = (indent_of(k), k.elems);
    let sp = if k.pad { " " } else { "" };
    let close = format!("{ind}{}{}", k.close, k.post);
    let input = vec![format!("{}{sp}{},// c", k.pre, e.join(", ")), close.clone()];
    let expected = vec![format!("{}{sp}{} // c", k.pre, e.join(", ")), close];
    in_kind(k, "one line, a `,` after the last element and a comment", input, expected)
}

/// The continuation: a comment after every element, the closing bracket on the next line.
fn continuation_comments(k: &Kind) -> Case {
    let ind = indent_of(k);
    let sp = if k.pad { " " } else { "" };
    let col = " ".repeat(k.pre.len() + sp.len());
    let close = format!("{ind}{}{}", k.close, k.post);
    let n = k.elems.len();
    let mut input = Vec::new();
    let mut expected = Vec::new();
    for (i, e) in k.elems.iter().enumerate() {
        let comma = if i + 1 < n { "," } else { "" };
        let gap = ["   ", "", " "][i % 3];
        let lead = if i == 0 { format!("{}{sp}", k.pre) } else { col.clone() };
        input.push(format!("{lead}{e}{comma}{gap}// c{i}"));
        expected.push(format!("{lead}{e}{comma}\t// c{i}"));
    }
    input.push(close.clone());
    expected.push(close);
    in_kind(k, "continuation, a comment after every element, the closing bracket on the next line", input, expected)
}

fn kind_cases(f: fn(&Kind) -> Case, kinds: &[&Kind]) -> Vec<Case> {
    kinds.iter().map(|k| f(k)).collect()
}

/// The 17 forms of the review R-70 (`tests/review-phase1/parent/r70/`), each a whole file, with their names.
const R70: &[(&str, &str)] = &[
    (
        "01_field_doc",
        r##"pub struct P {
  /// x coordinate
  x: F32,
  y: F32,
}

pub fn f() {}
"##,
    ),
    (
        "02_variant_doc",
        r##"pub enum Mode {
  /// silent
  Off,
  On,
}
"##,
    ),
    (
        "03_flow_input_doc",
        r##"pub flow gain(
  /// input signal
  x: Sig[F32],
  level: Ctl[F32],
) -> Sig[F32] {
  x * level
}
"##,
    ),
    (
        "04_arg_trailing",
        r##"fn f(
  a: F32, // gain
  b: F32, // offset
) -> F32 {
  a + b
}
"##,
    ),
    (
        "05_empty_body",
        r##"fn empty() {
  // todo
}
"##,
    ),
    (
        "06_match_arms",
        r##"fn g(x: I32) -> I32 {
  match x {
    0 => 1, // zero
    1 => 5, // one
    _ => 2, // other
  }
}
"##,
    ),
    (
        "07_array_table",
        r##"const C: [F32; 3] = [
  0.1, // b0
  0.2, // b1
  0.3, // b2
]
"##,
    ),
    (
        "08_mid_expr",
        r##"fn h(a: F32, b: F32) -> F32 {
  let y = a + // first
    b
  y
}
"##,
    ),
    (
        "09_after_open_brace",
        r##"fn f() -> I32 { // note
  1
}
"##,
    ),
    (
        "10_block_end",
        r##"fn f() -> I32 {
  let x = 1
  x
  // trailing note
}
"##,
    ),
    (
        "11_call_args",
        r##"fn k(a: F32, b: F32) -> F32 { a }

fn f() -> F32 {
  k(
    1.0, // first
    2.0, // second
  )
}
"##,
    ),
    (
        "12_struct_lit",
        r##"pub struct P {
  x: F32,
  y: F32,
}

fn f() -> P {
  P {
    x: 1.0, // left
    y: 2.0, // up
  }
}
"##,
    ),
    (
        "13_field_trailing",
        r##"pub struct P {
  x: F32, // left
  y: F32, // up
}
"##,
    ),
    (
        "14_leading_in_list",
        r##"const C: [F32; 4] = [
  // numerator
  0.1,
  0.2,
  // denominator
  0.3,
  0.4,
]
"##,
    ),
    (
        "15_if_cond",
        r##"fn f(a: Bool, b: Bool) -> I32 {
  if a && // first
    b {
    1
  } else {
    0
  }
}
"##,
    ),
    (
        "16_enum_trailing",
        r##"pub enum Mode {
  Off, // silent
  On,  // sound
}
"##,
    ),
    (
        "17_impl_end",
        r##"pub struct P {
  x: F32,
}

impl P {
  pub fn a(self) -> F32 { self.x }
  // more later
}
"##,
    ),
];

/// The same list with its first element only.
fn first_only(k: &Kind) -> Kind {
    Kind { elems: &k.elems[..1], ..*k }
}

/// The kinds that stay a list when it has one element (a tuple, a tuple type and the arguments of a function
/// type of one element are other things, §3.2).
const K_ONE: &[&Kind] = &[
    &K_CALL,
    &K_PARAMS,
    &K_ARRAY,
    &K_STRUCT_LIT,
    &K_STRUCT_DECL,
    &K_ENUM_DECL,
    &K_VARIANT,
    &K_MATCH,
    &K_FLOW_INPUTS,
    &K_ATTR_ARGS,
    &K_TYPE_PARAMS,
    &K_EFFECT_ROW,
    &K_USE,
];

fn one_element_cases(f: fn(&Kind) -> Case) -> Vec<Case> {
    K_ONE.iter().map(|k| f(&first_only(k))).collect()
}

#[test]
fn the_comment_after_an_element_of_the_block_form_follows_the_comma_that_is_added() {
    // §3.4, §3.2: the block form has a `,` after every element; a comment at the end of the line of an
    // element, which has no `,` written, goes after the added `,`. The comments of the consecutive lines are
    // in one column (the comma of the last element is part of its line).
    expect_fmt("block_trailing", &kind_cases(block_trailing, K_ALL));
}

#[test]
fn the_comment_after_the_last_element_alone_follows_the_added_comma() {
    expect_fmt("block_last_trailing", &kind_cases(block_last_trailing, K_ALL));
}

#[test]
fn the_comment_after_the_only_element_of_the_block_form_follows_the_added_comma() {
    expect_fmt("block_one_element", &one_element_cases(block_last_trailing));
}

#[test]
fn a_line_of_a_comment_in_a_list_of_the_block_form_stays_before_the_next_element_or_the_closing_bracket() {
    // §3.4: a line of a comment goes before the next element, and before the closing bracket when no element
    // follows.
    expect_fmt("block_leading", &kind_cases(block_leading, K_ALL));
}

#[test]
fn a_line_of_a_comment_in_a_list_of_the_block_form_is_at_the_column_of_the_elements() {
    expect_fmt("block_leading_misplaced", &kind_cases(block_leading_misplaced, K_ALL));
}

#[test]
fn a_comment_at_the_end_of_the_line_of_the_opening_bracket_stays_and_makes_the_block_form() {
    // A line break after the opening bracket and the comment (§3.2: the form is by the writer's line break).
    expect_fmt("block_open_line", &kind_cases(block_open_line, K_ALL));
}

#[test]
fn a_comment_in_every_place_of_a_list_of_the_block_form_stays_where_it_was_written() {
    expect_fmt("block_all", &kind_cases(block_all, K_ALL));
}

#[test]
fn a_list_of_the_block_form_with_comments_in_every_place_is_a_fixed_point() {
    let cases: Vec<Case> = kind_cases(block_all, K_ALL)
        .into_iter()
        .map(|c| Case { what: c.what.clone(), input: c.expected.clone(), expected: c.expected })
        .collect();
    expect_fmt("block_all_fixed", &cases);
}

#[test]
fn the_closing_bracket_of_the_one_line_form_stays_on_its_line_after_a_comment() {
    // S-507, S-497 (β): `f(a, b // c` and `)` on the next line is not moved before the comment, and the
    // spaces before the comment are one.
    expect_fmt("one_line_comment", &kind_cases(one_line_comment, K_ALL));
}

#[test]
fn a_comma_after_the_last_element_of_the_one_line_form_goes_also_before_a_comment() {
    expect_fmt("one_line_comment_comma", &kind_cases(one_line_comment_trailing_comma, K_ALL));
}

#[test]
fn the_comments_of_the_elements_of_a_continuation_are_in_one_column() {
    // §3.2: the elements are under the first, no `,` after the last (the form is a continuation); the
    // closing bracket after a comment stays on its line.
    expect_fmt("continuation_comments", &kind_cases(continuation_comments, K_ALL));
}

// ---- the comments in the middle of an expression (R-199, R-201) ----------------------------------------

/// A case of a function body whose expected lines may hold the TAB of `cols`.
fn bodyc(what: impl Into<String>, input: &[&str], expected: &[&str]) -> Case {
    let exp = cols(&strs(expected));
    let exp: Vec<&str> = exp.iter().map(String::as_str).collect();
    body(what, input, &exp)
}

#[test]
fn a_comment_after_the_symbol_of_a_continuation_stays_and_the_next_line_is_one_level_deeper() {
    let cases = vec![
        body("a binary operator", &["  let y = a +   // c", "  b", "  y"], &["  let y = a + // c", "    b", "  y"]),
        body("`=`", &["  let y =   // c", "  a + b", "  y"], &["  let y = // c", "    a + b", "  y"]),
        case(
            "`->` of a heading",
            &["fn f(a: I32) ->   // c", "I32 {", "  a", "}"],
            &["fn f(a: I32) -> // c", "  I32 {", "  a", "}"],
        ),
        body(
            "a range symbol of a heading",
            &["  for i in 0 ..<   // c", "  b {", "    h(i)", "  }", "  a"],
            &["  for i in 0 ..< // c", "    b {", "    h(i)", "  }", "  a"],
        ),
        body(
            "the `|` of a pattern",
            &["  match a {", "    0 |   // c", "    1 => 1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 | // c", "      1 => 1,", "    _ => 2,", "  }"],
        ),
        bodyc(
            "a comment on two lines of a continuation (in one column)",
            &["  let y = a + // one", "    b + // two", "    a", "  y"],
            &["  let y = a +\t// one", "    b +\t// two", "    a", "  y"],
        ),
    ];
    expect_fmt("continuation_symbols", &cases);
}

#[test]
fn a_comment_before_a_dot_of_the_next_line_stays_on_its_line() {
    // R-199: the `.` at the start of the next line continues the statement (spec §2.5); the comment is not
    // moved after the continued line.
    let cases = vec![
        body(
            "a call of a function value",
            &["  let z = f   // c", "  .(1)", "  z"],
            &["  let z = f // c", "    .(1)", "  z"],
        ),
        body("a method", &["  let z = a // c", "  .abs()", "  z"], &["  let z = a // c", "    .abs()", "  z"]),
        body("a field", &["  let z = p // c", "  .x", "  z"], &["  let z = p // c", "    .x", "  z"]),
        bodyc(
            "a chain with a comment on two lines (the comments of consecutive lines are in one column)",
            &["  let z = a // c1", "  .abs() // c2", "  .max(b)", "  z"],
            &["  let z = a\t// c1", "    .abs()\t// c2", "    .max(b)", "  z"],
        ),
        body("a chain that is a statement", &["  a // c", "  .abs()", "  1"], &["  a // c", "    .abs()", "  1"]),
        body(
            "a chain in a call, on one line",
            &["  h(a   // c", "  .abs(), b)", "  1"],
            &["  h(a // c", "    .abs(), b)", "  1"],
        ),
        body(
            "a chain in a list of the block form",
            &["  h(", "    a // c", "    .abs(),", "    b,", "  )", "  1"],
            &["  h(", "    a // c", "      .abs(),", "    b,", "  )", "  1"],
        ),
    ];
    expect_fmt("comment_before_dot", &cases);
}

#[test]
fn a_line_of_a_comment_inside_a_continuation_is_before_the_next_element() {
    // §3.4: a line of a comment goes before the next element, in the middle of an expression too. The line
    // of the comment is at the column of the line that follows it.
    let cases = vec![
        body(
            "after a binary operator",
            &["  let y = a +", "  // c", "  b", "  y"],
            &["  let y = a +", "    // c", "    b", "  y"],
        ),
        body(
            "before a dot",
            &["  let z = a", "  // c", "  .abs()", "  z"],
            &["  let z = a", "    // c", "    .abs()", "  z"],
        ),
        body("after `=`", &["  let y =", "  // c", "  a + b", "  y"], &["  let y =", "    // c", "    a + b", "  y"]),
    ];
    expect_fmt("comment_line_in_continuation", &cases);
}

#[test]
fn a_line_break_after_a_comment_inside_an_element_stays_at_more_places() {
    // R-201, S-497 (β): inside the brackets the line breaks of an element are removed, except after a comment
    // at the end of a line (§3.2). The line after the comment is one level deeper than the element.
    let cases = vec![
        body(
            "after `as`",
            &["  let y = g(x as   // c", "  F64)", "  y"],
            &["  let y = g(x as // c", "    F64)", "  y"],
        ),
        flow_body(
            "before `at`",
            &["  let y = h(p   // c", "  at sample)", "  y"],
            &["  let y = h(p // c", "    at sample)", "  y"],
        ),
        flow_body(
            "after `at`",
            &["  let y = h(p at   // c", "  sample)", "  y"],
            &["  let y = h(p at // c", "    sample)", "  y"],
        ),
        body(
            "after `if` in an expression",
            &["  let y = g(if   // c", "  a < 0 { 1 } else { 2 })", "  y"],
            &["  let y = g(if // c", "    a < 0 { 1 } else { 2 })", "  y"],
        ),
        body(
            "after `match` in an expression",
            &["  let y = g(match   // c", "  a { 0 => 1, _ => 2 })", "  y"],
            &["  let y = g(match // c", "    a { 0 => 1, _ => 2 })", "  y"],
        ),
        body("after `inout`", &["  h(inout   // c", "  a)", "  1"], &["  h(inout // c", "    a)", "  1"]),
        body(
            "after the colon of a field in the block form",
            &["  let s = S {", "    f:   // c", "    a,", "    g: 1,", "  }", "  s"],
            &["  let s = S {", "    f: // c", "      a,", "    g: 1,", "  }", "  s"],
        ),
        body(
            "after the arrow of an arm in the block form",
            &["  match a {", "    0 =>   // c", "    1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 => // c", "      1,", "    _ => 2,", "  }"],
        ),
        case(
            "after the colon of a parameter",
            &["fn f(a:   // c", "I32) -> I32 {", "  a", "}"],
            &["fn f(a: // c", "  I32) -> I32 {", "  a", "}"],
        ),
        bodyc(
            "a comment on every line of an element",
            &["  let y = g(a +   // one", "  b +   // two", "  c)", "  y"],
            &["  let y = g(a +\t// one", "    b +\t// two", "    c)", "  y"],
        ),
    ];
    expect_fmt("break_after_comment_more", &cases);
}

// ---- the comments the decisions S-528, S-529 and S-530 place ---------------------------------------------

#[test]
fn a_comment_after_a_closing_bracket_that_fmt_moves_to_a_line_of_its_own_stays_after_the_last_code_s528() {
    // S-528: a comment at the end of a line stays after the last code of that line, also when fmt puts the
    // closing bracket of the block form or the `}` of a block over more lines on a line of its own
    // (`b,` and `) // c`). Only the `,` that moves to the element before it goes past a comment.
    let cases = vec![
        case(
            "the arguments of a call",
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b)  // c", "}"],
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b,", "  ) // c", "}"],
        ),
        case(
            "the arguments of a call, the `,` written after the last",
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b,)  // c", "}"],
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b,", "  ) // c", "}"],
        ),
        case(
            "the elements of an array",
            &["fn f() -> [I32; 2] {", "  [", "    1,", "    2]  // c", "}"],
            &["fn f() -> [I32; 2] {", "  [", "    1,", "    2,", "  ] // c", "}"],
        ),
        case(
            "the fields of a struct literal",
            &["struct P { x: I32, y: I32 }", "fn f() -> P {", "  P {", "    x: 1,", "    y: 2 }  // c", "}"],
            &["struct P { x: I32, y: I32 }", "fn f() -> P {", "  P {", "    x: 1,", "    y: 2,", "  } // c", "}"],
        ),
        case(
            "the `}` of a block over more lines",
            &["fn f(a: I32, b: I32) -> I32 {", "  if a > 0 {", "    g(a)", "    g(b) }  // c", "  b", "}"],
            &["fn f(a: I32, b: I32) -> I32 {", "  if a > 0 {", "    g(a)", "    g(b)", "  } // c", "  b", "}"],
        ),
        case(
            "the `}` of a block before `else`",
            &[
                "fn f(a: I32, b: I32) -> I32 {",
                "  if a > 0 {",
                "    g(a)",
                "    g(b) } else { // c",
                "    g(a)",
                "  }",
                "  b",
                "}",
            ],
            &[
                "fn f(a: I32, b: I32) -> I32 {",
                "  if a > 0 {",
                "    g(a)",
                "    g(b)",
                "  } else { // c",
                "    g(a)",
                "  }",
                "  b",
                "}",
            ],
        ),
        case(
            "code after the closing bracket",
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b) + 1  // c", "}"],
            &["fn f(a: I32, b: I32) -> I32 {", "  g(", "    a,", "    b,", "  ) + 1 // c", "}"],
        ),
        case(
            "two closing brackets",
            &["fn f(a: I32, b: I32) -> I32 {", "  g(h(", "    a,", "    b)) // c", "}"],
            &["fn f(a: I32, b: I32) -> I32 {", "  g(h(", "    a,", "    b,", "  )) // c", "}"],
        ),
        case(
            "the closing brackets of two lists of the block form",
            &["fn f() -> I32 {", "  g(", "    [", "      1,", "      2", "    ])  // c", "}"],
            &["fn f() -> I32 {", "  g(", "    [", "      1,", "      2,", "    ],", "  ) // c", "}"],
        ),
    ];
    expect_fmt("s528", &cases);
}

#[test]
fn the_comment_of_a_line_of_a_comma_alone_stays_as_a_line_of_a_comment_in_its_place_s529() {
    // S-529: fmt moves the `,` at the head of a line to the element before it; the comment at the end of
    // that line stays in its place as a line of a comment (before the next element or the closing bracket),
    // whether the line of the element before has a comment or not.
    let cases = vec![
        case(
            "a line of a `,` alone",
            &["fn f() -> I32 {", "  g(", "    1", "    , // c2", "    2", "  )", "}"],
            &["fn f() -> I32 {", "  g(", "    1,", "    // c2", "    2,", "  )", "}"],
        ),
        case(
            "a line of a `,` alone after an element with a comment",
            &["fn f() -> I32 {", "  g(", "    1 // c1", "    , // c2", "    2", "  )", "}"],
            &["fn f() -> I32 {", "  g(", "    1, // c1", "    // c2", "    2,", "  )", "}"],
        ),
        case(
            "a line of a `,` alone before the closing bracket",
            &["fn f() -> [I32; 1] {", "  [", "    1", "    , // c", "  ]", "}"],
            &["fn f() -> [I32; 1] {", "  [", "    1,", "    // c", "  ]", "}"],
        ),
        case(
            "a line of a comment before a line of a `,` alone",
            &["fn f() -> I32 {", "  g(", "    1 // c38", "    // c", "    , // c39", "    2", "  )", "}"],
            &["fn f() -> I32 {", "  g(", "    1, // c38", "    // c", "    // c39", "    2,", "  )", "}"],
        ),
    ];
    expect_fmt("s529", &cases);
}

#[test]
fn a_line_of_a_comment_between_an_element_and_its_comma_stays_before_the_next_element_s530() {
    // S-530: the `,` moves to the element before it, the line of the comment stays before the next element.
    let cases = vec![case(
        "a line of a comment between an element and its `,`",
        &["fn f() -> I32 {", "  g(", "    1", "    // c", "    , 2", "  )", "}"],
        &["fn f() -> I32 {", "  g(", "    1,", "    // c", "    2,", "  )", "}"],
    )];
    expect_fmt("s530", &cases);
}

/// A case whose expected lines may hold the TAB of `cols`.
fn casec(what: impl Into<String>, input: &[&str], expected: &[&str]) -> Case {
    let exp = cols(&strs(expected));
    let exp: Vec<&str> = exp.iter().map(String::as_str).collect();
    case(what, input, &exp)
}

// ---- the comments round an attribute (R-212) -----------------------------------------------------------

#[test]
fn a_comment_between_an_attribute_and_its_item_stays_there() {
    // R-212, §3.4: a plain comment between the attribute and the declaration stays on the line it was
    // written on; it is not moved to the start of the body.
    let cases = vec![
        case(
            "a line of a comment after the attribute of a function",
            &["@fp(relaxed)", "// note", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed)", "// note", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "the line of the comment is not at the column of the item",
            &["@fp( relaxed )", "      // note", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed)", "// note", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a line of a comment after the attribute of a struct",
            &["@repr(c)", "// note", "pub struct P {", "  x: F32,", "}"],
            &["@repr(c)", "// note", "pub struct P {", "  x: F32,", "}"],
        ),
        case(
            "a line of a comment after the attribute of a flow",
            &["@fp(relaxed)", "// note", "pub flow g(x: F32 at sample) -> F32 at sample {", "  x", "}"],
            &["@fp(relaxed)", "// note", "pub flow g(x: F32 at sample) -> F32 at sample {", "  x", "}"],
        ),
        case(
            "two lines of comments",
            &["@fp(relaxed)", "// one", "// two", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed)", "// one", "// two", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a comment before the attribute and a comment between",
            &["// before", "@fp(relaxed)", "// between", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["// before", "@fp(relaxed)", "// between", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a doc comment before the attribute and a comment between",
            &["/// doc", "@fp(relaxed)", "// between", "pub fn f(x: F32) -> F32 {", "  x", "}"],
            &["/// doc", "@fp(relaxed)", "// between", "pub fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "an attribute with the arguments of the block form",
            &["@fp(", "  relaxed, // c", ")", "// note", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(", "  relaxed, // c", ")", "// note", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "an attribute in an impl",
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "  @fp(relaxed)",
                "  // note",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "  @fp(relaxed)",
                "  // note",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
        ),
    ];
    expect_fmt("comment_between_attribute_and_item", &cases);
}

#[test]
fn a_comment_at_the_end_of_the_line_of_an_attribute_stays_on_that_line() {
    let cases = vec![
        case(
            "a function",
            &["@fp(relaxed)   // fast", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed) // fast", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a struct",
            &["@repr(c)// layout", "pub struct P {", "  x: F32,", "}"],
            &["@repr(c) // layout", "pub struct P {", "  x: F32,", "}"],
        ),
        case(
            "the comment of the attribute and the comment of the item are not on the lines of one run",
            &["@fp(relaxed) // fast", "// note", "fn f(x: F32) -> F32 { // body", "  x", "}"],
            &["@fp(relaxed) // fast", "// note", "fn f(x: F32) -> F32 { // body", "  x", "}"],
        ),
    ];
    expect_fmt("attribute_line_comment", &cases);
}

#[test]
fn a_comment_inside_the_brackets_of_an_attribute_stays() {
    let cases = vec![
        case(
            "the closing bracket after a comment",
            &["@fp(relaxed // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "the closing bracket after a comment (loose spaces)",
            &["@fp( relaxed   // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a comment after the opening bracket: the block form",
            &["@fp(   // c", "  relaxed", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp( // c", "  relaxed,", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "a line of a comment before the closing bracket",
            &["@fp(", "  relaxed,", "  // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(", "  relaxed,", "  // c", ")", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
    ];
    expect_fmt("attribute_arguments_comment", &cases);
}

#[test]
fn a_comment_round_the_attribute_of_an_input_of_a_flow_in_the_block_form_stays() {
    // S-501, R-212: the attribute of an input is on a line of its own in the block form; a comment between
    // the attribute and the input stays between them, and a comment at the end of the line of the input
    // stays with the input when the attribute is moved to a line of its own.
    let cases = vec![
        case(
            "a line of a comment between the attribute and the input",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0)",
                "  // note",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0)",
                "  // note",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
        case(
            "a comment at the end of the line of the attribute",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0)   // range",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0) // range",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
        case(
            "the attribute on the line of the input with a comment at the end",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0) level: F32 at block, // level",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0)",
                "  level: F32 at block, // level",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
        casec(
            "comments at the end of the lines of the attribute and of the input",
            &[
                "flow g(",
                "  x: F32 at sample, // signal",
                "  @param(min: 0.0, max: 1.0) // range",
                "  level: F32 at block, // level",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  x: F32 at sample,\t// signal",
                "  @param(min: 0.0, max: 1.0)\t// range",
                "  level: F32 at block,\t// level",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
        case(
            "a doc comment, an attribute and a comment",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  /// the level",
                "  @param(min: 0.0, max: 1.0)",
                "  // note",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  /// the level",
                "  @param(min: 0.0, max: 1.0)",
                "  // note",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
    ];
    expect_fmt("flow_input_attribute_comment", &cases);
}

// ---- the enclosures that hold only a comment (§3.4, S-496, S-502) -----------------------------------------

#[test]
fn a_pair_of_braces_that_holds_only_a_comment_keeps_the_comment_on_its_line() {
    // §3.4: the comment is a content of the enclosure, so the braces are not put on one line and the
    // comment is not moved out. One level deeper than the line that has the opening brace.
    let cases = vec![
        case("a struct", &["struct P {", "// c", "}"], &["struct P {", "  // c", "}"]),
        case(
            "an impl",
            &["pub struct P {", "  x: F32,", "}", "", "impl P {", "// c", "}"],
            &["pub struct P {", "  x: F32,", "}", "", "impl P {", "  // c", "}"],
        ),
        case("a trait", &["trait T {", "      // c", "}"], &["trait T {", "  // c", "}"]),
        case("an effect", &["effect E {", "// c", "}"], &["effect E {", "  // c", "}"]),
        case("a test", &["test \"x\" {", "// c", "}"], &["test \"x\" {", "  // c", "}"]),
        case(
            "a flow",
            &["flow g(x: F32 at sample) -> F32 at sample {", "// c", "}"],
            &["flow g(x: F32 at sample) -> F32 at sample {", "  // c", "}"],
        ),
        case("the body of a function of a unit type", &["fn f() {", "  // c", "}"], &["fn f() {", "  // c", "}"]),
        body(
            "the body of an arm",
            &["  match a {", "    0 => {", "// c", "    },", "    _ => 2,", "  }"],
            &["  match a {", "    0 => {", "      // c", "    },", "    _ => 2,", "  }"],
        ),
        body(
            "a branch of an if",
            &["  if a < 0 {", "// c", "  } else {", "    1", "  }"],
            &["  if a < 0 {", "    // c", "  } else {", "    1", "  }"],
        ),
        body(
            "the branch after else",
            &["  if a < 0 {", "    1", "  } else {", "// c", "  }"],
            &["  if a < 0 {", "    1", "  } else {", "    // c", "  }"],
        ),
        body("a while", &["  while a < 0 {", "// c", "  }", "  1"], &["  while a < 0 {", "    // c", "  }", "  1"]),
        body(
            "a for",
            &["  for i in 0 ..< b {", "// c", "  }", "  1"],
            &["  for i in 0 ..< b {", "    // c", "  }", "  1"],
        ),
        body(
            "a closure",
            &["  let k = fn(x: I32) -> I32 {", "// c", "  }", "  1"],
            &["  let k = fn(x: I32) -> I32 {", "    // c", "  }", "  1"],
        ),
        body("an unsafe block", &["  unsafe {", "// c", "  }", "  1"], &["  unsafe {", "    // c", "  }", "  1"]),
    ];
    expect_fmt("empty_enclosure_comment", &cases);
}

#[test]
fn the_comment_at_the_end_of_the_line_of_an_opening_brace_stays_there_in_an_empty_enclosure() {
    let cases = vec![
        case("a struct", &["struct P { // c", "}"], &["struct P { // c", "}"]),
        case("a struct, loose", &["struct P {   // c", "}"], &["struct P { // c", "}"]),
        case("an impl", &["impl P { // c", "}"], &["impl P { // c", "}"]),
        case("a test", &["test \"x\" { // c", "}"], &["test \"x\" { // c", "}"]),
        body(
            "an arm",
            &["  match a {", "    0 => { // c", "    },", "    _ => 2,", "  }"],
            &["  match a {", "    0 => { // c", "    },", "    _ => 2,", "  }"],
        ),
        body(
            "a branch of an if",
            &["  if a < 0 { // c", "  } else {", "    1", "  }"],
            &["  if a < 0 { // c", "  } else {", "    1", "  }"],
        ),
        case(
            "the comment at the brace and a line of a comment",
            &["fn f() { // one", "// two", "}"],
            &["fn f() { // one", "  // two", "}"],
        ),
    ];
    expect_fmt("empty_enclosure_open_comment", &cases);
}

#[test]
fn the_blank_lines_round_a_comment_in_an_enclosure_follow_the_rule_of_the_first_and_the_last_content() {
    // S-502: a line of a comment is a content; the blank lines before the first and after the last content
    // are removed, the others are kept (at most one).
    let cases = vec![
        case(
            "an impl: a blank line before the first comment goes, after it stays",
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "",
                "  // c",
                "",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "  // c",
                "",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
        ),
        case(
            "a trait: a comment at the end, blank lines before it stay and after it go",
            &["trait T {", "  fn a(self) -> I32", "", "", "  // c", "", "}"],
            &["trait T {", "  fn a(self) -> I32", "", "  // c", "}"],
        ),
        case(
            "an enum",
            &["enum E {", "", "  // c", "", "  A,", "  B,", "}"],
            &["enum E {", "  // c", "", "  A,", "  B,", "}"],
        ),
        body(
            "a list of the block form",
            &["  g(", "", "    // c", "", "    a,", "", "    // d", "", "  )", "  1"],
            &["  g(", "    // c", "", "    a,", "", "    // d", "  )", "  1"],
        ),
        body(
            "a branch of an if with a comment only",
            &["  if a < 0 {", "", "  // c", "", "  } else {", "    1", "  }"],
            &["  if a < 0 {", "    // c", "  } else {", "    1", "  }"],
        ),
    ];
    expect_fmt("blank_lines_round_comments", &cases);
}

// ---- the doc comments ------------------------------------------------------------------------------------

#[test]
fn a_doc_comment_stays_before_its_element() {
    // §2.1: `///` is the doc of the declaration that follows; the fields, the variants and the inputs of a
    // flow can have one. fmt keeps it before that element (R-70, F-4).
    let cases = vec![
        case(
            "a field, at another column",
            &["pub struct P {", "      /// x coordinate", "  x: F32,", "/// y coordinate", "  y: F32", "}"],
            &["pub struct P {", "  /// x coordinate", "  x: F32,", "  /// y coordinate", "  y: F32,", "}"],
        ),
        case(
            "a field with a doc and a comment at the end of the line",
            &["pub struct P {", "  /// x coordinate", "  x: F32, // left", "  y: F32 // up", "}"],
            &["pub struct P {", "  /// x coordinate", "  x: F32, // left", "  y: F32, // up", "}"],
        ),
        case(
            "a variant with a payload and a doc",
            &["pub enum E {", "  /// off", "  Off,", "  /// a level", "  Level(F32) // on", "}"],
            &["pub enum E {", "  /// off", "  Off,", "  /// a level", "  Level(F32), // on", "}"],
        ),
        case(
            "the last field has a doc and no comma",
            &["pub struct P {", "  x: F32,", "  /// y", "  y: F32", "}"],
            &["pub struct P {", "  x: F32,", "  /// y", "  y: F32,", "}"],
        ),
        case(
            "a doc comment of two lines",
            &["pub struct P {", "  /// the first line", "  /// the second line", "  x: F32,", "}"],
            &["pub struct P {", "  /// the first line", "  /// the second line", "  x: F32,", "}"],
        ),
        case(
            "an input of a flow, at another column",
            &[
                "pub flow gain(",
                "/// input signal",
                "  x: Sig[F32],",
                "      /// level",
                "  level: Ctl[F32]",
                ") -> Sig[F32] {",
                "  x * level",
                "}",
            ],
            &[
                "pub flow gain(",
                "  /// input signal",
                "  x: Sig[F32],",
                "  /// level",
                "  level: Ctl[F32],",
                ") -> Sig[F32] {",
                "  x * level",
                "}",
            ],
        ),
        case(
            "a member of an impl",
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "/// the x",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
            &[
                "pub struct P {",
                "  x: F32,",
                "}",
                "",
                "impl P {",
                "  /// the x",
                "  pub fn a(self) -> F32 { self.x }",
                "}",
            ],
        ),
        case(
            "four slashes are a plain comment, also before a field",
            &["pub struct P {", "  //// a line", "  x: F32,", "}"],
            &["pub struct P {", "  //// a line", "  x: F32,", "}"],
        ),
        case(
            "a doc comment, an attribute and a blank line",
            &["/// doc", "", "@repr(c)", "pub struct P {", "  x: F32,", "}"],
            &["/// doc", "", "@repr(c)", "pub struct P {", "  x: F32,", "}"],
        ),
        text(
            "a module doc and a doc of an item",
            "//! the module\n\n/// the function\nfn f() -> I32 {\n  1\n}\n",
            "//! the module\n\n/// the function\nfn f() -> I32 {\n  1\n}\n",
        ),
    ];
    expect_fmt("doc_comments", &cases);
}

// ---- the combinations ------------------------------------------------------------------------------------

#[test]
fn comments_in_nested_forms_stay_where_they_were_written() {
    // A list in a list, a branch, a closure, a generic function, a `par` and a `use` list in one file.
    let input = "\
// the module
use std.math.{sin,   // wave
cos}

/// the point
pub struct P[T] {
  x: T, // left
  y: T // up
}

pub fn pick[T,   // the type
  U](a: T, b: U) -> T {   // keep a
  // look
  let c = if a < b { // smaller
    // first
    a
  } else { // other
    b
    // last
  }
  let k = fn(z: T) -> T { // closure
    z
  }
  g(k.(c), [
    1,   // one
    2 // two
  ])
}

pub flow w(f0: F32 at block) -> F32 at sample {
  let s = par i in 0 ..< 4 { // copies
    saw~(f0 *   // scaled
      2.0)
  }
  sum(s)
}
";
    let expected = "\
// the module
use std.math.{sin, // wave
              cos}

/// the point
pub struct P[T] {
  x: T, // left
  y: T, // up
}

pub fn pick[T,                    // the type
            U](a: T, b: U) -> T { // keep a
  // look
  let c = if a < b { // smaller
    // first
    a
  } else { // other
    b
    // last
  }
  let k = fn(z: T) -> T { // closure
    z
  }
  g(k.(c), [
    1, // one
    2, // two
  ])
}

pub flow w(f0: F32 at block) -> F32 at sample {
  let s = par i in 0 ..< 4 { // copies
    saw~(f0 *                // scaled
      2.0)
  }
  sum(s)
}
";
    expect_fmt("nested_forms", &[text("a file with the nested forms", input, expected)]);
}

// ---- the columns of the comments, the text of the comments ---------------------------------------------------

#[test]
fn the_comments_of_consecutive_lines_are_in_one_column_and_a_line_without_a_comment_ends_the_run() {
    // §3.2: the comments at the end of consecutive lines are in one column, one space after the longest
    // code. A line with no comment, and a blank line, ends the run; a comment alone on a line is not in it.
    let cases = vec![
        bodyc(
            "three lines",
            &["  g(a) // one", "  g(bbbb, c) // two", "  g(d)   // three", "  1"],
            &["  g(a)\t// one", "  g(bbbb, c)\t// two", "  g(d)\t// three", "  1"],
        ),
        body(
            "a line with no comment between: two runs of one line, one space",
            &["  g(a)      // one", "  g(bbbb, c)", "  g(d)      // three", "  1"],
            &["  g(a) // one", "  g(bbbb, c)", "  g(d) // three", "  1"],
        ),
        body(
            "a blank line between",
            &["  g(a)      // one", "", "  g(bbbb, c)      // two", "  1"],
            &["  g(a) // one", "", "  g(bbbb, c) // two", "  1"],
        ),
        bodyc(
            "the lines of different depths are one run",
            &["  if a < 0 { // one", "    1 // two", "  } else { // three", "    2 // four", "  } // five"],
            &["  if a < 0 {\t// one", "    1\t// two", "  } else {\t// three", "    2\t// four", "  }\t// five"],
        ),
        bodyc(
            "a line that holds only an opening bracket",
            &["  g( // one", "    a, // two", "    bbbb, // three", "  )"],
            &["  g(\t// one", "    a,\t// two", "    bbbb,\t// three", "  )"],
        ),
    ];
    expect_fmt("comment_columns", &cases);
}

#[test]
fn a_comment_keeps_its_text_and_a_string_with_two_slashes_is_not_a_comment() {
    // §2.1: the text of a comment is kept (`/*` and `*/` in a line comment are text, `///` and `////`
    // differ only by the doc); `//` in a string is not a comment (§2.4).
    let cases = vec![
        bodyc(
            "a string with two slashes before a comment",
            &["  g(\"http://x\") // one", "  g(\"a\") // two", "  1"],
            &["  g(\"http://x\")\t// one", "  g(\"a\")\t// two", "  1"],
        ),
        body(
            "the text of the comments",
            &["  g(a) //", "  g(b)", "  // /* x */ and */", "  g(c) // a  b   c", "  g(d)", "  //\tt", "  1"],
            &["  g(a) //", "  g(b)", "  // /* x */ and */", "  g(c) // a  b   c", "  g(d)", "  //\tt", "  1"],
        ),
        body(
            "no space between the code and the comment",
            &["  g(a)// one", "  g(b)", "  1"],
            &["  g(a) // one", "  g(b)", "  1"],
        ),
        body(
            "a comment with the characters of other scripts",
            &["  g(a) // 日本語のコメント", "  1"],
            &["  g(a) // 日本語のコメント", "  1"],
        ),
    ];
    expect_fmt("comment_text", &cases);
}

// ---- the 17 forms of the review R-70 ---------------------------------------------------------------------

#[test]
fn the_seventeen_forms_of_r70_are_not_changed_by_fmt() {
    // R-70, S-58: the files are in the normal form, the comments are on the lines and before the elements
    // where they are written; the doc comments of a field, a variant and an input of a flow stay before
    // their element; fmt changes nothing.
    assert_eq!(R70.len(), 17);
    let cases: Vec<Case> = R70.iter().map(|(name, t)| text(*name, t, t)).collect();
    expect_fmt("r70", &cases);
}

// ---- the diagnostics of the syntax stage that concern a comment -------------------------------------------

#[test]
fn a_file_with_a_brace_after_a_comment_on_another_line_is_refused() {
    // E0003 (§2.5): a comment does not let the `{` or the `else` stand on a line of its own.
    expect_refused(
        "e0003_comment",
        "E0003",
        &[
            ("a brace after the heading and its comment", "fn f() -> I32 // c\n{\n  1\n}\n".to_string()),
            (
                "a brace after the condition and its comment",
                "fn f(a: Bool) -> I32 {\n  if a // c\n  {\n    1\n  } else {\n    2\n  }\n}\n".to_string(),
            ),
            (
                "an else after the closing brace and its comment",
                "fn f(a: Bool) -> I32 {\n  if a {\n    1\n  } // c\n  else {\n    2\n  }\n}\n".to_string(),
            ),
            (
                "an else after a line of a comment",
                "fn f(a: Bool) -> I32 {\n  if a {\n    1\n  }\n  // c\n  else {\n    2\n  }\n}\n".to_string(),
            ),
        ],
    );
}

#[test]
fn a_doc_comment_that_documents_nothing_is_refused() {
    // E0004 (§2.1).
    expect_refused(
        "e0004_doc",
        "E0004",
        &[
            ("before a statement", "fn f() -> I32 {\n  /// doc\n  1\n}\n".to_string()),
            ("at the end of the file", "fn f() -> I32 {\n  1\n}\n/// end\n".to_string()),
            ("a module doc after an item", "fn f() -> I32 {\n  1\n}\n\n//! late\n".to_string()),
            ("after an attribute", "@fp(relaxed)\n/// doc\nfn f(x: F32) -> F32 {\n  x\n}\n".to_string()),
            ("before a parameter", "fn f(\n  /// doc\n  x: I32,\n) -> I32 {\n  x\n}\n".to_string()),
            ("before a use", "use std.math.{sin}\n/// doc of a use\nuse std.math.{cos}\n".to_string()),
        ],
    );
}

#[test]
fn a_block_comment_is_refused() {
    // E0020 for a closed block comment, E0002 for the others (§2.1).
    expect_refused(
        "e0020_block_comment",
        "E0020",
        &[
            ("at the end of a line", "fn f() -> I32 {\n  1 /* c */\n}\n".to_string()),
            ("over two lines", "fn f() -> I32 {\n  /* a\n  b */\n  1\n}\n".to_string()),
            ("inside an expression", "fn f() -> I32 {\n  let x = 1 + /* c */ 2\n  x\n}\n".to_string()),
            ("inside a list", "fn f() -> I32 {\n  let x = [\n    1, /* c */\n    2,\n  ]\n  1\n}\n".to_string()),
        ],
    );
    expect_refused(
        "e0002_block_comment",
        "E0002",
        &[
            ("never closed", "fn f() -> I32 {\n  /* never closed\n  1\n}\n".to_string()),
            ("nested", "fn f() -> I32 {\n  /* a /* b */ c */\n  1\n}\n".to_string()),
            ("code after the end of it", "fn f() -> I32 {\n  let a = 1 /* x\n  */ + 2\n  a\n}\n".to_string()),
        ],
    );
}
