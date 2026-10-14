//! What `onsa fmt` writes for a file that is not in the canonical form of the lines and the lists, by the
//! whole text of the output (W3-11/t, unit U3b; `docs/onsa-tools.md` §3.2, §3.4, spec §2.5, §18.2; plan
//! S-122, S-201, S-328, S-496, S-497, S-499 to S-502, S-505, S-507, S-510).
//!
//! The case files in `tests/spec/fmt/` pin that the canonical files are a fixed point of `fmt`. These tests
//! pin the rewriting: the input is not canonical, the expected text is the whole canonical file, and the
//! output is a fixed point (`fmt --check` ends with 0 and another `fmt` changes nothing). Both the input
//! and the expected text must have no diagnostic of the syntax stage (a file with one is not rewritten,
//! `onsa fmt` ends with 2, §18.2); every test checks it for the expected text (`fmt --check` does not end
//! with 2) and for the input (`fmt` ends with 0).
//!
//! The rules, from `docs/onsa-tools.md` §3.2 and §3.4:
//! - a list is in one of three forms by the writer's line breaks, for every kind of list (S-510, S-328):
//!   the arguments, the parameters of a declaration, the elements of an array and a tuple, the fields of a
//!   struct literal, a struct, an enum and a pattern, the arms of a `match`, the inputs of a flow, and the
//!   seven that were folded onto one line: the arguments of an attribute, the elements of a variant, an
//!   effect row and a `use` list, the type arguments (of a type and of an expression's `::[…]`) and the type
//!   parameters, the tuple type and the arguments of a function type. One line: no `,` after the last
//!   element. Block form: a `,` after every element, the closing bracket on a line of its own.
//!   Continuation: the elements under the first, no `,` after the last. The closing bracket of the one-line
//!   form and of the continuation follows the last element (S-507);
//! - the `..` of the pattern of a struct is not an element: in the block form no `,` follows it (S-500);
//! - the line breaks inside an element stay only at the places of a continuation (§2.5): the end of a line
//!   with a binary operator, a range symbol, `=`, `->`, an attribute or the `|` of a pattern, the start of
//!   a line with `.`. The others (after `=>` and `:`, round `as` and `at`, after a keyword in an
//!   expression, before the closing bracket of the one-line form and of the continuation, between
//!   `@mem(bulk)` and `let`) become one space; a line break after a comment at the end of a line stays
//!   at every place (S-497 (2) and (β), S-505, S-507);
//! - an attribute of an item and of an input in the block form is on a line of its own, an attribute of
//!   an input in the one-line form and the continuation is on the line of the input (S-501);
//! - the blank lines: at most one, between items, statements and elements of a list; none at the start
//!   and the end of a block, a list and the file (the start and the end are the first and the last
//!   content, a comment counts), none between the lines of a continuation and inside an element
//!   (S-122, S-499, S-502);
//! - CR LF is LF (S-201); an empty `{}` has no space and no line break inside, unless it has a comment
//!   (S-496, §3.4).
//!
//! What is not here: the fixed points (the case files of the unit U3a), the places of the comments that
//! move in a list (unit U4), the lists with no element (S-513), the spelling of a tuple index (S-508), the
//! rewrites of the tree (W3-12) and the check before writing (unit U5). The three tests of
//! `fmt_spaces_lists.rs` that waited for unit U3 (a `use` list and a pattern in the block form and the continuation, an attribute
//! of an input in the block form) are there and are not written again.
//!
//! Every test uses only the binary (`onsa fmt`). Expected texts are written from the spec; none is taken
//! from the output of the compiler. The tests that wait for W3-11 are `#[ignore]`d; each ignore names the
//! work that removes it and what differs.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // The counter makes the directory the test's own even when two tests use the same tag.
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_u3b_{}_{n}_{tag}", std::process::id()));
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

/// Runs `onsa fmt` on every input (one command, so the files are written one after the other), compares
/// the whole text of each output, and checks that the output is a fixed point: `fmt --check` ends with 0
/// and another `fmt` does not change the file. Before that, the expected text is checked to have no
/// diagnostic of the syntax stage (`fmt --check` ends with 0 or 1, not with 2).
fn expect_fmt(tag: &str, cases: &[Case]) {
    assert!(!cases.is_empty(), "no case to run");
    let d = Dir::new(tag);
    for (i, c) in cases.iter().enumerate() {
        let p = d.file(&format!("e{i}.onsa"), &c.expected);
        let out = onsa(&["fmt", "--check", &p]);
        assert_ne!(code(&out), 2, "{}: the expected text has a diagnostic of the syntax stage: {out:?}", c.what);
    }
    let paths: Vec<String> = cases.iter().enumerate().map(|(i, c)| d.file(&format!("c{i}.onsa"), &c.input)).collect();
    let mut args = vec!["fmt"];
    args.extend(paths.iter().map(String::as_str));
    let out = onsa(&args);
    assert_eq!(code(&out), 0, "onsa fmt: {out:?}");
    let mut wrong = Vec::new();
    for (c, path) in cases.iter().zip(&paths) {
        let got = read(path);
        if got != c.expected {
            wrong.push(format!("{}\n--- input\n{}--- expected\n{}--- got\n{got}", c.what, c.input, c.expected));
        }
    }
    assert!(wrong.is_empty(), "{} of {} files are not as expected:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    for (c, path) in cases.iter().zip(&paths) {
        let out = onsa(&["fmt", "--check", path]);
        assert_eq!(code(&out), 0, "{}: the output is not a fixed point of fmt --check: {out:?}", c.what);
        let out = onsa(&["fmt", path]);
        assert_eq!(code(&out), 0, "{}: {out:?}", c.what);
        assert_eq!(read(path), c.expected, "{}: a second fmt changes the output", c.what);
    }
}

/// Every input is refused: `onsa fmt` ends with 2, names `diag` in its output (diagnostics go to the
/// standard output, `docs/onsa-tools.md` §3.1) and does not touch the file.
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

// ---- the three forms of every kind of list ---------------------------------------------------------

/// One list in a file: the lines before, the line of the opening bracket (up to and including the bracket,
/// with its indentation), the elements, the closing bracket, the text that follows it on its line, and the
/// lines after. `pad` is a list whose braces have a space inside when it is on one line.
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

/// A writing of a list. `One`: all the elements on the line of the opening bracket (`trail`: a `,` after
/// the last; `next`: the closing bracket on the next line). `Block`: a line break after the opening
/// bracket (`last_comma`: a `,` after the last; `close_last`: the closing bracket on the line of the last
/// element). `Cont`: the elements under the first (`trail`, `next` as in `One`).
#[derive(Clone, Copy, Debug)]
enum Shape {
    One { trail: bool, next: bool },
    Block { last_comma: bool, close_last: bool },
    Cont { trail: bool, next: bool },
}
use Shape::{Block, Cont, One};

/// The written forms that are not canonical, by form. The canonical forms are `One` with nothing, `Block`
/// with the comma and the bracket on its own line, and `Cont` with nothing.
const ONE: &[Shape] =
    &[One { trail: true, next: false }, One { trail: false, next: true }, One { trail: true, next: true }];
const BLOCK: &[Shape] = &[
    Block { last_comma: false, close_last: false },
    Block { last_comma: false, close_last: true },
    Block { last_comma: true, close_last: true },
];
const CONT: &[Shape] =
    &[Cont { trail: true, next: false }, Cont { trail: false, next: true }, Cont { trail: true, next: true }];

fn canonical(s: Shape) -> Shape {
    match s {
        One { .. } => One { trail: false, next: false },
        Block { .. } => Block { last_comma: true, close_last: false },
        Cont { .. } => Cont { trail: false, next: false },
    }
}

fn render(k: &Kind, s: Shape) -> String {
    let ind = " ".repeat(k.pre.len() - k.pre.trim_start().len());
    let sp = if k.pad { " " } else { "" };
    let n = k.elems.len();
    let mut v: Vec<String> = k.head.iter().map(|l| l.to_string()).collect();
    match s {
        One { trail, next } => {
            let mut l = format!("{}{sp}{}", k.pre, k.elems.join(", "));
            if trail {
                l.push(',');
            }
            if next {
                v.push(l);
                v.push(format!("{ind}{}{}", k.close, k.post));
            } else {
                l.push_str(&format!("{sp}{}{}", k.close, k.post));
                v.push(l);
            }
        }
        Block { last_comma, close_last } => {
            v.push(k.pre.to_string());
            for (i, e) in k.elems.iter().enumerate() {
                let last = i == n - 1;
                let mut l = format!("{ind}  {e}");
                if !last || last_comma {
                    l.push(',');
                }
                if last && close_last {
                    l.push_str(&format!("{sp}{}{}", k.close, k.post));
                }
                v.push(l);
            }
            if !close_last {
                v.push(format!("{ind}{}{}", k.close, k.post));
            }
        }
        Cont { trail, next } => {
            let col = " ".repeat(k.pre.len() + sp.len());
            for (i, e) in k.elems.iter().enumerate() {
                let last = i == n - 1;
                let mut l = if i == 0 { format!("{}{sp}{e}", k.pre) } else { format!("{col}{e}") };
                if !last || trail {
                    l.push(',');
                }
                if last && !next {
                    l.push_str(&format!("{sp}{}{}", k.close, k.post));
                }
                v.push(l);
            }
            if next {
                v.push(format!("{ind}{}{}", k.close, k.post));
            }
        }
    }
    v.extend(k.tail.iter().map(|l| l.to_string()));
    src_s(&v)
}

fn list_cases(k: &Kind, shapes: &[Shape]) -> Vec<Case> {
    shapes
        .iter()
        .map(|&s| Case { what: format!("{}: {s:?}", k.name), input: render(k, s), expected: render(k, canonical(s)) })
        .collect()
}

macro_rules! list_test {
    ($name:ident, $kind:expr, $shapes:expr) => {
        #[test]
        fn $name() {
            expect_fmt(stringify!($name), &list_cases(&$kind, $shapes));
        }
    };
    ($name:ident, $kind:expr, $shapes:expr, $why:literal) => {
        #[test]
        #[ignore = $why]
        fn $name() {
            expect_fmt(stringify!($name), &list_cases(&$kind, $shapes));
        }
    };
}

// The seven kinds that `fmt` folded onto one line (S-510, S-328), and the other kinds of §3.2.

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

// S-510, S-328: the arguments of an attribute.
list_test!(attribute_arguments_one_line, K_ATTR_ARGS, ONE);
list_test!(attribute_arguments_block, K_ATTR_ARGS, BLOCK);
list_test!(attribute_arguments_continuation, K_ATTR_ARGS, CONT);

// The elements of a variant of an enum.
list_test!(variant_elements_one_line, K_VARIANT, ONE);
list_test!(variant_elements_block, K_VARIANT, BLOCK);
list_test!(variant_elements_continuation, K_VARIANT, CONT);

// An effect row.
list_test!(effect_row_one_line, K_EFFECT_ROW, ONE);
list_test!(effect_row_block, K_EFFECT_ROW, BLOCK);
list_test!(effect_row_continuation, K_EFFECT_ROW, CONT);

// A `use` list: the block form and the continuation are in `fmt_spaces_lists.rs`; here are the
// forms that file does not place.
list_test!(use_list_one_line, K_USE, &[One { trail: false, next: true }, One { trail: true, next: true }]);
list_test!(use_list_continuation, K_USE, &[Cont { trail: false, next: true }, Cont { trail: true, next: true }]);

// The type arguments of a type, of an expression (`::[…]`) and the type parameters.
list_test!(type_arguments_one_line, K_TYPE_ARGS, ONE);
list_test!(type_arguments_block, K_TYPE_ARGS, BLOCK);
list_test!(type_arguments_continuation, K_TYPE_ARGS, CONT);
list_test!(expression_type_arguments_one_line, K_EXPR_TYPE_ARGS, ONE);
list_test!(expression_type_arguments_block, K_EXPR_TYPE_ARGS, BLOCK);
list_test!(expression_type_arguments_continuation, K_EXPR_TYPE_ARGS, CONT);
list_test!(type_parameters_one_line, K_TYPE_PARAMS, ONE);
list_test!(type_parameters_block, K_TYPE_PARAMS, BLOCK);
list_test!(type_parameters_continuation, K_TYPE_PARAMS, CONT);

// A tuple type and the arguments of a function type.
list_test!(tuple_type_one_line, K_TUPLE_TYPE, ONE);
list_test!(tuple_type_block, K_TUPLE_TYPE, BLOCK);
list_test!(tuple_type_continuation, K_TUPLE_TYPE, CONT);
list_test!(function_type_arguments_one_line, K_FN_TYPE, ONE);
list_test!(function_type_arguments_block, K_FN_TYPE, BLOCK);
list_test!(function_type_arguments_continuation, K_FN_TYPE, CONT);

// The kinds of unit U2, the forms that are not in `fmt_spaces_lists.rs`.
list_test!(parameters_one_line, K_PARAMS, &[One { trail: false, next: true }, One { trail: true, next: true }]);
list_test!(parameters_block, K_PARAMS, &[Block { last_comma: true, close_last: true }]);
list_test!(parameters_continuation, K_PARAMS, &[Cont { trail: false, next: true }, Cont { trail: true, next: true }]);
list_test!(array_continuation, K_ARRAY, &[Cont { trail: true, next: false }, Cont { trail: true, next: true }]);
list_test!(array_one_line, K_ARRAY, &[One { trail: true, next: true }]);
list_test!(tuple_one_line, K_TUPLE, &[One { trail: false, next: true }, One { trail: true, next: true }]);
list_test!(
    tuple_block,
    K_TUPLE,
    &[Block { last_comma: false, close_last: true }, Block { last_comma: true, close_last: true }]
);
list_test!(tuple_continuation, K_TUPLE, CONT);
list_test!(struct_literal_one_line, K_STRUCT_LIT, &[One { trail: false, next: true }, One { trail: true, next: true }]);
list_test!(struct_literal_block, K_STRUCT_LIT, &[Block { last_comma: true, close_last: true }]);
list_test!(
    struct_literal_continuation,
    K_STRUCT_LIT,
    &[Cont { trail: true, next: false }, Cont { trail: true, next: true }]
);
list_test!(flow_inputs_one_line, K_FLOW_INPUTS, &[One { trail: false, next: true }, One { trail: true, next: true }]);
list_test!(
    flow_inputs_block,
    K_FLOW_INPUTS,
    &[Block { last_comma: false, close_last: true }, Block { last_comma: true, close_last: true }]
);
list_test!(flow_inputs_continuation, K_FLOW_INPUTS, CONT);
list_test!(struct_fields_one_line, K_STRUCT_DECL, ONE);
list_test!(struct_fields_block, K_STRUCT_DECL, &[Block { last_comma: true, close_last: true }]);
list_test!(struct_fields_continuation, K_STRUCT_DECL, CONT);
list_test!(enum_variants_one_line, K_ENUM_DECL, ONE);
list_test!(enum_variants_block, K_ENUM_DECL, &[Block { last_comma: true, close_last: true }]);
list_test!(enum_variants_continuation, K_ENUM_DECL, CONT);
list_test!(match_arms_one_line, K_MATCH, ONE);
list_test!(match_arms_block, K_MATCH, &[Block { last_comma: true, close_last: true }]);
list_test!(match_arms_continuation, K_MATCH, CONT);
list_test!(
    tuple_pattern_one_line,
    K_TUPLE_PATTERN,
    &[One { trail: false, next: true }, One { trail: true, next: true }]
);
list_test!(tuple_pattern_block, K_TUPLE_PATTERN, BLOCK);
list_test!(tuple_pattern_continuation, K_TUPLE_PATTERN, CONT);
list_test!(
    struct_pattern_one_line,
    K_STRUCT_PATTERN,
    &[One { trail: false, next: true }, One { trail: true, next: true }]
);
list_test!(struct_pattern_block, K_STRUCT_PATTERN, BLOCK);
list_test!(struct_pattern_continuation, K_STRUCT_PATTERN, CONT);
list_test!(
    variant_pattern_one_line,
    K_VARIANT_PATTERN,
    &[One { trail: false, next: true }, One { trail: true, next: true }]
);
list_test!(variant_pattern_block, K_VARIANT_PATTERN, BLOCK);
list_test!(variant_pattern_continuation, K_VARIANT_PATTERN, CONT);

// ---- a list of one element, and a grouping ------------------------------------------------------------

/// A list of one element of each of the seven kinds (and the type arguments of an expression).
fn single_kinds() -> Vec<Kind> {
    vec![
        Kind {
            name: "the arguments of an attribute",
            head: &["flow g("],
            pre: "  @param(",
            pad: false,
            elems: &["default: 0.5"],
            close: ")",
            post: "",
            tail: &["  level: F32 at block,", ") -> F32 at sample {", "  level", "}"],
        },
        Kind {
            name: "the elements of a variant",
            head: &["enum E {", "  A,"],
            pre: "  B(",
            pad: false,
            elems: &["I32"],
            close: ")",
            post: ",",
            tail: &["}"],
        },
        Kind {
            name: "an effect row",
            head: &[],
            pre: "fn g() -> I32 uses {",
            pad: false,
            elems: &["Alloc"],
            close: "}",
            post: " {",
            tail: &["  1", "}"],
        },
        Kind {
            name: "a use list",
            head: &[],
            pre: "use std.math.{",
            pad: false,
            elems: &["sin"],
            close: "}",
            post: "",
            tail: &[],
        },
        Kind {
            name: "the type arguments of a type",
            head: &["fn g(a: I32) -> I32 {"],
            pre: "  let r: Buf[",
            pad: false,
            elems: &["F32"],
            close: "]",
            post: " = f(a)",
            tail: &["  1", "}"],
        },
        Kind {
            name: "the type arguments of an expression",
            head: &["fn g(a: I32) -> I32 {"],
            pre: "  let r = h::[",
            pad: false,
            elems: &["I32"],
            close: "]",
            post: "(a)",
            tail: &["  1", "}"],
        },
        Kind {
            name: "the type parameters",
            head: &[],
            pre: "fn g[",
            pad: false,
            elems: &["T"],
            close: "]",
            post: "(a: T) -> T {",
            tail: &["  a", "}"],
        },
        Kind {
            name: "the arguments of a function type",
            head: &[],
            pre: "type Op = fn(",
            pad: false,
            elems: &["I32"],
            close: ")",
            post: " -> I32",
            tail: &[],
        },
    ]
}

#[test]
fn a_list_of_one_element_of_the_seven_kinds_loses_its_last_comma_on_one_line() {
    let mut cases = Vec::new();
    for k in single_kinds() {
        cases.push(Case {
            what: format!("{}: one line with a comma", k.name),
            input: render(&k, One { trail: true, next: false }),
            expected: render(&k, One { trail: false, next: false }),
        });
    }
    expect_fmt("single_element_one_line", &cases);
}

#[test]
fn a_list_of_one_element_of_the_seven_kinds_gets_the_comma_in_the_block_form() {
    // S-510, S-328: the block form has a `,` after every element, also when there is one.
    let mut cases = Vec::new();
    for k in single_kinds() {
        for s in [Block { last_comma: false, close_last: false }, Block { last_comma: false, close_last: true }] {
            cases.push(Case {
                what: format!("{}: {s:?}", k.name),
                input: render(&k, s),
                expected: render(&k, Block { last_comma: true, close_last: false }),
            });
        }
    }
    expect_fmt("single_element_block", &cases);
}

#[test]
fn a_type_in_parentheses_is_a_grouping_and_gets_no_comma_in_the_block_form() {
    // `(I32)` is a grouping, not a list of one element (`(I32,)` is E0002, spec §2.4): no `,` is added.
    let cases = vec![
        case("the closing bracket after the type", &["type T = (", "  I32)"], &["type T = (", "  I32", ")"]),
        case("not indented", &["type T = (", "I32", ")"], &["type T = (", "  I32", ")"]),
    ];
    expect_fmt("grouping", &cases);
}

// ---- the `..` of the pattern of a struct (S-500) ---------------------------------------------------

#[test]
fn the_rest_of_a_struct_pattern_is_not_an_element_and_gets_no_comma() {
    // `..` is an error of a later stage (E0020, spec §7), not of the syntax stage, so `fmt` writes the file.
    let cases = vec![
        body(
            "the one-line form without spaces",
            &["  let P {x:a,y:b,..} = p", "  a"],
            &["  let P { x: a, y: b, .. } = p", "  a"],
        ),
        body(
            "the one-line form, the brace on the next line",
            &["  let P { x: a, ..", "  } = p", "  a"],
            &["  let P { x: a, .. } = p", "  a"],
        ),
        body(
            "the pattern of an arm, the one-line form",
            &["  match a {", "    P {x: 0,..} => 1,", "    _ => 2,", "  }"],
            &["  match a {", "    P { x: 0, .. } => 1,", "    _ => 2,", "  }"],
        ),
    ];
    expect_fmt("rest_pattern", &cases);
}

#[test]
fn the_rest_of_a_struct_pattern_in_the_block_form_and_the_continuation_is_not_an_element() {
    // `..` is an error of a later stage (E0020, spec §7), not of the syntax stage, so `fmt` writes the file.
    let cases = vec![
        body(
            "the block form, not indented",
            &["  let P {", "x: a,", "      y: b,", "..", "  } = p", "  a"],
            &["  let P {", "    x: a,", "    y: b,", "    ..", "  } = p", "  a"],
        ),
        body(
            "the block form, the brace after the rest",
            &["  let P {", "    x: a,", "    ..} = p", "  a"],
            &["  let P {", "    x: a,", "    ..", "  } = p", "  a"],
        ),
        body(
            "the block form of the rest alone",
            &["  let P {", "..", "  } = p", "  a"],
            &["  let P {", "    ..", "  } = p", "  a"],
        ),
        body(
            "the continuation, the brace after the rest",
            &["  let P { x: a,", "..} = p", "  a"],
            &["  let P { x: a,", "          .. } = p", "  a"],
        ),
        body(
            "the continuation, the brace on the next line",
            &["  let P { x: a,", "          ..", "  } = p", "  a"],
            &["  let P { x: a,", "          .. } = p", "  a"],
        ),
        body(
            "the pattern of an arm, the block form",
            &["  match a {", "    P {", "x: 0,", "      ..", "    } => 1,", "    _ => 2,", "  }"],
            &["  match a {", "    P {", "      x: 0,", "      ..", "    } => 1,", "    _ => 2,", "  }"],
        ),
    ];
    expect_fmt("rest_pattern_w", &cases);
}

#[test]
fn a_comma_after_the_rest_of_a_struct_pattern_is_refused_and_the_file_stays() {
    // S-500: `..,` is E0002 (a diagnostic of the syntax stage), so `fmt` does not add or keep it: it does not
    // write the file.
    let wrap = |lines: &[&str]| in_fn(lines).join("\n") + "\n";
    let inputs: Vec<(&str, String)> = vec![
        ("the block form", wrap(&["  let P {", "    x: a,", "    ..,", "  } = p", "  a"])),
        ("the one-line form", wrap(&["  let P { x: a, .., } = p", "  a"])),
        ("the continuation", wrap(&["  let P { x: a,", "          .., } = p", "  a"])),
    ];
    expect_refused("rest_comma", "E0002", &inputs);
}

#[test]
fn a_line_that_starts_with_a_binary_symbol_inside_a_list_is_refused_and_the_file_stays() {
    // §2.5: a binary operator, a range symbol and the `|` of a pattern stand at the end of a line, also
    // inside the brackets; at the start of a line they are E0020 and `fmt` does not write the file.
    let wrap = |lines: &[&str]| in_fn(lines).join("\n") + "\n";
    let inputs: Vec<(&str, String)> = vec![
        ("a plus", wrap(&["  two(a", "    + b, 1)"])),
        ("a comparison", wrap(&["  two(a", "    == b, 1)"])),
        ("a logical and in the block form", wrap(&["  two(", "    a", "      && b,", "    1,", "  )"])),
        ("the bar of a pattern", wrap(&["  match a {", "    0", "      | 1 => 1,", "    _ => 2,", "  }"])),
    ];
    expect_refused("line_start_symbol", "E0020", &inputs);
}

// ---- the line breaks inside an element (S-497, S-505) ------------------------------------------------

#[test]
fn a_line_break_after_an_arrow_or_a_colon_inside_a_list_is_one_space() {
    let cases = vec![
        body(
            "after the arrow of an arm",
            &["  match a {", "    0 =>", "      1,", "    _ =>", "  2,", "  }"],
            &["  match a {", "    0 => 1,", "    _ => 2,", "  }"],
        ),
        body(
            "after the colon of a field in the one-line form",
            &["  let s = S { f:", "    a, g: 1 }", "  s"],
            &["  let s = S { f: a, g: 1 }", "  s"],
        ),
        body(
            "after the colon of a field in the block form",
            &["  let s = S {", "    f:", "      a,", "    g: 1,", "  }", "  s"],
            &["  let s = S {", "    f: a,", "    g: 1,", "  }", "  s"],
        ),
        body(
            "after the colon of a parameter",
            &["  let h = fn(x:", "    I32) -> I32 {", "    x", "  }", "  1"],
            &["  let h = fn(x: I32) -> I32 {", "    x", "  }", "  1"],
        ),
        case(
            "after the colon of a parameter of a declaration",
            &["fn h(x:", "I32) -> I32 {", "  x", "}"],
            &["fn h(x: I32) -> I32 {", "  x", "}"],
        ),
        case(
            "after the colon of a field of a struct",
            &["struct S {", "  f:", "    F32,", "  g: F32,", "}"],
            &["struct S {", "  f: F32,", "  g: F32,", "}"],
        ),
    ];
    expect_fmt("break_after_arrow_colon", &cases);
}

#[test]
fn a_line_break_before_an_arrow_or_a_colon_inside_a_list_is_one_space() {
    // S-505: the arrow and the colon at the start of a line, inside the brackets.
    let cases = vec![
        body(
            "before the arrow of an arm",
            &["  match a {", "    0", "      => 1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 => 1,", "    _ => 2,", "  }"],
        ),
        body(
            "before the colon of a field in the one-line form",
            &["  let s = S { f", "    : a }", "  s"],
            &["  let s = S { f: a }", "  s"],
        ),
        body(
            "before the colon of a field in the block form",
            &["  let s = S {", "    f", "      : a,", "    g: 1,", "  }", "  s"],
            &["  let s = S {", "    f: a,", "    g: 1,", "  }", "  s"],
        ),
        case(
            "before the colon of a parameter of a declaration",
            &["fn h(x", ": I32) -> I32 {", "  x", "}"],
            &["fn h(x: I32) -> I32 {", "  x", "}"],
        ),
    ];
    expect_fmt("break_before_arrow_colon", &cases);
}

#[test]
fn a_line_break_round_as_and_at_inside_a_list_is_one_space() {
    let cases = vec![
        body("before `as`", &["  g(x", "    as F64)"], &["  g(x as F64)"]),
        body("after `as`", &["  g(x as", "    F64)"], &["  g(x as F64)"]),
        body("before and after `as`", &["  g(x", "    as", "    F64, b)"], &["  g(x as F64, b)"]),
        body(
            "before `as` in the block form",
            &["  g(", "    x", "      as F64,", "    b,", "  )"],
            &["  g(", "    x as F64,", "    b,", "  )"],
        ),
        flow_body("before `at`", &["  k(p", "    at sample)"], &["  k(p at sample)"]),
        flow_body("after `at`", &["  k(p at", "    sample)"], &["  k(p at sample)"]),
        case(
            "before `at` in the inputs of a flow",
            &["flow h(p: F32", "  at block) -> F32 at sample {", "  p", "}"],
            &["flow h(p: F32 at block) -> F32 at sample {", "  p", "}"],
        ),
    ];
    expect_fmt("break_as_at", &cases);
}

#[test]
fn a_line_break_after_a_keyword_in_an_expression_inside_a_list_is_one_space() {
    let cases = vec![
        body("after `if`", &["  two(if", "    a < b { 1 } else { 2 }, 3)"], &["  two(if a < b { 1 } else { 2 }, 3)"]),
        body(
            "after `match`",
            &["  two(match", "    a { 0 => 1, _ => 2 }, 3)"],
            &["  two(match a { 0 => 1, _ => 2 }, 3)"],
        ),
        body("after `move`", &["  take(move", "    b)"], &["  take(move b)"]),
        body("after `inout`", &["  take(inout", "    b)"], &["  take(inout b)"]),
        body(
            "after `if` in the block form",
            &["  two(", "    if", "      a < b { 1 } else { 2 },", "    3,", "  )"],
            &["  two(", "    if a < b { 1 } else { 2 },", "    3,", "  )"],
        ),
    ];
    expect_fmt("break_after_keyword", &cases);
}

/// S-525: a body of one member is on one line when the writer has its `{` and its `}` on one line; the
/// line breaks of the writer inside an element go (S-497), but a body that fits on one line after that
/// stays over more than one line.
#[test]
fn a_body_that_fits_on_one_line_after_the_line_breaks_inside_an_element_go_stays_over_lines() {
    let cases = vec![
        case(
            "a line break before `as`",
            &["fn h() -> F64 { g(x", "  as F64) }"],
            &["fn h() -> F64 {", "  g(x as F64)", "}"],
        ),
        case(
            "a line break before the closing bracket",
            &["fn h() -> I32 { h(a, b", ") }"],
            &["fn h() -> I32 {", "  h(a, b)", "}"],
        ),
        case("on one line", &["fn h() -> I32 { two(a, b) }"], &["fn h() -> I32 { two(a, b) }"]),
    ];
    expect_fmt("body_one_line_s525", &cases);
}

#[test]
fn a_line_break_at_a_place_of_a_continuation_inside_a_list_stays() {
    // §2.5: the end of a line with a binary operator, a range symbol, `->`, `=` or the `|` of a pattern, and
    // the start of a line with `.`. The line after is one level deeper than the line the element starts on
    // (S-498).
    let cases = vec![
        body("an operator at the end", &["  two(a +", "b, c)"], &["  two(a +", "    b, c)"]),
        body(
            "an operator at the end, in the block form",
            &["  two(", "    a +", "b,", "    c,", "  )"],
            &["  two(", "    a +", "      b,", "    c,", "  )"],
        ),
        body("a dot at the start", &["  g(a", ".abs())"], &["  g(a", "    .abs())"]),
    ];
    expect_fmt("break_continuation", &cases);
}

#[test]
fn a_line_break_after_a_pattern_bar_or_inside_a_second_element_stays_with_its_indentation() {
    // §2.5: the end of a line with a binary operator, a range symbol, `->`, `=` or the `|` of a pattern, and
    // the start of a line with `.`. The line after is one level deeper than the line the element starts on
    // (S-498).
    let cases = vec![
        body(
            "the bar of a pattern at the end",
            &["  match a {", "    0 |", "1 => 1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 |", "      1 => 1,", "    _ => 2,", "  }"],
        ),
        body(
            "an operator at the end of the first of two elements",
            &["  two(a +", "1, b *", "2)"],
            &["  two(a +", "    1, b *", "      2)"],
        ),
    ];
    expect_fmt("break_continuation_w", &cases);
}

#[test]
fn the_closing_bracket_on_its_own_line_after_a_comment_stays() {
    // S-497 (β), S-507: a line break after the comment at the end of a line is not removed, so the
    // closing bracket and what follows it are not moved up before the comment (§3.4).
    let cases = vec![
        body("a call", &["  two(a,b   // c", "  )"], &["  two(a, b // c", "  )"]),
        body(
            "a call in an expression",
            &["  let x = two(a,b // c", "  ) + 1", "  x"],
            &["  let x = two(a, b // c", "  ) + 1", "  x"],
        ),
        body("a call in a call", &["  two(two(a,b // c", "  ), 1)"], &["  two(two(a, b // c", "  ), 1)"]),
        body("an array", &["  g([1,2   // c", "  ])"], &["  g([1, 2 // c", "  ])"]),
        body("a continuation", &["  two(a,   // c", "      b // d", "  )"], &["  two(a, // c", "      b  // d", "  )"]),
    ];
    expect_fmt("closing_after_comment", &cases);
}

#[test]
fn the_comma_goes_before_a_comment_and_the_element_after_it_stays_on_its_line() {
    // S-497: `two(a // c` and `, b)` on the next line: the `,` is moved up to `a`, before the comment, and the
    // element `b` stays on the next line, under `a` (the continuation).
    let cases =
        vec![body("a comma at the start of a line", &["  two(a // c", "    , b)"], &["  two(a, // c", "      b)"])];
    expect_fmt("comma_before_comment", &cases);
}

#[test]
fn a_line_break_after_a_comment_inside_an_element_stays() {
    let cases = vec![
        body(
            "after the arrow of an arm",
            &["  match a {", "    0 =>   // c", "      1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 => // c", "      1,", "    _ => 2,", "  }"],
        ),
        body(
            "after the colon of a field",
            &["  let s = S { f:   // c", "    a, g: 1 }", "  s"],
            &["  let s = S { f: // c", "    a, g: 1 }", "  s"],
        ),
        body(
            "after an operator at the end of a line",
            &["  two(a +   // c", "    b, c)"],
            &["  two(a + // c", "    b, c)"],
        ),
        body("before `as`", &["  g(x   // c", "    as F64)"], &["  g(x // c", "    as F64)"]),
        body("after `move`", &["  take(move   // c", "    b)"], &["  take(move // c", "    b)"]),
    ];
    expect_fmt("break_after_comment", &cases);
}

#[test]
fn the_attribute_of_a_let_stays_on_its_own_line_after_a_comment() {
    // S-497 (β), §3.2: `@mem(bulk)` is moved to the line of the `let` unless there is a comment between.
    let cases = vec![
        flow_body(
            "a comment after the attribute",
            &["  @mem( bulk )   // c", "  let d = delay~(x, 4800)", "  d"],
            &["  @mem(bulk) // c", "  let d = delay~(x, 4800)", "  d"],
        ),
        flow_body(
            "two comments (the comments of consecutive lines are in one column, §3.2)",
            &["  @mem(bulk) // c1", "  let a = delay~(x, 4800) // c2", "  a"],
            &[&format!("{:<26}// c1", "  @mem(bulk)"), &format!("{:<26}// c2", "  let a = delay~(x, 4800)"), "  a"],
        ),
    ];
    expect_fmt("attr_let_comment", &cases);
}

#[test]
fn two_comments_round_a_closing_bracket_are_in_one_column() {
    let cases = vec![body(
        "the comments of consecutive lines",
        &["  two(a,b // c1", "  ) // c2", "  1"],
        &["  two(a, b // c1", &format!("{:<11}// c2", "  )"), "  1"],
    )];
    expect_fmt("two_comments", &cases);
}

// ---- the attribute of an input of a flow (S-501) ----------------------------------------------------

#[test]
fn the_attribute_of_an_input_stays_on_the_line_of_the_input_in_the_one_line_form_and_the_continuation() {
    let cases = vec![
        case(
            "the one-line form",
            &["flow f(@param( default:0.0 )   x: F32 at block, y: F32 at sample) -> F32 at sample {", "  y", "}"],
            &["flow f(@param(default: 0.0) x: F32 at block, y: F32 at sample) -> F32 at sample {", "  y", "}"],
        ),
        case(
            "the one-line form, an attribute after the first input",
            &["flow f(y: F32 at sample, @param(default: 0.0)   x: F32 at block) -> F32 at sample {", "  y", "}"],
            &["flow f(y: F32 at sample, @param(default: 0.0) x: F32 at block) -> F32 at sample {", "  y", "}"],
        ),
        case(
            "the continuation",
            &["flow f(y: F32 at sample,", "@param(default:0.0) x: F32 at block) -> F32 at sample {", "  y", "}"],
            &[
                "flow f(y: F32 at sample,",
                "       @param(default: 0.0) x: F32 at block) -> F32 at sample {",
                "  y",
                "}",
            ],
        ),
    ];
    expect_fmt("attr_input_inline", &cases);
}

#[test]
fn the_attribute_of_an_input_with_a_line_break_after_it_in_the_one_line_form_keeps_the_line_break() {
    let cases = vec![case(
        "the one-line form, a line break after the attribute",
        &["flow f(@param(default: 0.0)", "x: F32 at block, y: F32 at sample) -> F32 at sample {", "  y", "}"],
        &["flow f(@param(default: 0.0)", "  x: F32 at block, y: F32 at sample) -> F32 at sample {", "  y", "}"],
    )];
    expect_fmt("attr_input_inline_w", &cases);
}

#[test]
fn an_attribute_in_the_block_form_goes_to_a_line_of_its_own_also_after_another_element() {
    let cases = vec![case(
        "an attribute on the line of the input before it",
        &[
            "flow g(",
            "  x: F32 at sample, @param(min: 0.0, max: 1.0, default: 0.5) level: F32 at block,",
            ") -> F32 at sample {",
            "  x",
            "}",
        ],
        &[
            "flow g(",
            "  x: F32 at sample,",
            "  @param(min: 0.0, max: 1.0, default: 0.5)",
            "  level: F32 at block,",
            ") -> F32 at sample {",
            "  x",
            "}",
        ],
    )];
    expect_fmt("attr_input_block", &cases);
}

// ---- the blank lines (S-122, S-499, S-502) -------------------------------------------------------------

#[test]
fn two_or_more_blank_lines_are_one_and_none_stays_none() {
    let cases = vec![
        case(
            "between items",
            &["fn a() -> I32 {", "  1", "}", "fn b() -> I32 {", "  2", "}", "", "", "", "fn c() -> I32 {", "  3", "}"],
            &["fn a() -> I32 {", "  1", "}", "fn b() -> I32 {", "  2", "}", "", "fn c() -> I32 {", "  3", "}"],
        ),
        body(
            "between statements",
            &["  let x = a", "  let y = b", "", "", "  let z = x + y", "", "  z"],
            &["  let x = a", "  let y = b", "", "  let z = x + y", "", "  z"],
        ),
        body(
            "in a nested block",
            &["  if a < b {", "    let x = a", "", "", "", "    x", "  } else {", "    b", "  }"],
            &["  if a < b {", "    let x = a", "", "    x", "  } else {", "    b", "  }"],
        ),
        case(
            "between the members of an impl",
            &[
                "impl P {",
                "  fn m(self) -> I32 {",
                "    1",
                "  }",
                "",
                "",
                "  fn n(self) -> I32 {",
                "    2",
                "  }",
                "}",
            ],
            &["impl P {", "  fn m(self) -> I32 {", "    1", "  }", "", "  fn n(self) -> I32 {", "    2", "  }", "}"],
        ),
        body("a blank line of spaces and tabs", &["  let x = a", "   ", "\t", "  x"], &["  let x = a", "", "  x"]),
    ];
    expect_fmt("blank_one", &cases);
}

#[test]
fn the_blank_lines_at_the_start_and_the_end_of_a_block_go() {
    let cases = vec![
        case(
            "a fn",
            &["fn f() -> I32 {", "", "", "  let x = 1", "", "  x", "", "}"],
            &["fn f() -> I32 {", "  let x = 1", "", "  x", "}"],
        ),
        body(
            "a branch",
            &["  if a < b {", "", "    1", "", "  } else {", "", "    2", "  }"],
            &["  if a < b {", "    1", "  } else {", "    2", "  }"],
        ),
        case(
            "an impl",
            &["impl P {", "", "  fn m(self) -> I32 {", "    1", "  }", "", "}"],
            &["impl P {", "  fn m(self) -> I32 {", "    1", "  }", "}"],
        ),
        case("a test", &["test \"t\" {", "", "  assert 1 == 1", "", "}"], &["test \"t\" {", "  assert 1 == 1", "}"]),
    ];
    expect_fmt("blank_block_ends", &cases);
}

#[test]
fn the_blank_lines_at_the_start_and_the_end_of_the_file_go() {
    let cases = vec![
        text("blank lines before the first item", "\n\n\nfn f() -> I32 {\n  1\n}\n", "fn f() -> I32 {\n  1\n}\n"),
        text("blank lines after the last item", "fn f() -> I32 {\n  1\n}\n\n\n\n", "fn f() -> I32 {\n  1\n}\n"),
        text("no line break at the end", "fn f() -> I32 {\n  1\n}", "fn f() -> I32 {\n  1\n}\n"),
        text("blank lines of spaces at the end", "fn f() -> I32 {\n  1\n}\n   \n\t\n", "fn f() -> I32 {\n  1\n}\n"),
        text(
            "blank lines before a comment and after it",
            "\n\n// c\n\n\nfn f() -> I32 {\n  1\n}\n",
            "// c\n\nfn f() -> I32 {\n  1\n}\n",
        ),
        text(
            "blank lines before a doc comment",
            "\n\n/// c\nfn f() -> I32 {\n  1\n}\n",
            "/// c\nfn f() -> I32 {\n  1\n}\n",
        ),
        text(
            "a comment last, blank lines after it",
            "fn f() -> I32 {\n  1\n}\n\n// end\n\n\n",
            "fn f() -> I32 {\n  1\n}\n\n// end\n",
        ),
    ];
    expect_fmt("blank_file_ends", &cases);
}

#[test]
fn the_blank_lines_between_the_lines_of_a_continuation_and_inside_an_element_go() {
    let cases = vec![
        body(
            "after an operator at the end",
            &["  let x = a +", "", "    b", "  x"],
            &["  let x = a +", "    b", "  x"],
        ),
        body(
            "before a dot at the start of a line",
            &["  let x = a", "", "    .abs()", "  x"],
            &["  let x = a", "    .abs()", "  x"],
        ),
        body(
            "inside an element of the block form",
            &["  two(", "    a +", "", "      b,", "    c,", "  )"],
            &["  two(", "    a +", "      b,", "    c,", "  )"],
        ),
    ];
    expect_fmt("blank_continuation", &cases);
}

#[test]
fn the_line_break_after_equals_or_a_comment_stays_when_the_blank_lines_go() {
    let cases = vec![
        body("after `=`", &["  let x =", "", "", "    a", "  x"], &["  let x =", "    a", "  x"]),
        body(
            "inside an element, after a comment",
            &["  match a {", "    0 => // c", "", "      1,", "    _ => 2,", "  }"],
            &["  match a {", "    0 => // c", "      1,", "    _ => 2,", "  }"],
        ),
    ];
    expect_fmt("blank_continuation_w", &cases);
}

/// The block form of a list with blank lines: `blanks[i]` blank lines before the element `i`, and the last
/// one before the closing bracket.
fn block_with_blanks(k: &Kind, blanks: &[usize]) -> String {
    let ind = " ".repeat(k.pre.len() - k.pre.trim_start().len());
    let mut v: Vec<String> = k.head.iter().map(|l| l.to_string()).collect();
    v.push(k.pre.to_string());
    for (i, e) in k.elems.iter().enumerate() {
        v.extend(std::iter::repeat_n(String::new(), blanks[i]));
        v.push(format!("{ind}  {e},"));
    }
    assert!(blanks.len() > k.elems.len(), "{}: one more number of blank lines than elements", k.name);
    v.extend(std::iter::repeat_n(String::new(), blanks[blanks.len() - 1]));
    v.push(format!("{ind}{}{}", k.close, k.post));
    v.extend(k.tail.iter().map(|l| l.to_string()));
    src_s(&v)
}

/// The same for the continuation: `blanks[i]` blank lines before the element `i + 1`.
fn cont_with_blanks(k: &Kind, blanks: &[usize]) -> String {
    let sp = if k.pad { " " } else { "" };
    let col = " ".repeat(k.pre.len() + sp.len());
    let mut v: Vec<String> = k.head.iter().map(|l| l.to_string()).collect();
    let n = k.elems.len();
    for (i, e) in k.elems.iter().enumerate() {
        if i > 0 {
            v.extend(std::iter::repeat_n(String::new(), blanks[i - 1]));
        }
        let mut l = if i == 0 { format!("{}{sp}{e}", k.pre) } else { format!("{col}{e}") };
        l.push_str(if i == n - 1 { "" } else { "," });
        if i == n - 1 {
            l.push_str(&format!("{sp}{}{}", k.close, k.post));
        }
        v.push(l);
    }
    v.extend(k.tail.iter().map(|l| l.to_string()));
    src_s(&v)
}

fn blank_cases(kinds: &[&Kind]) -> Vec<Case> {
    let mut cases = Vec::new();
    for k in kinds {
        cases.push(Case {
            what: format!("{}: the block form", k.name),
            input: block_with_blanks(k, &[2, 3, 1, 2]),
            expected: block_with_blanks(k, &[0, 1, 1, 0]),
        });
        cases.push(Case {
            what: format!("{}: the continuation", k.name),
            input: cont_with_blanks(k, &[3, 1]),
            expected: cont_with_blanks(k, &[1, 1]),
        });
    }
    cases
}

#[test]
fn the_blank_lines_between_the_elements_of_a_list_are_none_or_one_and_those_at_its_ends_go() {
    // S-499: the same rule as for the items and the statements, for every form and every kind of list.
    let kinds = [&K_PARAMS, &K_ARRAY, &K_TUPLE, &K_STRUCT_LIT, &K_FLOW_INPUTS, &K_STRUCT_DECL, &K_ENUM_DECL, &K_MATCH];
    expect_fmt("blank_lists", &blank_cases(&kinds));
}

#[test]
fn the_blank_lines_between_the_elements_of_the_lists_that_were_folded_are_none_or_one() {
    let kinds = [
        &K_ATTR_ARGS,
        &K_VARIANT,
        &K_EFFECT_ROW,
        &K_USE,
        &K_TYPE_ARGS,
        &K_EXPR_TYPE_ARGS,
        &K_TYPE_PARAMS,
        &K_TUPLE_TYPE,
        &K_FN_TYPE,
    ];
    expect_fmt("blank_lists_folded", &blank_cases(&kinds));
}

#[test]
fn the_blank_lines_round_a_comment_between_the_elements_are_none_or_one() {
    let cases = vec![case(
        "the fields of a struct",
        &["struct P {", "  x: F32,", "", "", "  // y", "  y: F32,", "}"],
        &["struct P {", "  x: F32,", "", "  // y", "  y: F32,", "}"],
    )];
    expect_fmt("blank_comment_between", &cases);
}

#[test]
fn the_blank_lines_round_a_comment_in_a_call_are_none_or_one() {
    let cases = vec![
        body(
            "a blank line before and after a comment line",
            &["  g(", "    a,", "", "", "    // c", "", "", "    b,", "  )"],
            &["  g(", "    a,", "", "    // c", "", "    b,", "  )"],
        ),
        body(
            "a comment line right after an element and a blank line after it",
            &["  g(", "    a,", "    // c", "", "", "    b,", "  )"],
            &["  g(", "    a,", "    // c", "", "    b,", "  )"],
        ),
    ];
    expect_fmt("blank_comment_between_w", &cases);
}

#[test]
fn a_comment_counts_as_content_for_the_start_and_the_end() {
    // S-502: the start is before the first content, a line of a comment too; the comment at the end of
    // the line of the opening bracket is not content.
    let cases = vec![
        case(
            "a blank line before a comment at the start of a block goes",
            &["fn f() -> I32 {", "", "  // c", "  let x = 1", "  x", "}"],
            &["fn f() -> I32 {", "  // c", "  let x = 1", "  x", "}"],
        ),
        case(
            "a blank line after a comment at the start of a block stays",
            &["fn f() -> I32 {", "  // c", "", "  let x = 1", "  x", "}"],
            &["fn f() -> I32 {", "  // c", "", "  let x = 1", "  x", "}"],
        ),
        case(
            "a blank line before a comment at the end of a block stays",
            &["fn f() -> I32 {", "  let x = 1", "  x", "", "  // c", "}"],
            &["fn f() -> I32 {", "  let x = 1", "  x", "", "  // c", "}"],
        ),
        case(
            "a blank line after a comment at the end of a block goes",
            &["fn f() -> I32 {", "  let x = 1", "  x", "  // c", "", "}"],
            &["fn f() -> I32 {", "  let x = 1", "  x", "  // c", "}"],
        ),
        case(
            "the fields of a struct: a blank line before a comment at the start goes",
            &["struct P {", "", "  // c", "  x: F32,", "}"],
            &["struct P {", "  // c", "  x: F32,", "}"],
        ),
    ];
    expect_fmt("blank_comment_ends", &cases);
}

#[test]
fn the_blank_lines_round_a_comment_of_the_opening_line_and_in_a_list_follow_the_comment() {
    // S-502: the start is before the first content, a line of a comment too; the comment at the end of
    // the line of the opening bracket is not content.
    let cases = vec![
        case(
            "a blank line after the comment of the line of the opening bracket goes",
            &["fn f() -> I32 { // c", "", "  let x = 1", "  x", "}"],
            &["fn f() -> I32 { // c", "  let x = 1", "  x", "}"],
        ),
        case(
            "the fields of a struct: a blank line after a comment at the start stays",
            &["struct P {", "  // c", "", "  x: F32,", "}"],
            &["struct P {", "  // c", "", "  x: F32,", "}"],
        ),
        case(
            "the fields of a struct: a blank line after the comment of the opening line goes",
            &["struct P { // c", "", "  x: F32,", "}"],
            &["struct P { // c", "  x: F32,", "}"],
        ),
        case(
            "a body with only a comment: a blank line after it goes and the braces stay on two lines",
            &["fn f() { // c", "", "}"],
            &["fn f() { // c", "}"],
        ),
        case(
            "a body with only a comment line and a blank line after it",
            &["fn f() {", "  // c", "", "}"],
            &["fn f() {", "  // c", "}"],
        ),
    ];
    expect_fmt("blank_comment_ends_w", &cases);
}

// ---- the empty braces (S-496, §3.4) --------------------------------------------------------------------

#[test]
fn an_empty_pair_of_braces_is_written_with_nothing_inside() {
    let cases = vec![
        case("a fn, the braces on two lines", &["fn f() {", "}"], &["fn f() {}"]),
        case("a fn, a blank line inside", &["fn f() {", "", "}"], &["fn f() {}"]),
        case("a fn, a space inside", &["fn f() { }"], &["fn f() {}"]),
        case("a fn with a result", &["fn f() -> I32 {", "}"], &["fn f() -> I32 {}"]),
        case("a struct", &["struct S {", "}"], &["struct S {}"]),
        case("a struct, a space inside", &["pub struct S { }"], &["pub struct S {}"]),
        case("an impl", &["impl S {", "}"], &["impl S {}"]),
        case("an enum", &["enum E {", "}"], &["enum E {}"]),
        body("a branch and its else", &["  if a < b {", "  } else {", "  }", "  a"], &["  if a < b {} else {}", "  a"]),
        body("a loop", &["  for x in a {", "  }", "  a"], &["  for x in a {}", "  a"]),
        body("an empty struct literal", &["  let s = S { }", "  s"], &["  let s = S {}", "  s"]),
        body("an empty struct literal on two lines", &["  let s = S {", "  }", "  s"], &["  let s = S {}", "  s"]),
    ];
    expect_fmt("empty_braces", &cases);
}

#[test]
fn an_empty_pair_of_braces_of_a_pattern_is_written_with_nothing_inside() {
    let cases = vec![
        body("an empty struct pattern", &["  let S { } = a", "  a"], &["  let S {} = a", "  a"]),
        body(
            "an empty struct pattern in an arm",
            &["  match a {", "    S { } => 1,", "  }"],
            &["  match a {", "    S {} => 1,", "  }"],
        ),
    ];
    expect_fmt("empty_braces_w", &cases);
}

#[test]
fn an_empty_pair_of_braces_with_a_comment_inside_is_not_put_on_one_line() {
    // §3.4: a pair of braces that holds a comment is not put on one line.
    let cases = vec![
        case("a comment line inside", &["fn f() {", "// c", "}"], &["fn f() {", "  // c", "}"]),
        case("a comment at the end of the line of the brace", &["fn f() { // c", "}"], &["fn f() { // c", "}"]),
    ];
    expect_fmt("empty_braces_comment", &cases);
}

// ---- CR LF (S-201, spec §2.5) ----------------------------------------------------------------------------

fn crlf(lf: &str) -> String {
    lf.replace('\n', "\r\n")
}

#[test]
fn a_cr_lf_is_written_as_an_lf() {
    let doc = "// a file\n\n/// the result\nfn f(a: I32, b: I32) -> I32 {\n  let x = a // one\n\n  x\n}\n";
    let lists = "fn g() -> I32 {\n  let r = h(\n    1,\n    2\n  )\n  let t = [1,\n           2]\n  r\n}\n";
    let canonical_lists = "fn g() -> I32 {\n  let r = h(\n    1,\n    2,\n  )\n  let t = [1,\n           2]\n  r\n}\n";
    let cases = vec![
        text("a file that is canonical but for the line breaks", &crlf(doc), doc),
        text("a block form and a continuation", &crlf(lists), canonical_lists),
        text(
            "blank lines",
            &crlf("fn a() -> I32 {\n  1\n}\n\n\n\nfn b() -> I32 {\n  2\n}\n"),
            "fn a() -> I32 {\n  1\n}\n\nfn b() -> I32 {\n  2\n}\n",
        ),
        text("no line break at the end", "fn f() -> I32 {\r\n  1\r\n}", "fn f() -> I32 {\n  1\n}\n"),
        text(
            "a mix of LF and CR LF",
            "fn f() -> I32 {\r\n  let x = 1\n  x\r\n}\n",
            "fn f() -> I32 {\n  let x = 1\n  x\n}\n",
        ),
        text(
            "a continuation",
            &crlf("fn f(a: I32) -> I32 {\n  let x = a +\n    1\n  x\n}\n"),
            "fn f(a: I32) -> I32 {\n  let x = a +\n    1\n  x\n}\n",
        ),
        text(
            "a line break inside a pair of brackets",
            &crlf("fn f(a: I32) -> I32 {\n  g(a,\n    a)\n}\n"),
            "fn f(a: I32) -> I32 {\n  g(a,\n    a)\n}\n",
        ),
    ];
    expect_fmt("crlf", &cases);
}

#[test]
fn a_cr_lf_after_a_comment_of_the_opening_line_is_written_as_an_lf() {
    let cases = vec![text(
        "a doc comment and a comment at the end of the line",
        &crlf("/// d\nfn f() -> I32 { // c\n  1\n}\n"),
        "/// d\nfn f() -> I32 { // c\n  1\n}\n",
    )];
    expect_fmt("crlf_w", &cases);
}

#[test]
fn a_cr_lf_file_that_is_fmt_checked_is_not_canonical_and_the_output_has_no_cr() {
    let d = Dir::new("crlf_check");
    let p = d.file("a.onsa", "fn f() -> I32 {\r\n  1\r\n}\r\n");
    let out = onsa(&["fmt", "--check", &p]);
    assert_eq!(code(&out), 1, "a file with CR LF is not canonical: {out:?}");
    let out = onsa(&["fmt", &p]);
    assert_eq!(code(&out), 0, "{out:?}");
    let bytes = std::fs::read(&p).unwrap();
    assert!(!bytes.contains(&b'\r'), "the output has a CR: {bytes:?}");
}

#[test]
fn a_single_cr_is_refused() {
    // S-201, spec §2.5: a CR that is not before an LF is E0001, in the code and in a comment; `fmt` does not
    // write the file.
    let inputs: Vec<(&str, String)> = vec![
        ("in the code", "fn f() -> I32 {\r  1\r}\r".to_string()),
        ("in a comment", "fn f() -> I32 {\n  // a\rb\n  1\n}\n".to_string()),
        ("at the end of a line of CR LF lines", "fn f() -> I32 {\r\n  1\r\r\n}\r\n".to_string()),
    ];
    expect_refused("single_cr", "E0001", &inputs);
}

// ---- lists in other places and in each other ---------------------------------------------------------

#[test]
fn lists_inside_lists_get_the_commas_and_the_closing_brackets_of_their_forms() {
    let cases = vec![
        body(
            "a block in a block",
            &["  f(", "    g(", "      1,", "      2", "    ),", "    h(3, 4,)", "  )"],
            &["  f(", "    g(", "      1,", "      2,", "    ),", "    h(3, 4),", "  )"],
        ),
        body(
            "a one-line list inside the elements of a continuation",
            &["  f(g(1, 2,),", "      h(3, 4,),", "      [5, 6,])"],
            &["  f(g(1, 2),", "    h(3, 4),", "    [5, 6])"],
        ),
        body(
            "the closing bracket after the last element of each",
            &["  f(", "    g(", "      1,", "      2),", "    3)"],
            &["  f(", "    g(", "      1,", "      2,", "    ),", "    3,", "  )"],
        ),
        body(
            "a struct literal in the fields of a struct literal",
            &["  let s = S {", "    a: T {", "      x: 1,", "      y: 2", "    },", "    b: 3", "  }", "  s"],
            &["  let s = S {", "    a: T {", "      x: 1,", "      y: 2,", "    },", "    b: 3,", "  }", "  s"],
        ),
        body(
            "a match in an argument",
            &["  f(", "    match a {", "      0 => 1,", "      _ => 2", "    },", "    3", "  )"],
            &["  f(", "    match a {", "      0 => 1,", "      _ => 2,", "    },", "    3,", "  )"],
        ),
    ];
    expect_fmt("lists_in_lists", &cases);
}

#[test]
fn lists_in_a_closure_a_generic_call_a_loop_and_a_par() {
    let cases = vec![
        body(
            "the parameters of a closure",
            &["  let h = fn(", "    x: I32,", "    y: I32", "  ) -> I32 {", "    x", "  }", "  1"],
            &["  let h = fn(", "    x: I32,", "    y: I32,", "  ) -> I32 {", "    x", "  }", "  1"],
        ),
        body(
            "the arguments of a closure called by `.(`",
            &["  let r = h.(a, b,)", "  r"],
            &["  let r = h.(a, b)", "  r"],
        ),
        body("a generic call", &["  let r = g::[I32, F32,](a, b,)", "  r"], &["  let r = g::[I32, F32](a, b)", "  r"]),
        body(
            "a call in the head of a loop",
            &["  for x in f(", "    a,", "    b", "  ) {", "    x", "  }", "  a"],
            &["  for x in f(", "    a,", "    b,", "  ) {", "    x", "  }", "  a"],
        ),
        flow_body(
            "a par with a one-line list and a block",
            &["  par i in 0 ..< 2 {", "    mix(x, i.round_f32(),)", "  }"],
            &["  par i in 0 ..< 2 {", "    mix(x, i.round_f32())", "  }"],
        ),
        flow_body(
            "a branch with a block in each side",
            &[
                "  if~ p > 0.0 {",
                "    mix(",
                "      x,",
                "      p",
                "    )",
                "  } else {",
                "    mix(",
                "      p,",
                "      x",
                "    )",
                "  }",
            ],
            &[
                "  if~ p > 0.0 {",
                "    mix(",
                "      x,",
                "      p,",
                "    )",
                "  } else {",
                "    mix(",
                "      p,",
                "      x,",
                "    )",
                "  }",
            ],
        ),
    ];
    expect_fmt("lists_in_forms", &cases);
}

#[test]
fn the_lists_of_the_items_of_a_module_are_written_in_their_forms() {
    let input = [
        "use std.math.{sin,",
        "         cos,}",
        "",
        "",
        "pub struct P {",
        "x: F32,",
        "      y: F32 }",
        "",
        "enum E {",
        "  A(I32,F32,),",
        "  B(",
        "    I32,",
        "    F32",
        "  )",
        "}",
        "",
        "fn g[T,U,](a: T,b: U) -> T {",
        "  match a {",
        "    0 => 1,",
        "    _ =>",
        "      2",
        "  }",
        "}",
    ];
    let expected = [
        "use std.math.{sin,",
        "              cos}",
        "",
        "pub struct P {",
        "  x: F32,",
        "  y: F32,",
        "}",
        "",
        "enum E {",
        "  A(I32, F32),",
        "  B(",
        "    I32,",
        "    F32,",
        "  ),",
        "}",
        "",
        "fn g[T, U](a: T, b: U) -> T {",
        "  match a {",
        "    0 => 1,",
        "    _ => 2,",
        "  }",
        "}",
    ];
    expect_fmt("module", &[case("a module", &input, &expected)]);
}
