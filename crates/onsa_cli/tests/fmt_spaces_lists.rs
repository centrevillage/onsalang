//! What `onsa fmt` writes for the spaces round the symbols and for the three forms of a list, and where it
//! puts `else`, `with` and an attribute (W3-11/t, unit U2; `docs/onsa-tools.md` §3.2, spec §2.5, §18.2;
//! plan S-07, S-122, R-143).
//!
//! The case files in `tests/spec/fmt/` (`space_*`, `list_*`, `attr_else_with`) pin that the canonical
//! files are a fixed point of `fmt`. These tests pin what `fmt` writes from a file that is not canonical:
//! by the whole text of the output, and that `fmt --check` ends with 0 and another `fmt` changes nothing
//! (§18.2: a canonical file is not changed by another `fmt`).
//!
//! The rules, from `docs/onsa-tools.md` §3.2:
//! - one space on each side of a binary operator, `=`, `->`, `=>`, `as` and `at`;
//! - no space after a prefix symbol, before a postfix one, round the marks of a name, round `::[` or inside
//!   a type argument list of an expression's brackets (a space there is E0020 or E0003, which `fmt` does
//!   not rewrite: exit code 2, the file stays);
//! - one space after `,` and `:`, none before; none inside `( )` and `[ ]`; one inside the braces of a
//!   struct literal and of a pattern, none inside the braces of an effect row and of a `use` list;
//! - a list is in one of three forms, by the writer's line breaks: one line (the last `,` goes), the block
//!   form (a line break after the opening bracket; one element a line, one level deeper; a `,` after every
//!   element; the closing bracket on a line of its own), the continuation (the elements under the first,
//!   no `,` after the last);
//! - `else` and `with` are on the line of the `}` before them; an attribute of an item or of an input of a
//!   flow is on a line of its own; the attribute of a `let` is on the line of the `let`.
//!
//! What is not here, because the plan does not decide it (see the report of W3-11/t U2): the places of the
//! comments, the line breaks inside an element, the levels of the indentation of a continuation inside a
//! continuation, the blank lines inside a list (S-497 to S-499, S-502), the spaces the list of §3.2 does
//! not name (S-496), the `..` of a struct pattern (S-500), an attribute of a flow input in a list of one
//! line (S-501), the form of a list of type arguments over several lines (S-328), and the ranges, the
//! spelling of the numbers and the column of `=` (unit U1).
//!
//! Every test uses only the binary (`onsa fmt`). Expected texts are written from the spec; none is taken
//! from the output of the compiler. The tests that wait for W3-11 are `#[ignore]`d; each ignore names the
//! work that removes it.

use std::path::PathBuf;
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        // The counter makes the directory the test's own even when two tests use the same tag.
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let d = std::env::temp_dir().join(format!("onsa_fmt_u2_{}_{n}_{tag}", std::process::id()));
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

/// `(what, input, expected output)`: the whole text of a file before and after `onsa fmt`.
type Case = (&'static str, String, String);

/// A case from the lines of a file before and after.
fn case(what: &'static str, input: &[&str], expected: &[&str]) -> Case {
    (what, src(input), src(expected))
}

/// Runs `onsa fmt` on every input (one command, so the files are written one after the other), compares
/// the whole text of each output, and checks that the output is a fixed point: `fmt --check` ends with 0
/// and another `fmt` does not change the file.
fn expect_fmt(tag: &str, cases: &[Case]) {
    assert!(!cases.is_empty(), "no case to run");
    let d = Dir::new(tag);
    let paths: Vec<String> =
        cases.iter().enumerate().map(|(i, (_, input, _))| d.file(&format!("c{i}.onsa"), input)).collect();
    let mut args = vec!["fmt"];
    args.extend(paths.iter().map(String::as_str));
    let out = onsa(&args);
    assert_eq!(code(&out), 0, "onsa fmt: {out:?}");
    let mut wrong = Vec::new();
    for ((what, input, expected), path) in cases.iter().zip(&paths) {
        let got = read(path);
        if &got != expected {
            wrong.push(format!("{what}\n--- input\n{input}--- expected\n{expected}--- got\n{got}"));
        }
    }
    assert!(wrong.is_empty(), "{} of {} files are not as expected:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    for ((what, _, expected), path) in cases.iter().zip(&paths) {
        let mut args = vec!["fmt", "--check"];
        args.push(path);
        let out = onsa(&args);
        assert_eq!(code(&out), 0, "{what}: the output is not a fixed point of fmt --check: {out:?}");
        let out = onsa(&["fmt", path]);
        assert_eq!(code(&out), 0, "{what}: {out:?}");
        assert_eq!(&read(path), expected, "{what}: a second fmt changes the output");
    }
}

/// Every input is refused: `onsa fmt` ends with 2, names `diag` in its output (diagnostics go to the
/// standard output, `docs/onsa-tools.md` §3.1) and does not touch the file.
fn expect_refused(tag: &str, diag: &str, inputs: &[(&'static str, String)]) {
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
fn body(what: &'static str, input: &[&str], expected: &[&str]) -> Case {
    let i = in_fn(input);
    let e = in_fn(expected);
    let i: Vec<&str> = i.iter().map(String::as_str).collect();
    let e: Vec<&str> = e.iter().map(String::as_str).collect();
    case(what, &i, &e)
}

/// A case with one expression as the tail of a function: `(input, expected)`.
fn expr(what: &'static str, input: &str, expected: &str) -> Case {
    let i = format!("  {input}");
    let e = format!("  {expected}");
    body(what, &[&i], &[&e])
}

fn exprs(what: &'static str, table: &[(&str, &str)]) -> Vec<Case> {
    table.iter().map(|(i, e)| expr(what, i, e)).collect()
}

// ---- the spaces round the symbols ------------------------------------------------------------------

#[test]
fn a_binary_operator_has_one_space_on_each_side() {
    // One or more for each group of §3.1 (the wrapping and saturating forms included).
    let table = [
        ("a*b", "a * b"),
        ("a/b", "a / b"),
        ("a*%b", "a *% b"),
        ("a*|b", "a *| b"),
        ("a%b", "a % b"),
        ("a+b", "a + b"),
        ("a-b", "a - b"),
        ("a+%b", "a +% b"),
        ("a-%b", "a -% b"),
        ("a+|b", "a +| b"),
        ("a-|b", "a -| b"),
        ("a==b", "a == b"),
        ("a!=b", "a != b"),
        ("a<b", "a < b"),
        ("a<=b", "a <= b"),
        ("a>b", "a > b"),
        ("a>=b", "a >= b"),
        ("a&&b", "a && b"),
        ("a||b", "a || b"),
        ("a&b", "a & b"),
        ("a|b", "a | b"),
        ("a^b", "a ^ b"),
        ("a<<b", "a << b"),
        ("a>>b", "a >> b"),
    ];
    expect_fmt("binary", &exprs("a binary operator written without spaces", &table));
}

#[test]
fn a_binary_operator_written_with_other_spaces_has_one_on_each_side() {
    let table = [
        ("a  *  b", "a * b"),
        ("a\t/\tb", "a / b"),
        ("a   %   b", "a % b"),
        ("a  +  b", "a + b"),
        ("a\t-\tb", "a - b"),
        ("a  +%  b", "a +% b"),
        ("a\t-|\tb", "a -| b"),
        ("a   ==   b", "a == b"),
        ("a\t!=\tb", "a != b"),
        ("a  <=  b", "a <= b"),
        ("a  >  b", "a > b"),
        ("a   &&   b", "a && b"),
        ("a\t||\tb", "a || b"),
        ("a  &  b", "a & b"),
        ("a  ^  b", "a ^ b"),
        ("a  <<  b", "a << b"),
        ("a\t>>\tb", "a >> b"),
    ];
    expect_fmt("binary_loose", &exprs("a binary operator with other spaces", &table));
}

#[test]
fn a_chain_of_operators_has_a_space_round_each() {
    let table = [
        ("a+b-1+2", "a + b - 1 + 2"),
        ("a*b/2*3", "a * b / 2 * 3"),
        ("a+b*b-a/b", "a + b * b - a / b"),
        ("a<=b&&b<a", "a <= b && b < a"),
        ("a&&b&&a", "a && b && a"),
        ("(a&b)|(a^b)", "(a & b) | (a ^ b)"),
        ("a<<1<<2", "a << 1 << 2"),
        ("(a&&b)||a", "(a && b) || a"),
        ("(a+1)%b", "(a + 1) % b"),
        ("a+%b-%1*%2", "a +% b -% 1 *% 2"),
        ("a+|b-|1*|2", "a +| b -| 1 *| 2"),
        ("a*(b+1)", "a * (b + 1)"),
        ("f(a+1)*g(b-1)", "f(a + 1) * g(b - 1)"),
        ("-a*b", "-a * b"),
        ("!a&&!b", "!a && !b"),
        ("-a+-b", "-a + -b"),
        ("a*-b", "a * -b"),
        ("a-(-b)", "a - (-b)"),
    ];
    expect_fmt("chain", &exprs("a chain of operators", &table));
}

#[test]
fn the_equals_has_one_space_on_each_side() {
    // `let`, `var`, an assignment, `const`, `type`. Each statement is alone in its function or separated by
    // a blank line, so that the column of `=` (unit U1) does not move them.
    let cases = vec![
        body("let", &["  let x=1", "  x"], &["  let x = 1", "  x"]),
        body("let, more spaces", &["  let x  =  1", "  x"], &["  let x = 1", "  x"]),
        body("let, a tab", &["  let x\t=\t1", "  x"], &["  let x = 1", "  x"]),
        body("let with a type", &["  let x:I32=1", "  x"], &["  let x: I32 = 1", "  x"]),
        body("var", &["  var x=1", "  x"], &["  var x = 1", "  x"]),
        body("var with a type", &["  var x :I32  =1", "  x"], &["  var x: I32 = 1", "  x"]),
        body("an assignment", &["  var x = 1", "", "  x=x+1", "  x"], &["  var x = 1", "", "  x = x + 1", "  x"]),
        body(
            "an assignment, more spaces",
            &["  var x = 1", "", "  x  =  2", "  x"],
            &["  var x = 1", "", "  x = 2", "  x"],
        ),
        body(
            "an assignment to a field",
            &["  var p = P { x: 1 }", "", "  p.x=2", "  1"],
            &["  var p = P { x: 1 }", "", "  p.x = 2", "  1"],
        ),
        body(
            "an assignment to an element",
            &["  var v = [1, 2]", "", "  v[0]=a", "  1"],
            &["  var v = [1, 2]", "", "  v[0] = a", "  1"],
        ),
        case("const", &["const N:U32=4"], &["const N: U32 = 4"]),
        case("const, more spaces", &["const N  :  U32  =  4"], &["const N: U32 = 4"]),
        case("type", &["type Sample=F32"], &["type Sample = F32"]),
        case("type, more spaces", &["type Sample\t=\tF32"], &["type Sample = F32"]),
        case("pub const", &["pub const N:U32=4"], &["pub const N: U32 = 4"]),
        body("a tuple pattern", &["  let (x,y)=(a,b)", "  x"], &["  let (x, y) = (a, b)", "  x"]),
        body("a struct pattern", &["  let P {x:x,y:y}=p", "  x"], &["  let P { x: x, y: y } = p", "  x"]),
    ];
    expect_fmt("equals", &cases);
}

#[test]
fn the_arrows_have_one_space_on_each_side() {
    let cases = vec![
        case("a fn head", &["fn f(a: I32)->I32 {", "  a", "}"], &["fn f(a: I32) -> I32 {", "  a", "}"]),
        case(
            "a fn head, more spaces",
            &["fn f(a: I32)  ->  I32 {", "  a", "}"],
            &["fn f(a: I32) -> I32 {", "  a", "}"],
        ),
        case("a fn head, a tab", &["fn f(a: I32)\t->\tI32 {", "  a", "}"], &["fn f(a: I32) -> I32 {", "  a", "}"]),
        case(
            "a function type in a parameter",
            &["fn f(g: fn(I32)->I32) -> I32 {", "  1", "}"],
            &["fn f(g: fn(I32) -> I32) -> I32 {", "  1", "}"],
        ),
        case(
            "a function type, more spaces",
            &["fn f(g: fn(I32)   ->   I32) -> I32 {", "  1", "}"],
            &["fn f(g: fn(I32) -> I32) -> I32 {", "  1", "}"],
        ),
        case(
            "a function type that returns a function type",
            &["type T=fn(I32)->fn(I32)->I32"],
            &["type T = fn(I32) -> fn(I32) -> I32"],
        ),
        case(
            "a function type in a field",
            &["struct S {", "  g: fn(F32)->F32,", "}"],
            &["struct S {", "  g: fn(F32) -> F32,", "}"],
        ),
        body(
            "a closure",
            &["  let h = fn(x: I32)->I32 {", "    x", "  }", "  1"],
            &["  let h = fn(x: I32) -> I32 {", "    x", "  }", "  1"],
        ),
        case(
            "a flow head",
            &["flow f(x: F32 at sample)->F32 at sample {", "  x", "}"],
            &["flow f(x: F32 at sample) -> F32 at sample {", "  x", "}"],
        ),
        case(
            "a method head",
            &["impl P {", "  fn m(self)->I32 {", "    1", "  }", "}"],
            &["impl P {", "  fn m(self) -> I32 {", "    1", "  }", "}"],
        ),
        body(
            "an arm",
            &["  match a {", "    0=>1,", "    _=>2,", "  }"],
            &["  match a {", "    0 => 1,", "    _ => 2,", "  }"],
        ),
        body(
            "an arm, more spaces",
            &["  match a {", "    0   =>   1,", "    _\t=>\t2,", "  }"],
            &["  match a {", "    0 => 1,", "    _ => 2,", "  }"],
        ),
        body(
            "an arm with a pattern of a variant and a guard",
            &["  match o {", "    Some(v) if v>0=>v,", "    _=>0,", "  }"],
            &["  match o {", "    Some(v) if v > 0 => v,", "    _ => 0,", "  }"],
        ),
    ];
    expect_fmt("arrows", &cases);
}

#[test]
fn as_and_at_have_one_space_on_each_side() {
    let cases = vec![
        expr("as", "a  as  F64", "a as F64"),
        expr("as, a tab", "a\tas\tF64", "a as F64"),
        expr("as of a prefix", "-a   as   F64", "-a as F64"),
        expr("as in parentheses", "(a   as   F64)  *  2.0", "(a as F64) * 2.0"),
        expr("as of a call", "f(a)  as  F64", "f(a) as F64"),
        case(
            "at in the head of a flow",
            &["flow f(x: F32   at   sample, p: F32\tat\tblock) -> F32   at   sample {", "  x", "}"],
            &["flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {", "  x", "}"],
        ),
        case(
            "at in an expression",
            &["flow f(p: F32 at block) -> F32 at sample {", "  p  at  sample", "}"],
            &["flow f(p: F32 at block) -> F32 at sample {", "  p at sample", "}"],
        ),
        case(
            "at and as together",
            &["flow f(p: I32 at block) -> F32 at sample {", "  (p   as   F32)   at   sample", "}"],
            &["flow f(p: I32 at block) -> F32 at sample {", "  (p as F32) at sample", "}"],
        ),
        case(
            "at of a let",
            &["flow f(p: F32 at block) -> F32 at sample {", "  let a = design(p)   at   block", "  a at sample", "}"],
            &["flow f(p: F32 at block) -> F32 at sample {", "  let a = design(p) at block", "  a at sample", "}"],
        ),
    ];
    expect_fmt("as_at", &cases);
}

#[test]
fn a_prefix_symbol_a_mark_and_a_postfix_symbol_get_no_space() {
    // These are the only spellings the language reads (§2.5), so `fmt` leaves each as it is, also when the
    // rest of the line is loose.
    let table = [
        ("-a", "-a"),
        ("!a", "!a"),
        ("-a[0]", "-a[0]"),
        ("!f(a)", "!f(a)"),
        ("-a as F64", "-a as F64"),
        ("-(a+b)", "-(a + b)"),
        ("f(a)", "f(a)"),
        ("g.(a)", "g.(a)"),
        ("p.x.(a)", "p.x.(a)"),
        ("ops[0].(a)", "ops[0].(a)"),
        ("pick(true).(5)", "pick(true).(5)"),
        ("xs[a]", "xs[a]"),
        ("xs[a][b]", "xs[a][b]"),
        ("xs[xs[a]]", "xs[xs[a]]"),
        ("p.x", "p.x"),
        ("t.0", "t.0"),
        ("t.0.1", "t.0.1"),
        ("p.m(a).n(b)", "p.m(a).n(b)"),
        ("a?", "a?"),
        ("f(a)?", "f(a)?"),
        ("a.b(c)[d].e?", "a.b(c)[d].e?"),
        ("saw~(a)", "saw~(a)"),
        ("lp~(a,b)", "lp~(a, b)"),
        ("prev~(^y)", "prev~(^y)"),
        ("prev~(-^y)", "prev~(-^y)"),
        ("prev~(^y.l)", "prev~(^y.l)"),
        ("buf.push!(a)", "buf.push!(a)"),
        ("buf.push_with::[F32,U8]!(a,1)", "buf.push_with::[F32, U8]!(a, 1)"),
        ("parse::[U32](a)", "parse::[U32](a)"),
        ("conv.parse::[I32](a)", "conv.parse::[I32](a)"),
        ("Buf::[F32].zeroed(4)", "Buf::[F32].zeroed(4)"),
        ("Rg::[F32,4].CAP", "Rg::[F32, 4].CAP"),
        ("Pr::[U8] {a: 250}", "Pr::[U8] { a: 250 }"),
        ("v.m::[I32](a)", "v.m::[I32](a)"),
        ("None::[I32]", "None::[I32]"),
        ("id::[Option[Option[U8]]](None)", "id::[Option[Option[U8]]](None)"),
        ("id::[fn(I32)->I32](inc)", "id::[fn(I32) -> I32](inc)"),
        ("pair::[U8,F32](1,2.0)", "pair::[U8, F32](1, 2.0)"),
    ];
    expect_fmt("no_space", &exprs("a form without a space", &table));
}

#[test]
fn the_type_argument_list_of_an_expression_has_no_space_round_its_brackets_and_inside_them() {
    let table = [
        ("id::[ U8 ]( a )", "id::[U8](a)"),
        ("pair::[ U8 , F32 ]( 1 , 2.0 )", "pair::[U8, F32](1, 2.0)"),
        ("pair::[U8,F32]( 1 )", "pair::[U8, F32](1)"),
        ("Rg::[ F32 , 4 ].CAP", "Rg::[F32, 4].CAP"),
        ("id::[ Option[ U8 ] ](None)", "id::[Option[U8]](None)"),
        ("id::[ fn( I32 )  ->  I32 ](inc)", "id::[fn(I32) -> I32](inc)"),
        ("v.m::[ I32 ](a)", "v.m::[I32](a)"),
        ("buf.push::[ F32 ]!(a)", "buf.push::[F32]!(a)"),
    ];
    expect_fmt("type_args", &exprs("a type argument list with other spaces", &table));
}

#[test]
fn an_expected_type_and_a_type_argument_are_not_written_as_each_other() {
    // §4.5: `let y: U8 = id(250)` and `let y = id::[U8](250)` are two ways to give the type; `fmt` writes
    // neither as the other, whatever the spaces were.
    let cases = vec![
        body("an expected type", &["  let y: U8 = id(250)", "  y"], &["  let y: U8 = id(250)", "  y"]),
        body("an expected type, loose", &["  let y :U8=id( 250 )", "  y"], &["  let y: U8 = id(250)", "  y"]),
        body("a type argument", &["  let y = id::[U8](250)", "  y"], &["  let y = id::[U8](250)", "  y"]),
        body("a type argument, loose", &["  let y=id::[ U8 ]( 250 )", "  y"], &["  let y = id::[U8](250)", "  y"]),
        body("both", &["  let y: U8 = id::[U8](250)", "  y"], &["  let y: U8 = id::[U8](250)", "  y"]),
        body("both, loose", &["  let y:U8=id::[ U8 ](250)", "  y"], &["  let y: U8 = id::[U8](250)", "  y"]),
        body(
            "a parse with the type in the annotation",
            &["  let n: I32 = parse( \"3\" )", "  n"],
            &["  let n: I32 = parse(\"3\")", "  n"],
        ),
        body(
            "a parse with the type argument",
            &["  let n = parse::[I32]( \"3\" )", "  n"],
            &["  let n = parse::[I32](\"3\")", "  n"],
        ),
    ];
    expect_fmt("annotation_or_argument", &cases);
}

#[test]
fn a_comma_and_a_colon_get_one_space_after_and_none_before() {
    let cases = vec![
        body("arguments", &["  f(a,b)"], &["  f(a, b)"]),
        body("arguments, a space before", &["  f(a ,b , a)"], &["  f(a, b, a)"]),
        body("arguments, more spaces after", &["  f(a,   b,\ta)"], &["  f(a, b, a)"]),
        body("an array", &["  [1,2,3]"], &["  [1, 2, 3]"]),
        body("an array, a space before", &["  [1 ,2 , 3]"], &["  [1, 2, 3]"]),
        body("a tuple", &["  (a,b)"], &["  (a, b)"]),
        body("a tuple, a space before", &["  (a ,   b)"], &["  (a, b)"]),
        case("parameters", &["fn g(a:I32,b:I32) -> I32 {", "  a", "}"], &["fn g(a: I32, b: I32) -> I32 {", "  a", "}"]),
        case(
            "parameters, spaces before",
            &["fn g(a :I32 ,b : I32) -> I32 {", "  a", "}"],
            &["fn g(a: I32, b: I32) -> I32 {", "  a", "}"],
        ),
        case("fields", &["struct P {", "  x:F32,", "  y :F32,", "}"], &["struct P {", "  x: F32,", "  y: F32,", "}"]),
        case("a tuple type", &["type T=(I32,F32)"], &["type T = (I32, F32)"]),
        case("a type with arguments", &["type T=Result[Str,IoError]"], &["type T = Result[Str, IoError]"]),
        case(
            "a type with arguments, spaces before",
            &["type T=Result[Str ,  IoError]"],
            &["type T = Result[Str, IoError]"],
        ),
        case("type parameters", &["fn g[T,U](x:T) -> U {", "  x", "}"], &["fn g[T, U](x: T) -> U {", "  x", "}"]),
        case(
            "a bound and a const parameter",
            &["fn g[T:PartialOrd,const N:U32](x:T) -> T {", "  x", "}"],
            &["fn g[T: PartialOrd, const N: U32](x: T) -> T {", "  x", "}"],
        ),
        body("a struct literal", &["  P {x:1,y:2}"], &["  P { x: 1, y: 2 }"]),
        body("a struct literal, spaces before", &["  P { x :1 ,y : 2 }"], &["  P { x: 1, y: 2 }"]),
        body("a call of a variant", &["  Some(a,b)"], &["  Some(a, b)"]),
        case("a variant of an enum", &["enum E {", "  A(I32,F32),", "}"], &["enum E {", "  A(I32, F32),", "}"]),
        body(
            "a closure",
            &["  let h = fn(x:I32,y:I32) -> I32 {", "    x", "  }", "  1"],
            &["  let h = fn(x: I32, y: I32) -> I32 {", "    x", "  }", "  1"],
        ),
        body("a method call", &["  p.m(a,b).n(b ,a)"], &["  p.m(a, b).n(b, a)"]),
        case(
            "a flow head",
            &["flow f(x:F32 at sample,p:F32 at block) -> F32 at sample {", "  x", "}"],
            &["flow f(x: F32 at sample, p: F32 at block) -> F32 at sample {", "  x", "}"],
        ),
    ];
    expect_fmt("comma_colon", &cases);
}

#[test]
fn a_round_or_square_bracket_has_no_space_inside() {
    let table = [
        ("f( a )", "f(a)"),
        ("f(  a ,  b  )", "f(a, b)"),
        ("f(\ta\t)", "f(a)"),
        ("f( )", "f()"),
        ("f(g( a ))", "f(g(a))"),
        ("[ 1, 2 ]", "[1, 2]"),
        ("[  ]", "[]"),
        ("( a, b )", "(a, b)"),
        ("a[ 0 ]", "a[0]"),
        ("a[ a[ 0 ] ]", "a[a[0]]"),
        ("( a + b ) * a", "(a + b) * a"),
        ("Some( a )", "Some(a)"),
        ("p.m( a ).n( b )", "p.m(a).n(b)"),
        ("g.( a )", "g.(a)"),
    ];
    let mut cases = exprs("a bracket with spaces inside", &table);
    cases.push(case(
        "parameters",
        &["fn g( a: I32, b: Span[ I32 ] ) -> I32 {", "  a", "}"],
        &["fn g(a: I32, b: Span[I32]) -> I32 {", "  a", "}"],
    ));
    cases.push(case(
        "types",
        &["type T = Result[ Str, IoError ]", "type U = ( I32, F32 )", "type V = fn( I32 ) -> I32"],
        &["type T = Result[Str, IoError]", "type U = (I32, F32)", "type V = fn(I32) -> I32"],
    ));
    cases.push(case(
        "type parameters",
        &["fn g[ T, U ](x: T) -> U {", "  x", "}"],
        &["fn g[T, U](x: T) -> U {", "  x", "}"],
    ));
    cases.push(body("a pattern", &["  let ( x, y ) = ( a, b )", "  x"], &["  let (x, y) = (a, b)", "  x"]));
    expect_fmt("inside_brackets", &cases);
}

#[test]
fn a_struct_literal_and_a_pattern_get_one_space_inside_the_braces() {
    let cases = vec![
        body("a literal without spaces", &["  P {x: 1.0, y: 2.0}"], &["  P { x: 1.0, y: 2.0 }"]),
        body("a literal with more", &["  P {   x: 1.0, y: 2.0   }"], &["  P { x: 1.0, y: 2.0 }"]),
        body("a literal with tabs", &["  P {\tx: 1.0, y: 2.0\t}"], &["  P { x: 1.0, y: 2.0 }"]),
        body("a literal of a field", &["  P {x: 1.0}"], &["  P { x: 1.0 }"]),
        body("a literal in a literal", &["  P {a: Q {x: 1.0}, b: 2.0}"], &["  P { a: Q { x: 1.0 }, b: 2.0 }"]),
        body("a literal in an argument", &["  f(P {x: 1.0}, 2)"], &["  f(P { x: 1.0 }, 2)"]),
        body("a literal in an array", &["  [P {x: 1.0}, P {x: 2.0}]"], &["  [P { x: 1.0 }, P { x: 2.0 }]"]),
        body("a literal with type arguments", &["  Pr::[U8] {a: 250}"], &["  Pr::[U8] { a: 250 }"]),
        body("a struct pattern", &["  let P {x: px, y: py} = a", "  px"], &["  let P { x: px, y: py } = a", "  px"]),
        body(
            "a struct pattern, more",
            &["  let P {  x: px, y: py  } = a", "  px"],
            &["  let P { x: px, y: py } = a", "  px"],
        ),
        body(
            "a struct pattern in an arm",
            &["  match o {", "    Some(P {x: qx, y: _}) => qx,", "    None => 0,", "  }"],
            &["  match o {", "    Some(P { x: qx, y: _ }) => qx,", "    None => 0,", "  }"],
        ),
    ];
    expect_fmt("struct_braces", &cases);
}

#[test]
fn an_effect_row_and_a_use_list_get_no_space_inside_the_braces() {
    let cases = vec![
        case(
            "an effect row",
            &["fn g() -> I32 uses { Alloc } {", "  1", "}"],
            &["fn g() -> I32 uses {Alloc} {", "  1", "}"],
        ),
        case(
            "an effect row with two",
            &["fn g() -> I32 uses {  Alloc ,Fs  } {", "  1", "}"],
            &["fn g() -> I32 uses {Alloc, Fs} {", "  1", "}"],
        ),
        case(
            "an effect row without spaces",
            &["fn g() -> I32 uses {Alloc,Fs} {", "  1", "}"],
            &["fn g() -> I32 uses {Alloc, Fs} {", "  1", "}"],
        ),
        case(
            "an effect row of a function type",
            &["fn g(h: fn(I32) -> I32 uses { Alloc }) -> I32 uses {Alloc} {", "  1", "}"],
            &["fn g(h: fn(I32) -> I32 uses {Alloc}) -> I32 uses {Alloc} {", "  1", "}"],
        ),
        case("a use list", &["use a.{ x, y }"], &["use a.{x, y}"]),
        case("a use list, without spaces", &["use a.{x,y}"], &["use a.{x, y}"]),
        case("a use list, more spaces", &["use a.b.{   x ,   y   }"], &["use a.b.{x, y}"]),
        case("a use list of one name", &["use std.math.{ sqrt }"], &["use std.math.{sqrt}"]),
        case("a use list with a tab", &["use a.{\tx,\ty\t}"], &["use a.{x, y}"]),
    ];
    expect_fmt("effect_use_braces", &cases);
}

#[test]
fn a_form_with_a_space_in_a_place_that_has_none_is_refused() {
    // §2.5: a space after a prefix symbol, before a postfix one, between a name and its mark, round `.`
    // and round `::[` is E0020. The file is not rewritten (§18.2): exit code 2, the text stays.
    let prefix: Vec<(&'static str, String)> = [
        ("a space after a prefix minus", "- a"),
        ("a space after a prefix not", "! a"),
        ("a space after a caret", "^ y"),
        ("a tab after a prefix minus", "-\ta"),
    ]
    .iter()
    .map(|(w, e)| (*w, in_fn(&[&format!("  {e}")]).join("\n") + "\n"))
    .collect();
    expect_refused("refused_prefix", "E0020", &prefix);
    let postfix: Vec<(&'static str, String)> = [
        ("a space before the parenthesis of a call", "f (a)"),
        ("a space before a bracket of an index", "xs [0]"),
        ("a space before the question mark", "a ?"),
        ("a space before the dot of a member", "a .b"),
        ("a space after the dot of a member", "a. b"),
        ("a space round the dot of a member", "a . b"),
        ("a space before the parenthesis of a value call", "g. (a)"),
        ("a space before the mark of a flow call", "saw ~(a)"),
        ("a space after the mark of a flow call", "saw~ (a)"),
        ("a space round the mark of a flow call", "saw ~ (a)"),
        ("a space after the bang of a call", "v.push! (a)"),
    ]
    .iter()
    .map(|(w, e)| (*w, in_fn(&[&format!("  {e}")]).join("\n") + "\n"))
    .collect();
    expect_refused("refused_postfix", "E0020", &postfix);
    let args: Vec<(&'static str, String)> = [
        ("a space before ::[", "id ::[U8](a)"),
        ("a space between :: and [", "id:: [U8](a)"),
        ("a space round ::", "id :: [U8](a)"),
        ("a space between ] and the parenthesis", "id::[U8] (a)"),
        ("a space before ::[ of a method", "v.m ::[I32](a)"),
        ("a space before ::[ of a struct literal", "Pr ::[U8] { a: 250 }"),
    ]
    .iter()
    .map(|(w, e)| (*w, in_fn(&[&format!("  {e}")]).join("\n") + "\n"))
    .collect();
    expect_refused("refused_type_args", "E0020", &args);
}

#[test]
fn the_symbols_work_together_and_a_second_fmt_changes_nothing() {
    let cases = vec![case(
        "a file of every kind",
        &[
            "const N:U32=4",
            "type Sample=F32",
            "pub struct P {",
            "  x:F32,",
            "  y:F32,",
            "}",
            "",
            "fn g(a:I32,b:Span[I32],h:fn(I32)->I32)->Option[I32] {",
            "  let p=P {x:1.0,y:2.0}",
            "",
            "  let P {x:px,y:_}=p",
            "",
            "  var c=a*2+b[ 0 ]",
            "",
            "  c=c-1",
            "  match Some(c) {",
            "    Some(v) if v>0=>Some(v+1),",
            "    _=>None,",
            "  }",
            "}",
        ],
        &[
            "const N: U32 = 4",
            "type Sample = F32",
            "pub struct P {",
            "  x: F32,",
            "  y: F32,",
            "}",
            "",
            "fn g(a: I32, b: Span[I32], h: fn(I32) -> I32) -> Option[I32] {",
            "  let p = P { x: 1.0, y: 2.0 }",
            "",
            "  let P { x: px, y: _ } = p",
            "",
            "  var c = a * 2 + b[0]",
            "",
            "  c = c - 1",
            "  match Some(c) {",
            "    Some(v) if v > 0 => Some(v + 1),",
            "    _ => None,",
            "  }",
            "}",
        ],
    )];
    expect_fmt("together", &cases);
}

// ---- the three forms of a list ---------------------------------------------------------------------

/// The same list in the three forms of one kind: `(kind, one line, block form, continuation)`, as the lines
/// of a whole file for each. The block form and the continuation are the output; the inputs are listed
/// in the tests below.
struct Kind {
    name: &'static str,
    one: Vec<&'static str>,
    block: Vec<&'static str>,
    cont: Vec<&'static str>,
}

/// Every kind of list that is written at the first level of a function body or at the top of a file.
fn kinds() -> Vec<Kind> {
    vec![
        Kind {
            name: "the arguments of a call",
            one: vec!["fn g() -> I32 {", "  let r = f(a, b, c)", "  r", "}"],
            block: vec!["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c,", "  )", "  r", "}"],
            cont: vec!["fn g() -> I32 {", "  let r = f(a,", "            b,", "            c)", "  r", "}"],
        },
        Kind {
            name: "the parameters of a declaration",
            one: vec!["fn g(a: I32, b: I32, c: I32) -> I32 {", "  a", "}"],
            block: vec!["fn g(", "  a: I32,", "  b: I32,", "  c: I32,", ") -> I32 {", "  a", "}"],
            cont: vec!["fn g(a: I32,", "     b: I32,", "     c: I32) -> I32 {", "  a", "}"],
        },
        Kind {
            name: "the elements of an array",
            one: vec!["fn g() -> I32 {", "  let xs = [1, 2, 3]", "  xs[0]", "}"],
            block: vec!["fn g() -> I32 {", "  let xs = [", "    1,", "    2,", "    3,", "  ]", "  xs[0]", "}"],
            cont: vec!["fn g() -> I32 {", "  let xs = [1,", "            2,", "            3]", "  xs[0]", "}"],
        },
        Kind {
            name: "the elements of a tuple",
            one: vec!["fn g() -> I32 {", "  let t = (1, 2.0, a)", "  1", "}"],
            block: vec!["fn g() -> I32 {", "  let t = (", "    1,", "    2.0,", "    a,", "  )", "  1", "}"],
            cont: vec!["fn g() -> I32 {", "  let t = (1,", "           2.0,", "           a)", "  1", "}"],
        },
        Kind {
            name: "the fields of a struct literal",
            one: vec!["fn g() -> P {", "  let p = P { x: 1.0, y: 2.0, z: 3.0 }", "  p", "}"],
            block: vec![
                "fn g() -> P {",
                "  let p = P {",
                "    x: 1.0,",
                "    y: 2.0,",
                "    z: 3.0,",
                "  }",
                "  p",
                "}",
            ],
            cont: vec![
                "fn g() -> P {",
                "  let p = P { x: 1.0,",
                "              y: 2.0,",
                "              z: 3.0 }",
                "  p",
                "}",
            ],
        },
        Kind {
            name: "the inputs of a flow",
            one: vec!["flow g(x: F32 at sample, p: F32 at block, q: F32 at init) -> F32 at sample {", "  x", "}"],
            block: vec![
                "flow g(",
                "  x: F32 at sample,",
                "  p: F32 at block,",
                "  q: F32 at init,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            cont: vec![
                "flow g(x: F32 at sample,",
                "       p: F32 at block,",
                "       q: F32 at init) -> F32 at sample {",
                "  x",
                "}",
            ],
        },
    ]
}

#[test]
fn a_one_line_list_stays_on_one_line_and_loses_its_last_comma() {
    let cases = vec![
        case(
            "the arguments of a call",
            &["fn g() -> I32 {", "  let r = f(a, b, c,)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(a, b, c)", "  r", "}"],
        ),
        case(
            "the arguments of a call, a space before the bracket",
            &["fn g() -> I32 {", "  let r = f(a, b, c, )", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(a, b, c)", "  r", "}"],
        ),
        case(
            "the parameters of a declaration",
            &["fn g(a: I32, b: I32, c: I32,) -> I32 {", "  a", "}"],
            &["fn g(a: I32, b: I32, c: I32) -> I32 {", "  a", "}"],
        ),
        case(
            "the elements of an array",
            &["fn g() -> I32 {", "  let xs = [1, 2, 3,]", "  xs[0]", "}"],
            &["fn g() -> I32 {", "  let xs = [1, 2, 3]", "  xs[0]", "}"],
        ),
        case(
            "the elements of a tuple",
            &["fn g() -> I32 {", "  let t = (1, 2.0, a,)", "  1", "}"],
            &["fn g() -> I32 {", "  let t = (1, 2.0, a)", "  1", "}"],
        ),
        case(
            "the fields of a struct literal",
            &["fn g() -> P {", "  let p = P { x: 1.0, y: 2.0, z: 3.0, }", "  p", "}"],
            &["fn g() -> P {", "  let p = P { x: 1.0, y: 2.0, z: 3.0 }", "  p", "}"],
        ),
        case(
            "the fields of a struct literal, no space before the brace",
            &["fn g() -> P {", "  let p = P { x: 1.0, y: 2.0,}", "  p", "}"],
            &["fn g() -> P {", "  let p = P { x: 1.0, y: 2.0 }", "  p", "}"],
        ),
        case(
            "the inputs of a flow",
            &["flow g(x: F32 at sample, p: F32 at block,) -> F32 at sample {", "  x", "}"],
            &["flow g(x: F32 at sample, p: F32 at block) -> F32 at sample {", "  x", "}"],
        ),
        case("a use list", &["use a.{x, y,}"], &["use a.{x, y}"]),
        case(
            "a tuple pattern",
            &["fn g(t: (I32, I32)) -> I32 {", "  let (a, b,) = t", "  a", "}"],
            &["fn g(t: (I32, I32)) -> I32 {", "  let (a, b) = t", "  a", "}"],
        ),
        case(
            "a struct pattern",
            &["fn g(p: P) -> I32 {", "  let P { x: a, y: b, } = p", "  a", "}"],
            &["fn g(p: P) -> I32 {", "  let P { x: a, y: b } = p", "  a", "}"],
        ),
        case(
            "the payload of a variant pattern",
            &["fn g(s: S) -> I32 {", "  match s {", "    S.R(w, z,) => w,", "    _ => 0,", "  }", "}"],
            &["fn g(s: S) -> I32 {", "  match s {", "    S.R(w, z) => w,", "    _ => 0,", "  }", "}"],
        ),
        case(
            "the payload of a variant declaration",
            &["enum E {", "  A(I32, F32,),", "}"],
            &["enum E {", "  A(I32, F32),", "}"],
        ),
        case(
            "a method call",
            &["fn g() -> I32 {", "  p.m(a, b,).n(b, a,)", "}"],
            &["fn g() -> I32 {", "  p.m(a, b).n(b, a)", "}"],
        ),
        case("a list of one element", &["fn g() -> I32 {", "  f(a,)", "}"], &["fn g() -> I32 {", "  f(a)", "}"]),
    ];
    expect_fmt("one_line_trailing_comma", &cases);
}

#[test]
fn the_canonical_form_of_each_kind_of_list_stays() {
    // The three forms of every kind, written canonical, are a fixed point (the case files
    // `tests/spec/fmt/list_forms*.onsa` pin the same; this runs them through the binary too).
    let mut cases = Vec::new();
    for k in kinds() {
        cases.push((k.name, src(&k.one), src(&k.one)));
        cases.push((k.name, src(&k.block), src(&k.block)));
        cases.push((k.name, src(&k.cont), src(&k.cont)));
    }
    expect_fmt("canonical_forms", &cases);
}

#[test]
fn the_last_element_of_a_block_gets_a_comma_and_the_closing_bracket_a_line_of_its_own() {
    let cases = vec![
        case(
            "the arguments of a call",
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c", "  )", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c,", "  )", "  r", "}"],
        ),
        case(
            "the arguments of a call, the bracket after the last element",
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c,", "  )", "  r", "}"],
        ),
        case(
            "the arguments of a call, the comma and the bracket after the last element",
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c,)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "    c,", "  )", "  r", "}"],
        ),
        case(
            "the parameters of a declaration",
            &["fn g(", "  a: I32,", "  b: I32", ") -> I32 {", "  a", "}"],
            &["fn g(", "  a: I32,", "  b: I32,", ") -> I32 {", "  a", "}"],
        ),
        case(
            "the parameters of a declaration, the bracket after the last one",
            &["fn g(", "  a: I32,", "  b: I32) -> I32 {", "  a", "}"],
            &["fn g(", "  a: I32,", "  b: I32,", ") -> I32 {", "  a", "}"],
        ),
        case(
            "the elements of an array",
            &["fn g() -> I32 {", "  let xs = [", "    1,", "    2", "  ]", "  xs[0]", "}"],
            &["fn g() -> I32 {", "  let xs = [", "    1,", "    2,", "  ]", "  xs[0]", "}"],
        ),
        case(
            "the elements of an array, the bracket after the last one",
            &["fn g() -> I32 {", "  let xs = [", "    1,", "    2]", "  xs[0]", "}"],
            &["fn g() -> I32 {", "  let xs = [", "    1,", "    2,", "  ]", "  xs[0]", "}"],
        ),
        case(
            "the elements of a tuple",
            &["fn g() -> I32 {", "  let t = (", "    1,", "    2.0", "  )", "  1", "}"],
            &["fn g() -> I32 {", "  let t = (", "    1,", "    2.0,", "  )", "  1", "}"],
        ),
        case(
            "the fields of a struct literal",
            &["fn g() -> P {", "  let p = P {", "    x: 1.0,", "    y: 2.0", "  }", "  p", "}"],
            &["fn g() -> P {", "  let p = P {", "    x: 1.0,", "    y: 2.0,", "  }", "  p", "}"],
        ),
        case(
            "the fields of a struct literal, the brace after the last one",
            &["fn g() -> P {", "  let p = P {", "    x: 1.0,", "    y: 2.0 }", "  p", "}"],
            &["fn g() -> P {", "  let p = P {", "    x: 1.0,", "    y: 2.0,", "  }", "  p", "}"],
        ),
        case(
            "the inputs of a flow",
            &["flow g(", "  x: F32 at sample,", "  p: F32 at block", ") -> F32 at sample {", "  x", "}"],
            &["flow g(", "  x: F32 at sample,", "  p: F32 at block,", ") -> F32 at sample {", "  x", "}"],
        ),
        case(
            "a list of one element",
            &["fn g() -> I32 {", "  f(", "    a", "  )", "}"],
            &["fn g() -> I32 {", "  f(", "    a,", "  )", "}"],
        ),
        case(
            "a method call",
            &["fn g() -> I32 {", "  p.m(", "    a,", "    b", "  )", "}"],
            &["fn g() -> I32 {", "  p.m(", "    a,", "    b,", "  )", "}"],
        ),
    ];
    expect_fmt("block_last_comma", &cases);
}

#[test]
fn the_elements_of_a_block_are_one_level_deeper_than_the_line_of_the_opening_bracket() {
    let cases = vec![
        case(
            "elements that were not indented",
            &["fn g() -> I32 {", "  let r = f(", "a,", "b,", ")", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "  )", "  r", "}"],
        ),
        case(
            "elements indented too much",
            &["fn g() -> I32 {", "  let r = f(", "        a,", "          b,", "        )", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "  )", "  r", "}"],
        ),
        case(
            "elements indented with tabs",
            &["fn g() -> I32 {", "  let r = f(", "\t\t\ta,", "\t\t\tb,", "\t)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "  )", "  r", "}"],
        ),
        case(
            "the parameters of a declaration at the top of a file",
            &["fn g(", "      a: I32,", "      b: I32,", "      ) -> I32 {", "  a", "}"],
            &["fn g(", "  a: I32,", "  b: I32,", ") -> I32 {", "  a", "}"],
        ),
        case(
            "an array at the top of a file",
            &["const XS: Buf[I32] = [", "1,", "    2,", "  3,", "]"],
            &["const XS: Buf[I32] = [", "  1,", "  2,", "  3,", "]"],
        ),
        case(
            "the fields of a declaration",
            &["struct P {", "x: F32,", "      y: F32,", "         }"],
            &["struct P {", "  x: F32,", "  y: F32,", "}"],
        ),
        case(
            "the variants of an enum",
            &["enum E {", "A,", "        B(F32),", "   }"],
            &["enum E {", "  A,", "  B(F32),", "}"],
        ),
        case(
            "the arms of a match",
            &["fn g(o: Option[I32]) -> I32 {", "  match o {", "Some(v) => v,", "        None => 0,", "      }", "}"],
            &["fn g(o: Option[I32]) -> I32 {", "  match o {", "    Some(v) => v,", "    None => 0,", "  }", "}"],
        ),
    ];
    expect_fmt("block_indent", &cases);
}

#[test]
fn a_continuation_is_aligned_under_its_first_element_and_loses_its_last_comma() {
    let cases = vec![
        case(
            "the arguments of a call",
            &["fn g() -> I32 {", "  let r = f(a,", "b,", "          c)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(a,", "            b,", "            c)", "  r", "}"],
        ),
        case(
            "the arguments of a call, a comma after the last",
            &["fn g() -> I32 {", "  let r = f(a,", "    b,", "    c,)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(a,", "            b,", "            c)", "  r", "}"],
        ),
        case(
            "the arguments of a call, spaces before the comma",
            &["fn g() -> I32 {", "  let r = f(a ,", "    b ,", "    c)", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(a,", "            b,", "            c)", "  r", "}"],
        ),
        case(
            "the parameters of a declaration",
            &["fn g(a: I32,", "  b: I32,", "            c: I32) -> I32 {", "  a", "}"],
            &["fn g(a: I32,", "     b: I32,", "     c: I32) -> I32 {", "  a", "}"],
        ),
        case(
            "the parameters of a declaration, a comma after the last",
            &["fn g(a: I32,", "     b: I32,) -> I32 {", "  a", "}"],
            &["fn g(a: I32,", "     b: I32) -> I32 {", "  a", "}"],
        ),
        case(
            "the elements of an array",
            &["fn g() -> I32 {", "  let xs = [1,", "2,", "      3]", "  xs[0]", "}"],
            &["fn g() -> I32 {", "  let xs = [1,", "            2,", "            3]", "  xs[0]", "}"],
        ),
        case(
            "the elements of a tuple",
            &["fn g() -> I32 {", "  let t = (1,", "2.0,", "      a)", "  1", "}"],
            &["fn g() -> I32 {", "  let t = (1,", "           2.0,", "           a)", "  1", "}"],
        ),
        case(
            "the fields of a struct literal",
            &["fn g() -> P {", "  let p = P { x: 1.0,", "y: 2.0,", "      z: 3.0 }", "  p", "}"],
            &["fn g() -> P {", "  let p = P { x: 1.0,", "              y: 2.0,", "              z: 3.0 }", "  p", "}"],
        ),
        case(
            "the fields of a struct literal, a comma after the last",
            &["fn g() -> P {", "  let p = P { x: 1.0,", "              y: 2.0, }", "  p", "}"],
            &["fn g() -> P {", "  let p = P { x: 1.0,", "              y: 2.0 }", "  p", "}"],
        ),
        case(
            "the inputs of a flow",
            &["flow g(x: F32 at sample,", "p: F32 at block,", "      q: F32 at init) -> F32 at sample {", "  x", "}"],
            &[
                "flow g(x: F32 at sample,",
                "       p: F32 at block,",
                "       q: F32 at init) -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
        case(
            "an argument list of two lines",
            &["fn g() -> I32 {", "  f(a,", "b)", "}"],
            &["fn g() -> I32 {", "  f(a,", "    b)", "}"],
        ),
        case(
            "a method call",
            &["fn g() -> I32 {", "  p.m(a,", "b)", "}"],
            &["fn g() -> I32 {", "  p.m(a,", "      b)", "}"],
        ),
    ];
    expect_fmt("continuation_align", &cases);
}

#[test]
fn the_closing_bracket_of_a_one_line_list_and_of_a_continuation_follows_the_last_element() {
    // Read from §3.2: a list on one line has all its elements on the line of the opening bracket, and the
    // closing bracket of a continuation follows the last element; only the block form has a line for the
    // closing bracket. (The text does not say it in so many words; see the report.)
    let cases = vec![
        case(
            "a one-line list, the bracket on the next line",
            &["fn g() -> I32 {", "  let a = f(a, b", "  )", "  a", "}"],
            &["fn g() -> I32 {", "  let a = f(a, b)", "  a", "}"],
        ),
        case(
            "an array, the bracket on the next line",
            &["fn g() -> I32 {", "  let c = [1, 2", "  ]", "  1", "}"],
            &["fn g() -> I32 {", "  let c = [1, 2]", "  1", "}"],
        ),
        case(
            "a continuation, the bracket on the next line",
            &["fn g() -> I32 {", "  let b = f(a,", "            b", "  )", "  b", "}"],
            &["fn g() -> I32 {", "  let b = f(a,", "            b)", "  b", "}"],
        ),
        case(
            "a struct literal in a continuation, the brace on the next line",
            &["fn g() -> I32 {", "  let d = P { x: 1,", "              y: 2", "  }", "  1", "}"],
            &["fn g() -> I32 {", "  let d = P { x: 1,", "              y: 2 }", "  1", "}"],
        ),
    ];
    expect_fmt("closing_bracket", &cases);
}

#[test]
fn a_block_in_the_body_of_a_par() {
    let cases = vec![case(
        "a block form call in a par over a range",
        &[
            "flow g(x: F32 at sample) -> Span[F32] at sample {",
            "  par i in 0 ..< 2 {",
            "    mix(",
            "      x,",
            "      i.round_f32()",
            "    )",
            "  }",
            "}",
        ],
        &[
            "flow g(x: F32 at sample) -> Span[F32] at sample {",
            "  par i in 0 ..< 2 {",
            "    mix(",
            "      x,",
            "      i.round_f32(),",
            "    )",
            "  }",
            "}",
        ],
    )];
    expect_fmt("par_block", &cases);
}

#[test]
fn the_form_is_the_writers_and_not_the_length_of_the_line() {
    // No line is folded and none is joined: a block of two short elements stays a block, and a long line
    // stays one line (docs/onsa-tools.md §3.2: the writer's line breaks stay, nothing is wrapped).
    let long_args = "a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b";
    let long_call = format!("  let r = f({long_args})");
    let short_block: Vec<&str> = vec!["fn g() -> I32 {", "  let r = f(", "    a,", "    b,", "  )", "  r", "}"];
    let long_call_ref: &str = &long_call;
    let cases = vec![
        ("a block of two short elements", src(&short_block), src(&short_block)),
        (
            "a very long call on one line",
            src(&["fn g(a: I32, b: I32) -> I32 {", long_call_ref, "  r", "}"]),
            src(&["fn g(a: I32, b: I32) -> I32 {", long_call_ref, "  r", "}"]),
        ),
        (
            "a one-line call with a trailing comma stays on its line",
            src(&["fn g(a: I32, b: I32) -> I32 {", "  f(a, b,)", "}"]),
            src(&["fn g(a: I32, b: I32) -> I32 {", "  f(a, b)", "}"]),
        ),
        (
            "a continuation of two short elements",
            src(&["fn g(a: I32, b: I32) -> I32 {", "  f(a,", "    b)", "}"]),
            src(&["fn g(a: I32, b: I32) -> I32 {", "  f(a,", "    b)", "}"]),
        ),
        (
            "a block of one short element",
            src(&["fn g(a: I32) -> I32 {", "  f(", "    a,", "  )", "}"]),
            src(&["fn g(a: I32) -> I32 {", "  f(", "    a,", "  )", "}"]),
        ),
    ];
    expect_fmt("form_by_breaks", &cases);
}

#[test]
fn the_forms_of_the_bodies_of_a_declaration_and_of_a_match_are_the_block_form() {
    // The fields of a struct, the variants of an enum and the arms of a match are written in the block
    // form: a `,` after every element, also after the last. (The one-line and the continuation of these
    // braces are not here: the spaces inside the braces are not named, see the report.)
    let cases = vec![
        case(
            "the fields of a struct",
            &["struct P {", "  x: F32,", "  y: F32", "}"],
            &["struct P {", "  x: F32,", "  y: F32,", "}"],
        ),
        case(
            "the fields of a struct, the brace after the last",
            &["struct P {", "  x: F32,", "  y: F32 }"],
            &["struct P {", "  x: F32,", "  y: F32,", "}"],
        ),
        case(
            "the fields of a generic struct",
            &["pub struct Pair[A, B] {", "  a: A,", "  b: B", "}"],
            &["pub struct Pair[A, B] {", "  a: A,", "  b: B,", "}"],
        ),
        case(
            "the variants of an enum",
            &["enum E {", "  A,", "  B(F32),", "  C(I32, F32)", "}"],
            &["enum E {", "  A,", "  B(F32),", "  C(I32, F32),", "}"],
        ),
        case(
            "the variants of an enum, the brace after the last",
            &["pub enum E {", "  A,", "  B(F32) }"],
            &["pub enum E {", "  A,", "  B(F32),", "}"],
        ),
        case(
            "the arms of a match",
            &["fn g(o: Option[I32]) -> I32 {", "  match o {", "    Some(v) => v,", "    None => 0", "  }", "}"],
            &["fn g(o: Option[I32]) -> I32 {", "  match o {", "    Some(v) => v,", "    None => 0,", "  }", "}"],
        ),
        case(
            "the arms of a match with guards",
            &[
                "fn g(o: Option[I32]) -> I32 {",
                "  match o {",
                "    Some(v) if v > 0 => v,",
                "    Some(v) => -v,",
                "    None => 0",
                "  }",
                "}",
            ],
            &[
                "fn g(o: Option[I32]) -> I32 {",
                "  match o {",
                "    Some(v) if v > 0 => v,",
                "    Some(v) => -v,",
                "    None => 0,",
                "  }",
                "}",
            ],
        ),
        case(
            "the arms of a match in a let",
            &[
                "fn g(o: Option[I32]) -> I32 {",
                "  let k = match o {",
                "    Some(v) => v,",
                "    None => 0",
                "  }",
                "  k",
                "}",
            ],
            &[
                "fn g(o: Option[I32]) -> I32 {",
                "  let k = match o {",
                "    Some(v) => v,",
                "    None => 0,",
                "  }",
                "  k",
                "}",
            ],
        ),
        case(
            "the arms of a match on tilde in a flow",
            &[
                "flow g(k: U32 at sample) -> F32 at sample {",
                "  match~ k {",
                "    0 => saw~(1.0),",
                "    _ => saw~(2.0)",
                "  }",
                "}",
            ],
            &[
                "flow g(k: U32 at sample) -> F32 at sample {",
                "  match~ k {",
                "    0 => saw~(1.0),",
                "    _ => saw~(2.0),",
                "  }",
                "}",
            ],
        ),
    ];
    expect_fmt("bodies_block", &cases);
}

#[test]
fn a_block_inside_a_branch_a_loop_and_a_closure_is_one_level_deeper_than_its_own_line() {
    let cases = vec![
        case(
            "a block in a branch",
            &[
                "fn g(c: Bool) -> I32 {",
                "  if c {",
                "    let r = f(",
                "      a,",
                "      b",
                "    )",
                "  } else {",
                "    let r = [",
                "      1,",
                "      2",
                "    ]",
                "  }",
                "  1",
                "}",
            ],
            &[
                "fn g(c: Bool) -> I32 {",
                "  if c {",
                "    let r = f(",
                "      a,",
                "      b,",
                "    )",
                "  } else {",
                "    let r = [",
                "      1,",
                "      2,",
                "    ]",
                "  }",
                "  1",
                "}",
            ],
        ),
        case(
            "a block in a loop",
            &[
                "fn g(xs: Span[I32]) -> I32 {",
                "  for x in xs {",
                "    f(",
                "      x,",
                "      x",
                "    )",
                "  }",
                "  1",
                "}",
            ],
            &[
                "fn g(xs: Span[I32]) -> I32 {",
                "  for x in xs {",
                "    f(",
                "      x,",
                "      x,",
                "    )",
                "  }",
                "  1",
                "}",
            ],
        ),
        case(
            "a block in a closure",
            &[
                "fn g() -> I32 {",
                "  let h = fn(a: I32) -> I32 {",
                "    f(",
                "      a,",
                "      a",
                "    )",
                "  }",
                "  1",
                "}",
            ],
            &[
                "fn g() -> I32 {",
                "  let h = fn(a: I32) -> I32 {",
                "    f(",
                "      a,",
                "      a,",
                "    )",
                "  }",
                "  1",
                "}",
            ],
        ),
        case(
            "a block in a method of an impl",
            &["impl P {", "  fn m(self) -> I32 {", "    f(", "      1,", "      2", "    )", "  }", "}"],
            &["impl P {", "  fn m(self) -> I32 {", "    f(", "      1,", "      2,", "    )", "  }", "}"],
        ),
        case(
            "the parameters of a method",
            &["impl P {", "  fn m(", "    self,", "    a: I32", "  ) -> I32 {", "    a", "  }", "}"],
            &["impl P {", "  fn m(", "    self,", "    a: I32,", "  ) -> I32 {", "    a", "  }", "}"],
        ),
        case(
            "a continuation in a branch",
            &["fn g(c: Bool) -> I32 {", "  if c {", "    let r = f(a,", "      b)", "  }", "  1", "}"],
            &["fn g(c: Bool) -> I32 {", "  if c {", "    let r = f(a,", "              b)", "  }", "  1", "}"],
        ),
    ];
    expect_fmt("lists_in_blocks", &cases);
}

#[test]
fn a_list_of_one_line_lists_keeps_the_inner_lists_on_their_lines() {
    let cases = vec![
        case(
            "structs in an array",
            &["fn g() -> I32 {", "  let ps = [", "    P {x: 1.0,y: 2.0},", "    P {x: 3.0,y: 4.0}", "  ]", "  1", "}"],
            &[
                "fn g() -> I32 {",
                "  let ps = [",
                "    P { x: 1.0, y: 2.0 },",
                "    P { x: 3.0, y: 4.0 },",
                "  ]",
                "  1",
                "}",
            ],
        ),
        case(
            "lists in the arguments of a call",
            &[
                "fn g() -> I32 {",
                "  let r = f(",
                "    h(1,2),",
                "    [3,4],",
                "    (5,6),",
                "    P {x: 1}",
                "  )",
                "  r",
                "}",
            ],
            &[
                "fn g() -> I32 {",
                "  let r = f(",
                "    h(1, 2),",
                "    [3, 4],",
                "    (5, 6),",
                "    P { x: 1 },",
                "  )",
                "  r",
                "}",
            ],
        ),
        case(
            "operators in the elements",
            &["fn g(a: I32, b: I32) -> I32 {", "  let r = f(", "    a+1,", "    b*2,", "    a<b", "  )", "  r", "}"],
            &[
                "fn g(a: I32, b: I32) -> I32 {",
                "  let r = f(",
                "    a + 1,",
                "    b * 2,",
                "    a < b,",
                "  )",
                "  r",
                "}",
            ],
        ),
        case(
            "lists in a continuation",
            &["fn g() -> I32 {", "  let r = f(h(1,2),", "     [3,4],", "     (5,6))", "  r", "}"],
            &["fn g() -> I32 {", "  let r = f(h(1, 2),", "            [3, 4],", "            (5, 6))", "  r", "}"],
        ),
    ];
    expect_fmt("nested_one_line", &cases);
}

#[test]
fn the_three_forms_of_the_inputs_of_a_flow_are_kept() {
    let cases = vec![
        case(
            "one line",
            &["flow g(x: F32 at sample, p: F32 at block) -> F32 at sample {", "  x", "}"],
            &["flow g(x: F32 at sample, p: F32 at block) -> F32 at sample {", "  x", "}"],
        ),
        case(
            "the block form, the last comma missing",
            &["flow g(", "  x: F32 at sample,", "  p: F32 at block", ") -> F32 at sample {", "  x", "}"],
            &["flow g(", "  x: F32 at sample,", "  p: F32 at block,", ") -> F32 at sample {", "  x", "}"],
        ),
        case(
            "the continuation",
            &["pub flow g(x: F32 at sample,", "  p: F32 at block) -> F32 at sample {", "  x", "}"],
            &["pub flow g(x: F32 at sample,", "           p: F32 at block) -> F32 at sample {", "  x", "}"],
        ),
    ];
    expect_fmt("flow_inputs", &cases);
}

// ---- the lists that `fmt` does not keep yet --------------------------------------------------------

#[test]
fn the_forms_of_a_use_list_are_kept() {
    let cases = vec![
        case("one line, the last comma goes", &["use a.{x, y,}"], &["use a.{x, y}"]),
        case("a block form", &["use a.{", "  x,", "  y,", "}"], &["use a.{", "  x,", "  y,", "}"]),
        case(
            "a block form, the last comma missing",
            &["use a.{", "  x,", "  y", "}"],
            &["use a.{", "  x,", "  y,", "}"],
        ),
        case(
            "a block form, the brace after the last name",
            &["use a.{", "  x,", "  y}"],
            &["use a.{", "  x,", "  y,", "}"],
        ),
        case("a block form of one name", &["use a.{", "  x", "}"], &["use a.{", "  x,", "}"]),
        case(
            "a block form, not indented",
            &["use std.math.{", "sqrt,", "      sum,", "}"],
            &["use std.math.{", "  sqrt,", "  sum,", "}"],
        ),
        case("a continuation", &["use a.{x,", "  y}"], &["use a.{x,", "       y}"]),
        case("a continuation, a comma after the last", &["use a.{x,", "       y,}"], &["use a.{x,", "       y}"]),
        case(
            "a continuation of three names",
            &["use std.fmt.{show,", "debug,", "      pad}"],
            &["use std.fmt.{show,", "             debug,", "             pad}"],
        ),
    ];
    expect_fmt("use_forms", &cases);
}

#[test]
fn the_forms_of_the_lists_of_a_pattern_are_kept() {
    let cases = vec![
        case(
            "a tuple pattern, the block form",
            &["fn g(t: (I32, I32)) -> I32 {", "  let (", "    a,", "    b", "  ) = t", "  a", "}"],
            &["fn g(t: (I32, I32)) -> I32 {", "  let (", "    a,", "    b,", "  ) = t", "  a", "}"],
        ),
        case(
            "a tuple pattern, the continuation",
            &["fn g(t: (I32, I32)) -> I32 {", "  let (a,", "  b) = t", "  a", "}"],
            &["fn g(t: (I32, I32)) -> I32 {", "  let (a,", "       b) = t", "  a", "}"],
        ),
        case(
            "a struct pattern, the block form",
            &["fn g(p: P) -> I32 {", "  let P {", "    x: a,", "    y: b", "  } = p", "  a", "}"],
            &["fn g(p: P) -> I32 {", "  let P {", "    x: a,", "    y: b,", "  } = p", "  a", "}"],
        ),
        case(
            "a struct pattern, the continuation",
            &["fn g(p: P) -> I32 {", "  let P { x: a,", "  y: b } = p", "  a", "}"],
            &["fn g(p: P) -> I32 {", "  let P { x: a,", "          y: b } = p", "  a", "}"],
        ),
        case(
            "the payload of a variant pattern, the block form",
            &[
                "fn g(s: S) -> I32 {",
                "  match s {",
                "    S.R(",
                "      w,",
                "      z",
                "    ) => w,",
                "    _ => 0,",
                "  }",
                "}",
            ],
            &[
                "fn g(s: S) -> I32 {",
                "  match s {",
                "    S.R(",
                "      w,",
                "      z,",
                "    ) => w,",
                "    _ => 0,",
                "  }",
                "}",
            ],
        ),
        case(
            "the payload of a variant pattern, the continuation",
            &["fn g(s: S) -> I32 {", "  match s {", "    S.R(w,", "    z) => w,", "    _ => 0,", "  }", "}"],
            &["fn g(s: S) -> I32 {", "  match s {", "    S.R(w,", "        z) => w,", "    _ => 0,", "  }", "}"],
        ),
    ];
    expect_fmt("pattern_forms", &cases);
}

// ---- `else`, `with` and the attributes -------------------------------------------------------------

#[test]
fn else_and_with_stay_on_the_line_of_the_closing_brace() {
    let cases = vec![
        body(
            "else, one space",
            &["  if a < b {", "    return 1", "  } else {", "    return 2", "  }", "  3"],
            &["  if a < b {", "    return 1", "  } else {", "    return 2", "  }", "  3"],
        ),
        body(
            "else, more spaces",
            &["  if a < b {", "    return 1", "  }   else   {", "    return 2", "  }", "  3"],
            &["  if a < b {", "    return 1", "  } else {", "    return 2", "  }", "  3"],
        ),
        body(
            "else, no space before the brace",
            &["  if a < b {", "    return 1", "  }else {", "    return 2", "  }", "  3"],
            &["  if a < b {", "    return 1", "  } else {", "    return 2", "  }", "  3"],
        ),
        body(
            "else, a tab",
            &["  if a < b {", "    return 1", "  }\telse\t{", "    return 2", "  }", "  3"],
            &["  if a < b {", "    return 1", "  } else {", "    return 2", "  }", "  3"],
        ),
        body(
            "else if",
            &[
                "  if a < b {",
                "    return 1",
                "  } else if a > b {",
                "    return 2",
                "  } else {",
                "    return 3",
                "  }",
                "  4",
            ],
            &[
                "  if a < b {",
                "    return 1",
                "  } else if a > b {",
                "    return 2",
                "  } else {",
                "    return 3",
                "  }",
                "  4",
            ],
        ),
        body(
            "else if, more spaces",
            &[
                "  if a < b {",
                "    return 1",
                "  }  else   if a > b {",
                "    return 2",
                "  }  else  {",
                "    return 3",
                "  }",
                "  4",
            ],
            &[
                "  if a < b {",
                "    return 1",
                "  } else if a > b {",
                "    return 2",
                "  } else {",
                "    return 3",
                "  }",
                "  4",
            ],
        ),
        body(
            "else in a let",
            &["  let k = if a < b {", "    1", "  }  else  {", "    2", "  }", "  k"],
            &["  let k = if a < b {", "    1", "  } else {", "    2", "  }", "  k"],
        ),
        body(
            "else in a branch",
            &[
                "  if a < b {",
                "    if a > 0 {",
                "      return 1",
                "    }  else  {",
                "      return 2",
                "    }",
                "  }",
                "  3",
            ],
            &[
                "  if a < b {",
                "    if a > 0 {",
                "      return 1",
                "    } else {",
                "      return 2",
                "    }",
                "  }",
                "  3",
            ],
        ),
        body(
            "with",
            &["  let r = handle {", "    load(a)", "  } with memory_fs", "  r"],
            &["  let r = handle {", "    load(a)", "  } with memory_fs", "  r"],
        ),
        body(
            "with, more spaces",
            &["  let r = handle {", "    load(a)", "  }   with   memory_fs", "  r"],
            &["  let r = handle {", "    load(a)", "  } with memory_fs", "  r"],
        ),
        body(
            "with and arguments",
            &["  let r = handle {", "    load(a)", "  }  with  arena(inout scratch)", "  r"],
            &["  let r = handle {", "    load(a)", "  } with arena(inout scratch)", "  r"],
        ),
        body(
            "with and a handler in place",
            &[
                "  let r = handle {",
                "    load(a)",
                "  }  with  Fs {",
                "    fn read(_: Path) -> I32 {",
                "      1",
                "    }",
                "  }",
                "  r",
            ],
            &[
                "  let r = handle {",
                "    load(a)",
                "  } with Fs {",
                "    fn read(_: Path) -> I32 {",
                "      1",
                "    }",
                "  }",
                "  r",
            ],
        ),
        case(
            "else on tilde in a flow",
            &[
                "flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {",
                "  if~ c {",
                "    lp~(x)",
                "  }  else  {",
                "    x",
                "  }",
                "}",
            ],
            &[
                "flow g(x: F32 at sample, c: Bool at sample) -> F32 at sample {",
                "  if~ c {",
                "    lp~(x)",
                "  } else {",
                "    x",
                "  }",
                "}",
            ],
        ),
    ];
    expect_fmt("else_with", &cases);
}

#[test]
fn else_and_with_on_a_line_of_their_own_are_refused() {
    // §2.5: `else`, `with` and `else if` are on the line of the `}` (E0003, a syntax-stage error), so
    // `fmt` does not rewrite the file.
    let wrap = |lines: &[&str]| in_fn(lines).join("\n") + "\n";
    let inputs: Vec<(&'static str, String)> = vec![
        (
            "else on a line of its own",
            wrap(&["  if a < b {", "    return 1", "  }", "  else {", "    return 2", "  }", "  3"]),
        ),
        (
            "else on a line of its own, after a comment",
            wrap(&["  if a < b {", "    return 1", "  } // one", "  else {", "    return 2", "  }", "  3"]),
        ),
        (
            "else if on a line of its own",
            wrap(&["  if a < b {", "    return 1", "  }", "  else if a > b {", "    return 2", "  }", "  3"]),
        ),
        (
            "the if of else if on a line of its own",
            wrap(&["  if a < b {", "    return 1", "  } else", "  if a > b {", "    return 2", "  }", "  3"]),
        ),
        ("with on a line of its own", wrap(&["  let r = handle {", "    load(a)", "  }", "  with memory_fs", "  r"])),
        (
            "with on a line of its own, after a comment",
            wrap(&["  let r = handle {", "    load(a)", "  } // one", "  with memory_fs", "  r"]),
        ),
    ];
    expect_refused("else_with_refused", "E0003", &inputs);
}

#[test]
fn the_attribute_of_an_item_is_on_a_line_of_its_own() {
    let cases = vec![
        case(
            "an attribute of a struct",
            &["@repr(c)", "pub struct S {", "  x: F32,", "}"],
            &["@repr(c)", "pub struct S {", "  x: F32,", "}"],
        ),
        case(
            "an attribute of a struct on the line of the struct",
            &["@repr(c) pub struct S {", "  x: F32,", "}"],
            &["@repr(c)", "pub struct S {", "  x: F32,", "}"],
        ),
        case(
            "an attribute of a fn on the line of the fn",
            &["@fp(relaxed) pub fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed)", "pub fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "an attribute of a fn, more spaces before the fn",
            &["@fp(relaxed)    fn f(x: F32) -> F32 {", "  x", "}"],
            &["@fp(relaxed)", "fn f(x: F32) -> F32 {", "  x", "}"],
        ),
        case(
            "an attribute of a flow on the line of the flow",
            &["@fp(relaxed) pub flow f(x: F32 at sample) -> F32 at sample {", "  x", "}"],
            &["@fp(relaxed)", "pub flow f(x: F32 at sample) -> F32 at sample {", "  x", "}"],
        ),
        case(
            "an attribute of a method on the line of the method",
            &["impl S {", "  @fp(relaxed) pub fn m(self) -> F32 {", "    1.0", "  }", "}"],
            &["impl S {", "  @fp(relaxed)", "  pub fn m(self) -> F32 {", "    1.0", "  }", "}"],
        ),
        case(
            "an attribute of a method, already on its own line",
            &["impl S {", "  @fp(relaxed)", "  pub fn m(self) -> F32 {", "    1.0", "  }", "}"],
            &["impl S {", "  @fp(relaxed)", "  pub fn m(self) -> F32 {", "    1.0", "  }", "}"],
        ),
        case(
            "an attribute with a value",
            &["@repr(c)   struct S {", "  x: F32,", "}"],
            &["@repr(c)", "struct S {", "  x: F32,", "}"],
        ),
        case(
            "an attribute with the spaces inside its brackets",
            &["@repr( c )", "struct S {", "  x: F32,", "}"],
            &["@repr(c)", "struct S {", "  x: F32,", "}"],
        ),
    ];
    expect_fmt("attr_item", &cases);
}

#[test]
fn the_attribute_of_an_input_of_a_flow_on_a_line_of_its_own_stays() {
    let cases = vec![
        case(
            "an attribute on its own line",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  level: F32 at block,",
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
        ),
        case(
            "two attributes, the last comma missing",
            &[
                "flow g(",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  a: F32 at block,",
                "  @param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\")",
                "  b: F32 at block",
                ") -> F32 at sample {",
                "  a",
                "}",
            ],
            &[
                "flow g(",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  a: F32 at block,",
                "  @param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\")",
                "  b: F32 at block,",
                ") -> F32 at sample {",
                "  a",
                "}",
            ],
        ),
        case(
            "the spaces in the attribute",
            &[
                "flow g(",
                "  @param(min:0.0,max:1.0,default:0.5)",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  level",
                "}",
            ],
            &[
                "flow g(",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  level: F32 at block,",
                ") -> F32 at sample {",
                "  level",
                "}",
            ],
        ),
    ];
    expect_fmt("attr_input", &cases);
}

#[test]
fn the_attribute_of_an_input_of_a_flow_written_on_the_line_of_the_input_goes_to_a_line_of_its_own() {
    let cases = vec![
        case(
            "an attribute on the line of the input",
            &[
                "flow g(",
                "  x: F32 at sample,",
                "  @param(min: 0.0, max: 1.0, default: 0.5) level: F32 at block,",
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
        ),
        case(
            "two attributes on the lines of the inputs, the last comma missing",
            &[
                "flow g(",
                "  @param(min: 0.0, max: 1.0, default: 0.5) a: F32 at block,",
                "  @param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\") b: F32 at block",
                ") -> F32 at sample {",
                "  a",
                "}",
            ],
            &[
                "flow g(",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  a: F32 at block,",
                "  @param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\")",
                "  b: F32 at block,",
                ") -> F32 at sample {",
                "  a",
                "}",
            ],
        ),
        case(
            "an attribute on the line of the input, one with a doc comment",
            &[
                "flow g(",
                "  /// The level.",
                "  @param(min: 0.0, max: 1.0, default: 0.5) level: F32 at block,",
                "  x: F32 at sample,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
            &[
                "flow g(",
                "  /// The level.",
                "  @param(min: 0.0, max: 1.0, default: 0.5)",
                "  level: F32 at block,",
                "  x: F32 at sample,",
                ") -> F32 at sample {",
                "  x",
                "}",
            ],
        ),
    ];
    expect_fmt("attr_input_same_line", &cases);
}

#[test]
#[ignore = "W3-11 U3c: fmt keeps the line break between `@mem(bulk)` and `let` (§3.2, S-497)"]
fn the_attribute_of_a_let_is_on_the_line_of_the_let() {
    let cases = vec![
        case(
            "an attribute on the line of the let",
            &["flow g(x: F32 at sample) -> F32 at sample {", "  @mem(bulk) let d = delay~(x, 4800)", "  d", "}"],
            &["flow g(x: F32 at sample) -> F32 at sample {", "  @mem(bulk) let d = delay~(x, 4800)", "  d", "}"],
        ),
        case(
            "an attribute on a line of its own",
            &["flow g(x: F32 at sample) -> F32 at sample {", "  @mem(bulk)", "  let d = delay~(x, 4800)", "  d", "}"],
            &["flow g(x: F32 at sample) -> F32 at sample {", "  @mem(bulk) let d = delay~(x, 4800)", "  d", "}"],
        ),
        case(
            "an attribute on a line of its own, in a branch",
            &[
                "flow g(c: Bool at block, x: F32 at sample) -> F32 at sample {",
                "  if c {",
                "    @mem(bulk)",
                "    let d = delay~(x, 4800)",
                "    d",
                "  } else {",
                "    x",
                "  }",
                "}",
            ],
            &[
                "flow g(c: Bool at block, x: F32 at sample) -> F32 at sample {",
                "  if c {",
                "    @mem(bulk) let d = delay~(x, 4800)",
                "    d",
                "  } else {",
                "    x",
                "  }",
                "}",
            ],
        ),
        case(
            "an attribute on a line of its own, in a fn",
            &["fn g(x: F32) -> F32 {", "  @mem(bulk)", "  let a = x", "  a", "}"],
            &["fn g(x: F32) -> F32 {", "  @mem(bulk) let a = x", "  a", "}"],
        ),
        case(
            "two attributed lets",
            &[
                "flow g(x: F32 at sample) -> F32 at sample {",
                "  @mem(bulk)",
                "  let a = delay~(x, 4800)",
                "  let g = x * 0.5",
                "  @mem(bulk)",
                "  let b = delay~(g, 64)",
                "  a + b",
                "}",
            ],
            &[
                "flow g(x: F32 at sample) -> F32 at sample {",
                "  @mem(bulk) let a = delay~(x, 4800)",
                "  let g = x * 0.5",
                "  @mem(bulk) let b = delay~(g, 64)",
                "  a + b",
                "}",
            ],
        ),
        case(
            "the spaces in the attribute",
            &["fn g(x: F32) -> F32 {", "  @mem( bulk ) let a = x", "  a", "}"],
            &["fn g(x: F32) -> F32 {", "  @mem(bulk) let a = x", "  a", "}"],
        ),
    ];
    expect_fmt("attr_let", &cases);
}
