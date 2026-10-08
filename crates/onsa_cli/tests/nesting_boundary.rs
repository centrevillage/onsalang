//! The boundary of the nesting depth limit through the built `onsa` (spec §2.5, §3.1, §18.1;
//! S-183, S-221, W3-14/t2).
//!
//! The limit is 256 levels, counted per declaration unit from 0: a function body block is level 1,
//! each form (parenthesis, prefix operator, call, `if`, block, tuple type, ...) is one level, names,
//! literals and statements are not counted, and `const` initializer's first form is level 1. 256
//! levels are accepted and 257 are E0006; the primary position is the token that makes level 257,
//! the first one in reading order, and the unit is not read any further (so no E0002 for brackets
//! that are not closed).
//!
//! Every input here is one or two lines built from the numbers below (the number of repetitions is
//! worked out in the comment of each case). The exact boundary is also in the case files
//! `tests/spec/nesting/boundary_*.onsa` and `tests/spec/negative/nesting_boundary_*.onsa`; the
//! columns of the primary token can only be tested here (the markers `//~` are line based).
//!
//! The tests of the over-the-limit inputs follow `tests/pending.toml` while the limit is not
//! there, as in `nesting.rs`: as long as the list holds the `diag-code` item `E0006`, the body must
//! FAIL, and the protocol is removed together with the item (W3-14). The accepted inputs are checked
//! always: they hold with and without the limit. They are at most 300 levels deep, which the
//! 64 MiB stack of the CLI thread takes (measured with the shallow versions).
//!
//! Not tested, because the spec does not fix the token: a chain of one binary group or a postfix
//! chain is left-nested, so "the first form over 256 in reading order" is the operator that is
//! deepest in the tree (the first one of the chain) or the one that makes the tree 257 high (the
//! last); a type with arguments (`Option[...]`: the name or the `[`), a struct literal, an enum or
//! struct pattern. Their lines are tested in the case files.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

const LIMIT: usize = 256;

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_nesting_boundary_{}_{tag}", std::process::id()));
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
    let out = Command::new(ONSA).args(args).output().expect("run onsa");
    // A signal (a stack overflow) is never an acceptable end, listed as pending or not.
    assert!(out.status.code().is_some(), "onsa {args:?} ended by a signal: {out:?}");
    out
}

fn code(out: &Output) -> i32 {
    out.status.code().unwrap()
}

fn text(out: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

// ---- the pending protocol (as in nesting.rs)

fn e0006_is_pending() -> bool {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let list = std::fs::read_to_string(root.join("tests/pending.toml")).unwrap();
    list.split("[[pending]]").any(|block| {
        let has = |line: &str| block.lines().any(|l| l.trim() == line);
        has("kind = \"diag-code\"") && has("target = \"E0006\"")
    })
}

fn limit_test(what: &str, body: impl FnOnce() -> Result<(), String>) {
    let result = body();
    if e0006_is_pending() {
        if let Err(e) = &result {
            // what is missing now, for `--nocapture`
            eprintln!("{what}: pending, fails as listed: {e}");
        }
        assert!(
            result.is_err(),
            "{what}: the behaviour is there, but tests/pending.toml still lists the diag-code E0006: remove the item (W3-14)"
        );
    } else if let Err(e) = result {
        panic!("{what}: {e}");
    }
}

macro_rules! ensure {
    ($cond:expr, $($msg:tt)+) => {
        if !$cond {
            return Err(format!($($msg)+));
        }
    };
}

// ---- JSON

#[derive(Debug, PartialEq)]
struct Diag {
    code: String,
    line: u64,
    col: u64,
    end_col: u64,
}

/// The diagnostics of `check --json`: a bare array (today) or an object with `diagnostics` (S-215).
fn diagnostics(out: &Output) -> Result<Vec<Diag>, String> {
    let v: serde_json::Value = serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("`check --json` printed no JSON ({e}): {}", text(out)))?;
    let all = match (&v, v.get("diagnostics")) {
        (serde_json::Value::Array(a), _) => a,
        (_, Some(serde_json::Value::Array(a))) => a,
        _ => return Err(format!("the JSON has no diagnostics: {v}")),
    };
    Ok(all
        .iter()
        .map(|d| Diag {
            code: d["code"].as_str().unwrap_or("?").to_string(),
            line: d["span"]["line"].as_u64().unwrap_or(0),
            col: d["span"]["col"].as_u64().unwrap_or(0),
            end_col: d["span"]["end_col"].as_u64().unwrap_or(0),
        })
        .collect())
}

// ---- the inputs

/// A source and, for an input over the limit, where the primary token is: `(line, col, token)`.
struct Input {
    name: String,
    src: String,
    /// `None` for an accepted input.
    primary: Option<(u64, u64, &'static str)>,
}

fn rep(s: &str, n: usize) -> String {
    s.repeat(n)
}

/// An accepted input.
fn ok(name: &str, src: String) -> Input {
    Input { name: name.to_string(), src, primary: None }
}

/// An input over the limit. `head` is the text before the body (all on the lines before the last
/// newline of the source, or the first line), `body` the body, and `offset` the byte offset of the
/// primary token in the body, whose text is `token`. The source is `head + body + tail`.
fn over(name: &str, head: &str, body: &str, tail: &str, offset: usize, token: &'static str) -> Input {
    let src = format!("{head}{body}{tail}");
    let at = head.len() + offset;
    assert_eq!(&src[at..at + token.len()], token, "{name}: the arithmetic of the primary position is wrong");
    let line = src[..at].matches('\n').count() as u64 + 1;
    let col = (at - src[..at].rfind('\n').map_or(0, |i| i + 1)) as u64 + 1;
    Input { name: name.to_string(), src, primary: Some((line, col, token)) }
}

const ID: &str = "pub fn id[T](x: T) -> T { x }\n";

/// Each pair is (accepted at 256, one over). `n - 1`, `n` etc. count the forms; the body block of a
/// function is level 1, so a function body takes at most 255 nested forms of one level each.
fn pairs() -> Vec<(Input, Input)> {
    let mut v = Vec::new();
    let f = |params: &str, ret: &str| format!("pub fn f({params}) -> {ret} {{ ");

    // parentheses: body 1 + 255 parentheses = 256. 256 parentheses: the 256th `(` is level 257.
    let n = LIMIT - 1;
    v.push((
        ok("paren", format!("{}{}1{} }}\n", f("", "I32"), rep("(", n), rep(")", n))),
        over("paren", &f("", "I32"), &format!("{}1{}", rep("(", n + 1), rep(")", n + 1)), " }\n", n, "("),
    ));

    // prefix operator with a parenthesis (`-(` is two levels): 127 of them and `-x` (one level) make
    // 255 under the body; 128 of them and `x`: the `(` of the 128th is level 1 + 2 * 127 + 2 = 257.
    let k = (LIMIT - 2) / 2;
    v.push((
        ok("prefix", format!("{}{}-x{} }}\n", f("x: I32", "I32"), rep("-(", k), rep(")", k))),
        over(
            "prefix",
            &f("x: I32", "I32"),
            &format!("{}x{}", rep("-(", k + 1), rep(")", k + 1)),
            " }\n",
            2 * k + 1,
            "(",
        ),
    ));

    // calls `id(id(...))`: one level per call (the name `id` is not counted); 255 calls under the
    // body block. The `(` of the 256th call is level 257, at offset 3 * 255 + 2.
    v.push((
        ok("call", format!("{ID}{}{}x{} }}\n", f("x: I32", "I32"), rep("id(", n), rep(")", n))),
        over(
            "call",
            &format!("{ID}{}", f("x: I32", "I32")),
            &format!("{}x{}", rep("id(", n + 1), rep(")", n + 1)),
            " }\n",
            3 * n + 2,
            "(",
        ),
    ));

    // tuple type in a parameter: the header is not counted, so the outermost tuple type is level 1:
    // 256 tuple types are accepted, the 257th `(` of 257 is level 257.
    let tup = |n: usize| format!("{}I32{}", rep("(", n), rep(", I32)", n));
    v.push((
        ok("tuple type", format!("pub fn f(t: {}) -> I32 {{ 1 }}\n", tup(LIMIT))),
        over("tuple type", "pub fn f(t: ", &tup(LIMIT + 1), ") -> I32 { 1 }\n", LIMIT, "("),
    ));

    // array type
    let arr = |n: usize| format!("{}I32{}", rep("[", n), rep("; 1]", n));
    v.push((
        ok("array type", format!("pub fn f(t: {}) -> I32 {{ 1 }}\n", arr(LIMIT))),
        over("array type", "pub fn f(t: ", &arr(LIMIT + 1), ") -> I32 { 1 }\n", LIMIT, "["),
    ));

    // function type: `fn(` is three characters; the 257th `fn` is at offset 3 * 256
    let fnty = |n: usize| format!("{}I32{}", rep("fn(", n), rep(") -> I32", n));
    v.push((
        ok("function type", format!("pub fn f(t: {}) -> I32 {{ 1 }}\n", fnty(LIMIT))),
        over("function type", "pub fn f(t: ", &fnty(LIMIT + 1), ") -> I32 { 1 }\n", 3 * LIMIT, "fn"),
    ));

    // `if` in the then-block: body 1; an `if` and its block are two levels. Wrapped in one
    // parenthesis, the `if` of the r-th is level 2r + 1 (r = 128: 257) and its block 2r + 2: 127
    // of them reach 256. `if c { ` is 7 bytes. Without the parenthesis the block of the 128th is
    // the first over (level 2r + 1 = 257; 127 of them reach 255), the `{` at offset 7 * 127 + 5.
    let k = (LIMIT - 2) / 2; // 127
    let nest = |n: usize| format!("{}1{}", rep("if c { ", n), rep(" } else { 0 }", n));
    v.push((
        ok("if keyword", format!("{}({} ) }}\n", f("c: Bool", "I32"), nest(k))),
        over("if keyword", &format!("{}(", f("c: Bool", "I32")), &nest(k + 1), ") }\n", 7 * k, "if"),
    ));
    v.push((
        ok("if block", format!("{}{} }}\n", f("c: Bool", "I32"), nest(k))),
        over("if block", &f("c: Bool", "I32"), &nest(k + 1), " }\n", 7 * k + 5, "{"),
    ));

    // `match` nested in an arm: one level per `match` (the arms are not counted). `match n { 0 => `
    // is 15 bytes; 255 of them reach 256, the 256th `match` is level 257.
    let mat = |n: usize| format!("{}1{}", rep("match n { 0 => ", n), rep(", _ => 0 }", n));
    v.push((
        ok("match", format!("{}{} }}\n", f("n: I32", "I32"), mat(n))),
        over("match", &f("n: I32", "I32"), &mat(n + 1), " }\n", 15 * n, "match"),
    ));

    // an `else if` chain: the `if` of the j-th link is level j + 1 and its block j + 2: 254 links
    // are accepted. The `{` of the 255th link's block is level 257. The conditions are names. The
    // first link is `if c { 1 }` (10 bytes), each other `else if c { 1 }` with its space 16 bytes
    // and the `{` at its offset 11.
    let chain = |j: usize| format!("if c {{ 1 }}{} else {{ 0 }}", rep(" else if c { 1 }", j - 1));
    v.push((
        ok("else if chain", format!("{}{} }}\n", f("c: Bool", "I32"), chain(LIMIT - 2))),
        over("else if chain", &f("c: Bool", "I32"), &chain(LIMIT - 1), " }\n", 10 + 16 * (LIMIT - 3) + 11, "{"),
    ));

    // `const`: the first form of the initializer is level 1, so 256 parentheses are accepted (a
    // function takes 255); the 257th `(` is level 257
    let konst = "pub const DEEP: I32 = ";
    v.push((
        ok("const", format!("{konst}{}1{}\n", rep("(", LIMIT), rep(")", LIMIT))),
        over("const", konst, &format!("{}1{}", rep("(", LIMIT + 1), rep(")", LIMIT + 1)), "\n", LIMIT, "("),
    ));

    // `test`: the body block is level 1 like a function body (the argument of `assert` is under it)
    let test = "test \"deep\" { assert ";
    v.push((
        ok("test", format!("{test}{}true{} }}\n", rep("(", n), rep(")", n))),
        over("test", test, &format!("{}true{}", rep("(", n + 1), rep(")", n + 1)), " }\n", n, "("),
    ));

    // a method of an `impl`: the same boundary as a function
    let imp = "pub struct S { n: I32 }\nimpl S {\n  pub fn m(self) -> I32 { ";
    v.push((
        ok("method", format!("{imp}{}1{} }}\n}}\n", rep("(", n), rep(")", n))),
        over("method", imp, &format!("{}1{}", rep("(", n + 1), rep(")", n + 1)), " }\n}\n", n, "("),
    ));

    // a chain of one group of binary operators: only the code and the line (the token is not tested)
    // is in `chain_boundary`
    v
}

/// The left-nested chain `1 + 1 + ...`: 255 operators under a body block are accepted, 256 are over.
fn chain(ops: usize) -> String {
    format!("pub fn f() -> I32 {{ 1{} }}\n", rep(" + 1", ops))
}

fn run_ok(d: &Dir, i: &Input) -> Result<(), String> {
    let f = d.file(&format!("{}.onsa", i.name.replace(' ', "_")), &i.src);
    let out = onsa(&["check", "--json", &f]);
    ensure!(code(&out) == 0, "{}: an accepted input exits {} (want 0): {}", i.name, code(&out), text(&out));
    let diags = diagnostics(&out)?;
    ensure!(diags.is_empty(), "{}: an accepted input has diagnostics {diags:?}", i.name);
    Ok(())
}

fn run_over(d: &Dir, i: &Input) -> Result<(), String> {
    let (line, col, token) = i.primary.unwrap();
    let f = d.file(&format!("{}.onsa", i.name.replace(' ', "_")), &i.src);
    let out = onsa(&["check", "--json", &f]);
    ensure!(code(&out) == 1, "{}: exits {} (want 1): {}", i.name, code(&out), text(&out));
    let diags = diagnostics(&out)?;
    let want = Diag { code: "E0006".into(), line, col, end_col: col + token.len() as u64 };
    ensure!(
        diags == vec![want],
        "{}: diagnostics {diags:?} (want one E0006 at {line}:{col}, the token `{token}`)",
        i.name
    );
    Ok(())
}

// ---- tests

/// Exactly 256 levels are accepted, in every kind of form and in every kind of unit.
#[test]
fn the_largest_accepted_inputs() {
    let d = Dir::new("ok");
    for (accepted, _) in pairs() {
        run_ok(&d, &accepted).unwrap_or_else(|e| panic!("{e}"));
    }
    let src = chain(LIMIT - 1);
    let f = d.file("chain.onsa", &src);
    let out = onsa(&["check", &f]);
    assert_eq!(code(&out), 0, "a chain of {} operators: {}", LIMIT - 1, text(&out));
}

/// 257 levels are E0006 at the token that makes level 257: the only diagnostic, with the span of
/// that token. The position is the first one in reading order.
#[test]
fn one_over_is_e0006_at_the_token() {
    limit_test("one over the limit", || {
        let d = Dir::new("over");
        let errors: Vec<String> = pairs().iter().filter_map(|(_, o)| run_over(&d, o).err()).collect();
        ensure!(errors.is_empty(), "{} of the inputs fail:\n{}", errors.len(), errors.join("\n"));
        Ok(())
    });
}

/// A chain of one group: 256 operators make 257 levels. The token is not tested (left-nested), only
/// the code and that the E0006 is on the line.
#[test]
fn a_chain_one_over_is_e0006() {
    limit_test("a chain one over the limit", || {
        let d = Dir::new("chain");
        let f = d.file("chain.onsa", &chain(LIMIT));
        let out = onsa(&["check", "--json", &f]);
        ensure!(code(&out) == 1, "exits {} (want 1): {}", code(&out), text(&out));
        let diags = diagnostics(&out)?;
        ensure!(
            diags.len() == 1 && diags[0].code == "E0006" && diags[0].line == 1,
            "diagnostics {diags:?} (want one E0006 on line 1)"
        );
        Ok(())
    });
}

/// The first form over, in reading order: a nest far deeper than the limit has the same E0006 at
/// the 256th parenthesis, and no other diagnostic. A unit that stops there is not read on, so the
/// brackets that are never closed are no E0002.
#[test]
fn the_first_form_over_and_no_closing_diagnostics() {
    limit_test("the first form over", || {
        let d = Dir::new("first");
        let head = "pub fn f() -> I32 { ";
        let inputs = [
            // 300 levels, closed
            over("300 closed", head, &format!("{}1{}", rep("(", 300), rep(")", 300)), " }\n", LIMIT - 1, "("),
            // 300 parentheses never closed, and no `}` either
            over("unclosed", head, &rep("(", 300), "", LIMIT - 1, "("),
            // 257 levels exactly, the parentheses closed but not the body
            over("unclosed body", head, &format!("{}1{}", rep("(", LIMIT), rep(")", LIMIT)), "\n", LIMIT - 1, "("),
            // 257 levels exactly, the parentheses never closed, a following line that would be an error
            over("unclosed then more", head, &rep("(", LIMIT), "\n", LIMIT - 1, "("),
        ];
        let errors: Vec<String> = inputs.iter().filter_map(|i| run_over(&d, i).err()).collect();
        ensure!(errors.is_empty(), "{} of the inputs fail:\n{}", errors.len(), errors.join("\n"));
        Ok(())
    });
}

/// The depth is per unit (§18.1): units at exactly 256 levels in one file add up to nothing, and an
/// over unit between them is the only error, at its own position.
#[test]
fn units_at_the_limit_do_not_add_up() {
    limit_test("units at the limit", || {
        let d = Dir::new("units");
        let n = LIMIT - 1;
        let unit = |name: &str, n: usize| format!("pub fn {name}() -> I32 {{ {}1{} }}\n", rep("(", n), rep(")", n));
        let mut src = String::new();
        src.push_str(&unit("a", n));
        src.push_str(&unit("b", n + 1)); // line 2: over
        src.push_str(&unit("c", n));
        src.push_str(&unit("d", n));
        let f = d.file("units.onsa", &src);
        let out = onsa(&["check", "--json", &f]);
        ensure!(code(&out) == 1, "exits {} (want 1): {}", code(&out), text(&out));
        let diags = diagnostics(&out)?;
        let col = "pub fn b() -> I32 { ".len() as u64 + n as u64 + 1;
        let want = Diag { code: "E0006".into(), line: 2, col, end_col: col + 1 };
        ensure!(diags == vec![want], "diagnostics {diags:?} (want one E0006 at 2:{col})");
        Ok(())
    });
}

/// The count is on the written source, before `fmt` takes redundant parentheses away (§2.5): a
/// file at 256 levels is formatted, and the result (shallower) is still accepted.
#[test]
fn fmt_accepts_the_largest_input_and_does_not_make_it_deeper() {
    let d = Dir::new("fmt");
    let n = LIMIT - 1;
    let src = format!("pub fn f() -> I32 {{\n  {}1{}\n}}\n", rep("(", n), rep(")", n));
    let f = d.file("deep.onsa", &src);
    let out = onsa(&["fmt", &f]);
    assert_eq!(code(&out), 0, "fmt of a file at 256 levels: {}", text(&out));
    let out = onsa(&["check", &f]);
    assert_eq!(code(&out), 0, "check after fmt: {}", text(&out));
    let out = onsa(&["fmt", "--check", &f]);
    assert_eq!(code(&out), 0, "fmt --check after fmt: {}", text(&out));
}
