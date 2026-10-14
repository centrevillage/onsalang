//! `onsa fmt` (`docs/onsa-tools.md` §3, S-07, T1-9): writes a file in the
//! single canonical form. The printer (`fmt/print.rs`) walks the tokens of
//! the CST and keeps the line structure the author chose (one-line and
//! multi-line blocks, the form of each list, line breaks in chains, blank
//! lines up to one); the plan (`fmt/plan.rs`) drops, adds and respells the
//! tokens of §3.2 and §3.3 and adds and removes the line breaks of §3.2;
//! everything else (spacing, indentation, alignment of `=` in `let` runs and
//! of trailing comments) is normalized.

mod align;
mod plan;
mod print;
#[cfg(test)]
mod print_tests;
pub(crate) mod rewrites;
mod shape;
mod space;
#[cfg(test)]
mod table_tests;

use crate::diff::{Difference, Place, same_program};
use crate::parser::Parsed;

/// Why [`format`] gives no text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatError {
    /// The lexer or the parser reported a diagnostic (`Parsed::syntax_errors()`,
    /// R-146, S-214): the file is not formatted (§18.2).
    Syntax,
    /// The output is not the program of the input (`docs/onsa-tools.md`
    /// §3.5): a bug of fmt, an internal error (§18.2).
    Unverified(Difference),
}

/// Format a parsed file (`text` is its source). The diagnostics of later
/// stages (E0320 of the names stage) do not block formatting (§18.2, S-120).
/// The output is parsed again and compared with the input before it is given
/// ([`verify`]), whoever calls it.
pub fn format(parsed: &Parsed, text: &str) -> Result<String, FormatError> {
    if parsed.syntax_errors() {
        return Err(FormatError::Syntax);
    }
    let out = print::print(&parsed.cst, text);
    verify(parsed, text, &out)?;
    Ok(out)
}

/// The check before writing (`docs/onsa-tools.md` §3.5): `out`, parsed
/// again, has no diagnostic of the syntax stage (checked first: the
/// comparison takes trees without one) and is the program of `parsed`
/// ([`same_program`]). `parsed` has no diagnostic of the syntax stage.
pub fn verify(parsed: &Parsed, text: &str, out: &str) -> Result<(), FormatError> {
    let eof = parsed.cst.tokens().last().expect("a file ends with its Eof token").span;
    let again = crate::parse(eof.file, out);
    if let Some(first) = again.first_syntax_error() {
        let line = out[..first.span.start as usize].matches('\n').count() + 1;
        let what = format!("{} on line {line} of the output: {}", first.code.as_str(), first.message);
        let at = onsa_diag::Span::empty(eof.file, 0);
        return Err(FormatError::Unverified(Difference { place: Place::Unparsed(what), at }));
    }
    match same_program(parsed, text, &again, out) {
        Some(d) => Err(FormatError::Unverified(d)),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::FileId;

    #[test]
    fn move_expressions_round_trip() {
        let src = "fn f(move b: Buf[F32]) {\n  let y = move b\n  let s = Box { b: move y }\n  match move b {\n    _ => 1,\n  }\n}\n";
        assert_eq!(fmt(src), src);
        assert_eq!(fmt("fn f(move b: U32) {\n  let y =   move   b\n}\n"), "fn f(move b: U32) {\n  let y = move b\n}\n");
    }

    #[test]
    fn const_type_arguments_round_trip() {
        let src = "pub fn f(r: Ring[F32, 4]) -> Ring[F32, TABLE_SIZE] {\n  r\n}\n";
        assert_eq!(fmt(src), src);
    }

    fn fmt(src: &str) -> String {
        let parsed = crate::parse(FileId(0), src);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let out = crate::format(&parsed, src).unwrap();
        let again = crate::parse(FileId(0), &out);
        let out2 = crate::format(&again, &out).unwrap();
        assert_eq!(out, out2, "not idempotent");
        out
    }

    #[test]
    fn negative_literal_patterns_keep_their_comments_once() {
        // The parentheses stay, the spaces go (S-185); a comment inside is kept once on its
        // line with the line break after it (`docs/onsa-tools.md` §3.4, S-58; W2-06/b: the
        // comment was printed twice, `) = // c`), and the output parses again.
        let kept = |src: &'static str| (src, src);
        for (src, want) in [
            kept("fn p(x: I32) -> I32 {\n  match x {\n    -( // c\n      5\n    ) => 5,\n    _ => 0,\n  }\n}\n"),
            kept("fn p(x: I32) -> I32 {\n  match x {\n    -(6 // c\n    ) | -7 => 6,\n    _ => 0,\n  }\n}\n"),
            (
                "fn p(x: I32) -> I32 {\n  match x {\n    -( ( 2 ) ) => 2,\n    _ => 0,\n  }\n}\n",
                "fn p(x: I32) -> I32 {\n  match x {\n    -((2)) => 2,\n    _ => 0,\n  }\n}\n",
            ),
        ] {
            let out = fmt(src);
            assert_eq!(out, want, "from {src}");
            assert!(crate::parse(FileId(0), &out).diagnostics.is_empty(), "{out}");
        }
    }

    #[test]
    fn a_value_call_reads_its_dot_from_the_tree_and_not_from_a_comment() {
        // W3-20/b: fmt took the `.` of `.(` from the text, so a `.` or a `(` in a comment
        // between the callee and the `.` changed the output, and an integer literal callee
        // was joined to its `.(` on one line (`1.(` read as the literal `1.` then, S-350). The
        // output is the same whatever the comment says, keeps the line break before a `.(`
        // that starts a line (as `.max(1)` does), and reads to the same tree. Each comment
        // stays on its line (`docs/onsa-tools.md` §3.4, R-199, S-58): these are canonical.
        let cases = [
            // e3, e4: a comment with and without `.` and `(` between the callee and `.(`.
            "pub fn g(f: fn(I32) -> I32) -> I32 {\n  let a = f // a.b ()\n    .(1)\n  a\n}\n",
            "pub fn g(f: fn(I32) -> I32) -> I32 {\n  let a = f // ab ()\n    .(1)\n  a\n}\n",
            // e5: a `.` in a comment after the call.
            "pub fn g(f: fn(I32) -> I32) -> I32 {\n  let a = f.(1) // a.b\n  a\n}\n",
            // d2: a comment line between the callee and the `.(` of the next line.
            "pub fn g(f: fn(I32) -> I32) -> I32 {\n  let a = f\n    // see x.y (and z)\n    .(1)\n  a\n}\n",
            // w1: an integer literal callee keeps its line break before `.(`.
            "pub fn p(f: fn(I32) -> I32) -> I32 {\n  let r = f.(1 // c.d (e)\n    .(1))\n  r\n}\n",
        ];
        for src in cases {
            let out = fmt(src);
            assert_eq!(out, src);
            let (old, new) = (crate::parse(FileId(0), src), crate::parse(FileId(0), &out));
            assert!(new.diagnostics.is_empty(), "{out}: {:?}", new.diagnostics);
            assert!(crate::diff::diff(&old, src, &new, &out).is_empty(), "{out}");
        }
    }

    #[test]
    fn whitespace_is_normalized() {
        assert_eq!(
            fmt("fn f(x:F32)->F32{\nlet a=x+(y*z)\na\n}"),
            "fn f(x: F32) -> F32 {\n  let a = x + (y * z)\n  a\n}\n"
        );
        assert_eq!(fmt("fn f( a : I32 , b:I32 ) { g( a,b ) }"), "fn f(a: I32, b: I32) { g(a, b) }\n");
        assert_eq!(fmt("fn f(x: F32) -> F32 {  -x.abs()  }"), "fn f(x: F32) -> F32 { -x.abs() }\n");
        assert_eq!(fmt("fn f(x: I32) -> F64 { ( x as F64 ) }"), "fn f(x: I32) -> F64 { (x as F64) }\n");
        assert_eq!(fmt("fn f() uses { Alloc , Fs } {}"), "fn f() uses {Alloc, Fs} {}\n");
        assert_eq!(fmt("use std.math.{ exp ,cos }"), "use std.math.{exp, cos}\n");
    }

    #[test]
    fn call_marks_are_tight() {
        assert_eq!(
            fmt("flow v(f0: Ctl[F32]) -> Sig[F32] { saw~(f0) }"),
            "flow v(f0: Ctl[F32]) -> Sig[F32] { saw~(f0) }\n"
        );
        assert_eq!(
            fmt("fn f(inout out: Span[F32]) { out.fill!( 0.0 ) }"),
            "fn f(inout out: Span[F32]) { out.fill!(0.0) }\n"
        );
    }

    #[test]
    fn trailing_commas_follow_layout() {
        // Block style gets a trailing comma; inline has none; visual style has none.
        assert_eq!(fmt("struct P {\n  x: F32,\n  y: F32\n}"), "struct P {\n  x: F32,\n  y: F32,\n}\n");
        assert_eq!(fmt("fn f() { g(1, 2,) }"), "fn f() { g(1, 2) }\n");
        assert_eq!(fmt("fn f() {\n  g(1,\n      2,\n     3)\n}"), "fn f() {\n  g(1,\n    2,\n    3)\n}\n");
        assert_eq!(fmt("fn f() {\n  g(\n    1, 2,\n    3\n  )\n}"), "fn f() {\n  g(\n    1, 2,\n    3,\n  )\n}\n");
    }

    #[test]
    fn blank_lines_collapse() {
        assert_eq!(fmt("fn a() {}\n\n\n\nfn b() {}\n"), "fn a() {}\n\nfn b() {}\n");
        assert_eq!(fmt("fn a() {}\nfn b() {}\n"), "fn a() {}\nfn b() {}\n");
        assert_eq!(fmt("fn f() {\n\n  let a = 1\n\n\n  let b = 2\n\n}\n"), "fn f() {\n  let a = 1\n\n  let b = 2\n}\n");
        assert_eq!(fmt("fn a() {}\n\n\n"), "fn a() {}\n");
        assert_eq!(fmt(""), "");
    }

    #[test]
    fn trailing_return_is_removed() {
        assert_eq!(
            fmt("fn f(x: I32) -> I32 {\n  let y = x\n  return y\n}\n"),
            "fn f(x: I32) -> I32 {\n  let y = x\n  y\n}\n"
        );
        // Only at the end of the function body: an early return stays.
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n"),
            "fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n"
        );
    }

    #[test]
    fn one_line_and_multi_line_blocks_are_kept() {
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 { if c { 1 } else { 2 } }"),
            "fn f(c: Bool) -> I32 { if c { 1 } else { 2 } }\n"
        );
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}"),
            "fn f(c: Bool) -> I32 {\n  if c {\n    1\n  } else {\n    2\n  }\n}\n"
        );
        assert_eq!(
            fmt("fn f(c: Bool) -> I32 {\n  match c {\n    true => 1,\n    false => 2\n  }\n}"),
            "fn f(c: Bool) -> I32 {\n  match c {\n    true => 1,\n    false => 2,\n  }\n}\n"
        );
    }

    #[test]
    fn continuation_lines_are_kept() {
        assert_eq!(
            fmt("fn f(x: F32) -> F32 {\n  let y = x +\n        1.0\n  y\n}"),
            "fn f(x: F32) -> F32 {\n  let y = x +\n    1.0\n  y\n}\n"
        );
        assert_eq!(fmt("fn f(x: F32) -> F32 {\n  x\n      .abs()\n}"), "fn f(x: F32) -> F32 {\n  x\n    .abs()\n}\n");
    }

    #[test]
    fn let_runs_are_always_aligned() {
        assert_eq!(
            fmt("fn f() {\n  let r  = 1\n  let y1 = 2\n  let y = 3\n}"),
            "fn f() {\n  let r  = 1\n  let y1 = 2\n  let y  = 3\n}\n"
        );
        // Canonical regardless of the author's spacing (S-07).
        assert_eq!(fmt("fn f() {\n  let st = 1\n  let t = 2\n}"), "fn f() {\n  let st = 1\n  let t  = 2\n}\n");
        // Annotated bindings, patterns and `var` are in the run (S-89); a line of comments
        // does not cut it (S-122).
        assert_eq!(
            fmt("fn f(t: (I32, I32)) {\n  let r  = 1\n  let x: I32 = 2\n  // c\n  var y1 = 3\n  let (a, b) = t\n}"),
            "fn f(t: (I32, I32)) {\n  let r      = 1\n  let x: I32 = 2\n  // c\n  var y1     = 3\n  let (a, b) = t\n}\n"
        );
        // A blank line, another statement, a multi-line statement and a `let` with an
        // attribute cut it (S-122).
        let cut = "fn f() {\n  let a = 1\n\n  let bb = 2\n  g()\n  let ccc = 3\n  let d = h(1,\n            2)\n  let eeee = 4\n  @mem(bulk) let ff = 5\n  let g = 6\n}\n";
        assert_eq!(fmt(cut), cut);
        // The statements of other blocks are in no run with these.
        let blocks = "fn f(c: Bool) {\n  let a = 1\n  if c { let bbb = 2 }\n  let cc = {\n    let dddd = 3\n    dddd\n  }\n}\nfn g() { let eeeee = 4 }\nfn h() { let f = 5 }\n";
        assert_eq!(fmt(blocks), blocks);
        // A run aligns again to the same text (idempotence).
        let once = fmt("fn f() {\n  let a: I32 = 1\n  // c\n  let bb = 2\n}");
        assert_eq!(once, "fn f() {\n  let a: I32 = 1\n  // c\n  let bb     = 2\n}\n");
        assert_eq!(fmt(&once), once);
    }

    #[test]
    fn ranges_have_a_space_on_each_side() {
        assert_eq!(
            fmt("fn f(n: I32) {\n  for i in 0..<n+1 {}\n  par j in n-1..=n { g() }\n}"),
            "fn f(n: I32) {\n  for i in 0 ..< n + 1 {}\n  par j in n - 1 ..= n { g() }\n}\n"
        );
    }

    #[test]
    fn numbers_take_their_canonical_spelling() {
        assert_eq!(
            fmt("fn f() {\n  let a = 0X1f_ + 0B1__0 + 1__000_\n  let b = 01.50E+03 + 1e_0_3 + 2.5E-0_7\n  t.0\n}"),
            "fn f() {\n  let a = 0x1F + 0b1_0 + 1_000\n  let b = 1.50e03 + 1e0_3 + 2.5e-0_7\n  t.0\n}\n"
        );
        assert_eq!(
            fmt(
                "fn f(x: I32) -> I32 {\n  match x {\n    0X1f => 1,\n    (1_) => 2,\n    -( 0b1_ ) => 3,\n    -1__0 => 4,\n    _ => 0,\n  }\n}"
            ),
            "fn f(x: I32) -> I32 {\n  match x {\n    0x1F => 1,\n    (1) => 2,\n    -(0b1) => 3,\n    -1_0 => 4,\n    _ => 0,\n  }\n}\n"
        );
    }

    #[test]
    fn comments_are_preserved_and_aligned() {
        let src = "// head\n/// doc\nfn f() {\n  // inside\n  let a = 1 // one\n  let bb = 2    // two\n\n  // before tail\n  a\n}\n";
        let want = "// head\n/// doc\nfn f() {\n  // inside\n  let a  = 1 // one\n  let bb = 2 // two\n\n  // before tail\n  a\n}\n";
        assert_eq!(fmt(src), want);
        // Exactly one space after the longest code of the run, whatever the author wrote.
        assert_eq!(fmt("fn f() {\n  let a = 1        // c\n}\n"), "fn f() {\n  let a = 1 // c\n}\n");
        // Comments before `}` and at end of file survive.
        assert_eq!(
            fmt("fn f() {\n  let a = 1\n  // last\n}\n// eof\n"),
            "fn f() {\n  let a = 1\n  // last\n}\n// eof\n"
        );
    }

    #[test]
    fn refuses_files_with_syntax_errors() {
        let src = "fn f() {\n  let a = x + y % z\n}\n";
        let parsed = crate::parse(FileId(0), src);
        assert_eq!(crate::format(&parsed, src), Err(crate::fmt::FormatError::Syntax));
        // Naming errors do not block formatting.
        let src = "fn Bad() {}\n";
        let parsed = crate::parse(FileId(0), src);
        assert_eq!(crate::format(&parsed, src), Ok("fn Bad() {}\n".to_string()));
    }

    /// R-204: the check before writing refuses an output that is not the
    /// program of the input (`docs/onsa-tools.md` §3.5). A correct fmt does
    /// not make one, so the outputs are false ones.
    #[test]
    fn the_check_refuses_an_output_of_another_program() {
        use crate::diff::Place;
        use crate::fmt::FormatError;
        let src = "fn f() -> I32 {\n  let a = 1 // one\n  let b = 2\n  return a\n}\n";
        let parsed = crate::parse(FileId(0), src);
        let check = |out: &str| match crate::fmt::verify(&parsed, src, out) {
            Ok(()) => None,
            Err(FormatError::Unverified(d)) => {
                Some((d.place, src[d.at.start as usize..].lines().next().unwrap_or("").to_string()))
            }
            Err(e) => panic!("{e:?}"),
        };
        let good = "fn f() -> I32 {\n  let a = 1 // one\n  let b = 2\n  a\n}\n";
        assert_eq!(crate::format(&parsed, src).as_deref(), Ok(good));
        assert_eq!(check(good), None);
        // A comment lost, a comment of another text.
        assert_eq!(check(&good.replace(" // one", "")), Some((Place::Comment(1), "// one".into())));
        assert_eq!(check(&good.replace("// one", "// on")), Some((Place::Comment(1), "// one".into())));
        // A statement lost.
        assert_eq!(check(&good.replace("  let b = 2\n", "")), Some((Place::Item("fn f".into()), "let b = 2".into())));
        // An output that does not parse.
        // An output with a syntax error is `Unparsed` before any comparison
        // (W3-11/b2 A: the comparison takes no broken tree): a body not
        // closed, an error in the middle of the body, extra tokens.
        let unparsed = |out: &str| {
            let got = check(out);
            assert!(
                matches!(&got, Some((Place::Unparsed(w), at)) if w.starts_with("E0") && at.starts_with("fn f")),
                "{got:?}"
            );
        };
        unparsed("fn f() -> I32 {\n  let a = 1 // one\n  let b = 2\n  a\n");
        unparsed("fn f() -> I32 {\n  let a = 1 // one\n  let = 2\n  a\n}\n");
        unparsed(&format!("{good}fn g() {{}} )\n"));
        unparsed(&good.replace("  a\n}\n", "  a\n}\n)\n"));
        // The `return` of the input, which the comparison rewrites, with an
        // output not closed (W3-11/b2 A).
        let src = "fn f() -> I32 {\n  return 1\n}\n";
        let parsed = crate::parse(FileId(0), src);
        let got = crate::fmt::verify(&parsed, src, "fn f() -> I32 {\n  1\n");
        assert!(matches!(&got, Err(FormatError::Unverified(d)) if matches!(d.place, Place::Unparsed(_))), "{got:?}");
    }
}
