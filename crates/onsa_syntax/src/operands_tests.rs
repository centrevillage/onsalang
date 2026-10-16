//! Tests of the completion of the candidates (`crate::operands`, S-537):
//! what it reads again is bounded by the size of the file, also when a unit
//! holds many diagnostics, an `impl` many members with one each, a candidate
//! edits two units or a unit is near the nesting limit, and no candidate of
//! a file of the repository is dropped.

use onsa_diag::{Code, FileId};

use crate::CandidateReads;

/// The number of diagnostics of `src`, what the completion read again, and
/// the bytes that the check of the nesting limit read (`groups::READ`).
fn reads(src: &str) -> (usize, CandidateReads, usize) {
    let before = crate::groups::READ.get();
    let p = crate::parse(FileId(0), src);
    (p.diagnostics.len(), p.candidate_reads, crate::groups::READ.get() - before)
}

/// The text read again is at most this many times the file: one diagnostic
/// is reported in a unit, it has a candidate or two, and each is read at
/// most twice (with and without the parentheses); the check of the nesting
/// limit reads a unit only when it is near the limit. The text lexed to
/// judge whether two tokens join is bounded alike: the lines of each
/// candidate reported once, and the line of a failure once for its row.
const AT_MOST: usize = 3;

#[test]
fn the_text_read_again_is_at_most_a_constant_times_the_file() {
    let n = 200;
    let joined = "    let x = if c { 1 } else { 2 }\n    + b\n    x\n";
    let consts: String =
        (0..n).map(|k| format!("  const K{k}: I32 = if true {{ 1 }} else {{ 2 }}\n  + 1\n\n")).collect();
    let deep = deep();
    let members: String =
        (0..n).map(|k| format!("  fn m{k}(self, c: Bool, b: I32) -> I32 {{\n{joined}  }}\n\n")).collect();
    let in_one = |line: &dyn Fn(usize) -> String| -> String {
        let lines: String = (0..n).map(line).collect();
        format!("fn g(a: I32) -> I32 {{\n  a\n}}\n\nfn f(a: I32, c: Bool, b: I32) -> I32 {{\n{lines}  a\n}}\n")
    };
    let inputs = [
        // An `impl` whose members each have a line joined after an `if` (a unit each).
        ("members", format!("struct S {{\n  v: I32,\n}}\n\nimpl S {{\n{members}}}\n"), false),
        // Functions with one each.
        ("functions", (0..n).map(|k| format!("fn f{k}(c: Bool, b: I32) -> I32 {{\n{joined}}}\n\n")).collect(), false),
        // One unit with many forms of other languages: the parser stops at the first.
        ("comments", in_one(&|k| format!("  let x{k} = a /* c{k} */\n")), false),
        ("semicolons", in_one(&|k| format!("  let x{k} = a;\n")), false),
        // One line of many clocks in the types of the inputs: a diagnostic
        // and a candidate each that writes a clock apart from the token after
        // it, one reported; whether it joins is judged for that one
        // (`insert_apart`, `apart`).
        (
            "clocks in a line",
            format!(
                "pub flow lp({}) -> F32 at sample {{\n  0.5\n}}\n",
                (0..n).map(|k| format!("x{k}: Option[F32 at sample]")).collect::<Vec<_>>().join(", ")
            ),
            false,
        ),
        // One line of many `;`: one candidate takes each out, and whether
        // the tokens round each join is judged on the line once (`apart`).
        ("semicolons in a line", format!("fn f(a: I32) -> I32 {{\n  let x = a{}\n  x\n}}\n", ";".repeat(n)), false),
        ("blanks", in_one(&|k| format!("  let x{k} = g (a)\n")), false),
        ("joined lines", in_one(&|k| format!("  let x{k} = if c {{ 1 }} else {{ 2 }}\n  + b\n")), false),
        // One unit with many diagnostics of the syntax stage (the checks on its
        // tree), each with a candidate: `onsa_driver::reduce` reports one, and
        // only that one is completed (`Units::choose`).
        ("operators", in_one(&|k| format!("  let x{k} = a & b | c\n  let y{k} = a as I64 as F64\n")), true),
        // Constants of an `impl` with a line joined after an `if`.
        ("constants", format!("struct S {{\n  v: I32,\n}}\n\nimpl S {{\n{consts}}}\n"), false),
        // A candidate that edits two units: a constant and the line after it.
        (
            "two units",
            (0..n).map(|k| format!("const A{k}: I32 = if true {{ 1 }} else {{ 2 }}\n+ 1\n\n")).collect(),
            false,
        ),
        // A unit near the nesting limit, with an E0013 whose candidate would
        // go over it, and many units with an E0013 and an E0010 each.
        (
            "near the limit",
            format!(
                "{deep}{}",
                (0..n)
                    .map(|k| format!(
                        "fn f{k}() -> I32 {{\n  {{ 1 }} + {{ 2 }}\n}}\n\nfn g{k}(b: I32) -> I32 {{\n  b & b | b\n}}\n\n"
                    ))
                    .collect::<String>()
            ),
            true,
        ),
    ];
    // The stack of a command: the unit near the limit is 254 levels deep.
    onsa_diag::stack::run(move || {
        for (name, src, many) in inputs {
            let (diagnostics, r, limit) = reads(&src);
            assert!(!many || diagnostics >= n, "{name}: {diagnostics} diagnostics");
            let read = r.bytes + limit;
            assert!(
                diagnostics > 0 && r.bytes > 0,
                "{name}: nothing was read again ({diagnostics} diagnostics, {r:?})"
            );
            assert!(
                read <= AT_MOST * src.len(),
                "{name}: read {read} bytes ({r:?}, {limit}) of a file of {}",
                src.len()
            );
            assert!(
                r.lexed <= AT_MOST * src.len(),
                "{name}: lexed {} bytes ({r:?}) of a file of {}",
                r.lexed,
                src.len()
            );
            assert_eq!(r.dropped, 0, "{name}");
            if name == "semicolons in a line" || name == "clocks in a line" {
                assert!(r.lexed > 0, "the line was not lexed");
            }
            if name == "near the limit" {
                assert!(limit > 0, "the unit near the limit was not read again");
            }
        }
    });
}

#[test]
fn a_unit_near_the_limit_is_read_alone_and_its_candidate_dropped() {
    // The E0013 of the deep unit has no candidate (§18.1, §2.5): the
    // parentheses would take it over the limit. Only that unit is read again,
    // not the file: the other units are far from the limit.
    let deep = deep();
    let size = deep.len();
    let src = format!("{deep}fn f(b: I32) -> I32 {{\n  {{ 1 }} + {{ 2 }}\n}}\n");
    let (diagnostics, limit) = onsa_diag::stack::run(move || {
        let before = crate::groups::READ.get();
        let p = crate::parse(FileId(0), &src);
        let found: Vec<(Code, usize, usize)> =
            p.diagnostics.iter().map(|d| (d.code, d.fixes.len(), d.notes.len())).collect();
        (found, crate::groups::READ.get() - before)
    });
    assert_eq!(diagnostics, [(Code::E0013, 0, 1), (Code::E0013, 1, 0)]);
    assert!(0 < limit && limit < size + 8, "read {limit} bytes, the deep unit is {size}");
}

/// A function whose body is 256 levels deep, the limit (§2.5: its block,
/// 253 groups, the binary operator and the blocks of its operands), with an
/// E0013 at the bottom: its parentheses would add a level.
fn deep() -> String {
    format!("fn deep(b: I32) -> I32 {{\n  {}{{ 1 }} + {{ 2 }}{}\n}}\n\n", "(".repeat(253), ")".repeat(253))
}

#[test]
fn no_candidate_of_a_file_of_the_repository_is_dropped() {
    // The stack of a command: every file is at most 256 levels deep.
    let (read, dropped) = onsa_diag::stack::run(|| {
        let files = crate::cst_tests::repo_files();
        assert!(files.len() > 400, "only {} files found", files.len());
        let mut read = 0;
        let mut dropped = Vec::new();
        for (name, text) in &files {
            let r = crate::parse(FileId(0), text).candidate_reads;
            read += r.bytes;
            if r.dropped > 0 || r.unread > 0 {
                dropped.push(format!("{name}: {} dropped, {} kept without a reading", r.dropped, r.unread));
            }
        }
        (read, dropped)
    });
    assert!(read > 0, "no candidate was read again");
    // A candidate kept without a reading (`Units::reading` is `None`) takes
    // no parentheses: a maker that edits two lists or skips a unit shows here.
    assert!(dropped.is_empty(), "the candidates dropped or kept without a reading: {dropped:#?}");
}

/// Each unit of each file of the repository read alone in the context of its
/// list ([`crate::read`], what the completion reads): a unit without a
/// diagnostic of the syntax stage in the file (nor its members) has none
/// alone, and its tree
/// lowers (every member form of an `impl`, `trait`, `effect`, `handler` and
/// `extern`).
#[test]
fn every_unit_of_the_repository_reads_alone_in_the_context_of_its_list() {
    let (members, problems) = onsa_diag::stack::run(|| {
        let mut members = 0;
        let mut problems = Vec::new();
        for (name, text) in &crate::cst_tests::repo_files() {
            let p = crate::parse(FileId(0), text);
            for (u, unit) in p.units.list.iter().enumerate() {
                let failed = |v: &crate::units::Unit| v.syntax_failed;
                if failed(unit) || p.units.list[unit.members.clone()].iter().any(failed) || unit.item.is_none() {
                    continue;
                }
                let own = &text[unit.span.start as usize..unit.span.end as usize];
                let ctx = unit.list;
                members += usize::from(unit.parent.is_some());
                let alone = crate::read(FileId(0), own, ctx);
                let syntax: Vec<_> = alone.diagnostics.iter().filter(|d| d.stage == onsa_diag::Stage::Syntax).collect();
                if !syntax.is_empty() || alone.ast.items.is_empty() {
                    problems.push(format!("{name}: unit {u} ({ctx:?}): {syntax:?}"));
                }
            }
        }
        (members, problems)
    });
    assert!(members > 100, "only {members} members");
    assert!(problems.is_empty(), "{problems:#?}");
}

/// Another error of the unit, which the candidate brings to light, does not
/// drop it: the candidate with the parentheses is kept when it leaves no
/// more than the candidate alone did, less the E0013 it takes away.
#[test]
fn another_error_of_the_unit_keeps_the_candidate_with_its_parentheses() {
    let src =
        "fn f(a: I32, b: I32, c: Bool) -> I32 {\n  let x = if c { 1 } else { 2 }\n  + b\n  let y = a & b | a\n  x\n}\n";
    let p = crate::parse(FileId(0), src);
    assert_eq!(p.candidate_reads.dropped, 0);
    let d = p.diagnostics.iter().find(|d| d.code == onsa_diag::Code::E0020).expect("the E0020 of the line");
    let fixed: Vec<String> =
        d.fixes.iter().map(|f| onsa_diag::apply_text(src, &f.edits().iter().collect::<Vec<_>>()).unwrap()).collect();
    assert_eq!(fixed, [src.replace("if c { 1 } else { 2 }\n  + b", "(if c { 1 } else { 2 }) +\n  b")]);
    // What is left is the other error alone.
    let codes: Vec<_> = crate::parse(FileId(0), &fixed[0]).diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(codes, [onsa_diag::Code::E0010]);
}

/// The reported diagnostic of the unit of `src` that holds `at` (`onsa_driver::reduce`'s choice,
/// [`crate::units::Units::choose`]): its code, and the text after each of its candidates with
/// their titles.
fn reported(src: &str, at: &str) -> (Code, Vec<(String, String)>) {
    let p = crate::parse(FileId(0), src);
    let offset = src.find(at).expect("the place") as u32;
    let chosen = p.units.choose(&p.diagnostics.iter().collect::<Vec<_>>());
    let unit = p.units.of(onsa_diag::Span::new(FileId(0), offset, offset));
    let (d, _) = p.diagnostics.iter().zip(chosen).find(|(_, (u, c))| *c && *u == unit).expect("a reported diagnostic");
    let after = |f: &onsa_diag::Fix| onsa_diag::apply_text(src, &f.edits().iter().collect::<Vec<_>>()).unwrap();
    (d.code, d.fixes.iter().map(|f| (f.title().to_string(), after(f))).collect())
}

#[test]
fn a_candidate_that_edits_two_units_takes_the_parentheses() {
    // The line of the operator is a unit of its own (tokens of no
    // declaration, §18.1), in the list of the trait (a constant of a trait,
    // which this version refuses in a later stage, E0200).
    let src = "trait T {\n  const K: I32 = if true { 1 } else { 2 }\n  + 1\n}\n";
    let (code, fixes) = reported(src, "+ 1");
    assert_eq!(code, Code::E0020);
    let texts: Vec<&str> = fixes.iter().map(|(_, t)| t.as_str()).collect();
    assert_eq!(texts, ["trait T {\n  const K: I32 = (if true { 1 } else { 2 }) +\n  1\n}\n"]);
    // A block and a line that starts with `-`, at the top level.
    let src = "const B: I32 = { 3 }\n- 1\n";
    let (_, fixes) = reported(src, "- 1");
    let texts: Vec<&str> = fixes.iter().map(|(_, t)| t.as_str()).collect();
    assert_eq!(texts, ["const B: I32 = ({ 3 }) - 1\n"]);
}

#[test]
fn an_expression_that_only_meets_an_edit_takes_no_parentheses() {
    // S-537 (D-2): the expressions whose text an edit of the candidate shares
    // (a character at least) are parenthesized, not one it only meets at an
    // end: `[1{ 2 } + 3]` and `[1 { 2 } + 3]` have the same candidate as to
    // `{ 2 } + 3`, which stays an error of its own (E0013, the unit's second).
    for line in ["let a = [1{ 2 } + 3]", "let a = [1 { 2 } + 3]"] {
        let src = format!("fn f() -> I32 {{\n  {line}\n  0\n}}\n");
        let (_, fixes) = reported(&src, "let a");
        assert!(!fixes.is_empty(), "{line}: no candidate");
        for (title, text) in &fixes {
            assert!(text.contains("{ 2 } + 3]") && !text.contains("({ 2 })"), "{line}: {title}: {text}");
        }
    }
    // A candidate of E0010 parenthesizes the block-like operand of the chain it
    // rewrites, though it was there before; the title is the reading (§3.1).
    let src = "fn f(n: I32) -> I32 {\n  let a = n & n | { 1 }\n  a\n}\n";
    let (code, fixes) = reported(src, "let a");
    assert_eq!(code, Code::E0010);
    assert!(!fixes.is_empty());
    assert!(fixes[0].0.contains("(n & n) | { 1 }"), "{}", fixes[0].0);
    assert!(fixes[0].1.contains("let a = (n & n) | ({ 1 })"), "{}", fixes[0].1);
}
