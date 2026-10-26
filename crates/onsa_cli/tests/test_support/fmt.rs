//! Shared by the tests of what `onsa fmt` writes for a file (`fmt_comments.rs`, `fmt_lines_lists.rs`,
//! `fmt_spaces_lists.rs`, `fmt_spellings_columns_ranges.rs`): the formatter is called in the process
//! (`onsa_driver::format_file`, the function `onsa fmt` calls on each file it reads), so that no file is
//! written for a case (X-16: each file `onsa fmt` writes back is synced to the disk, `spec/tools.md` §3.6).
//! What `onsa fmt` does with the result (writes the file back, `--check`, several files at once, a file it
//! cannot write, a file it refuses stays) is pinned by `fmt_write.rs` and by the tests that run the binary.

#![allow(dead_code)]

use onsa_diag::SourceMap;
use onsa_driver::Formatted;

/// What `onsa fmt` makes of one file, by the exit codes of `spec/tools.md` §3.
#[derive(Debug, PartialEq, Eq)]
pub enum Fmt {
    /// The text of the file after `fmt`: exit code 0, and with `--check` 1 when it differs from the input.
    Text(String),
    /// The file has a diagnostic of the syntax stage and is not rewritten (exit code 2, spec §18.2): the
    /// diagnostics as `onsa fmt` prints them.
    Syntax(String),
    /// An internal error (exit code 101), as `onsa fmt` prints it.
    Internal(String),
}

/// `onsa fmt` on a file named `name` that holds `text`, on a thread with the stack of a command.
pub fn format(name: &str, text: &str) -> Fmt {
    let mut sources = SourceMap::default();
    let file = sources.add(name, text);
    match onsa_diag::stack::run(|| onsa_driver::format_file(&sources, file)) {
        Ok(Formatted::Text(out)) => Fmt::Text(out),
        Ok(Formatted::Syntax(diagnostics)) => Fmt::Syntax(onsa_diag::to_text(&sources, &diagnostics)),
        Err(e) => Fmt::Internal(e.render(&sources)),
    }
}

/// Every case is `(what, input, expected)`, the whole text of a file before and after `onsa fmt`.
/// The expected text has no diagnostic of the syntax stage (`fmt --check` on it would not end with 2);
/// `onsa fmt` on all the inputs ends with 0 and writes the expected texts; the output is a fixed point
/// (`fmt --check` on it ends with 0, and another `fmt` does not change it). `tag` names the files in the
/// messages.
pub fn expect_fmt(tag: &str, cases: &[(&str, &str, &str)]) {
    assert!(!cases.is_empty(), "no case to run");
    let again: Vec<Fmt> = cases
        .iter()
        .enumerate()
        .map(|(i, (what, _, expected))| {
            let r = format(&format!("{tag}/e{i}.onsa"), expected);
            if let Fmt::Syntax(d) = &r {
                panic!("{what}: the expected text has a diagnostic of the syntax stage:\n{d}");
            }
            r
        })
        .collect();
    let mut wrong = Vec::new();
    for (i, (what, input, expected)) in cases.iter().enumerate() {
        match format(&format!("{tag}/c{i}.onsa"), input) {
            Fmt::Text(got) if got == *expected => {}
            Fmt::Text(got) => wrong.push(format!("{what}\n--- input\n{input}--- expected\n{expected}--- got\n{got}")),
            other => panic!("{what}: onsa fmt does not end with 0: {other:?}"),
        }
    }
    assert!(wrong.is_empty(), "{} of {} files are not as expected:\n{}", wrong.len(), cases.len(), wrong.join("\n"));
    for ((what, _, expected), r) in cases.iter().zip(&again) {
        assert_eq!(*r, Fmt::Text(expected.to_string()), "{what}: the output is not a fixed point of fmt");
    }
}
