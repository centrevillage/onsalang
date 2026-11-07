//! The forms of a `use` list that the case files cannot show (spec §15.1, `spec/tools.md` §3.3, §3.4; S-515,
//! S-598; W5-11 U6):
//! - the empty list on two lines with nothing between its braces (`use std.time.{` then `}`): the E0002 of the
//!   syntax stage at its `{`, with the one candidate that takes out the whole `use`, and the text after it,
//!   which the check reports nothing of. A case file cannot hold it: its marker is a comment, and a comment in
//!   the braces leaves no candidate (`tests/spec/negative/use_empty_list_comment.onsa`);
//! - the text `onsa fmt` writes for a list of one bare name (`use a.{b}` is `use a.b`, a `,` after the name
//!   goes too, `pub use` the same). The fmt cases of `tests/spec/fmt/use_one_name_*.onsa` check that the file
//!   changes and that the output is a fixed point, not its text. `onsa diff --ast` reads the two forms as the
//!   same program (§3.5). A comment at the end of the line of the `}` keeps the list (§3.4), and `diff --ast`
//!   reads it as the form without the list too.
//!
//! Everything runs in this process with no file written (X-16).

use crate::test_support;

use test_support::fmt::{diff_ast, expect_fmt};
use test_support::sweep::*;

/// §15.1, S-515: the empty list over two lines is the E0002 at its `{` (line 1, column 14), and its one
/// candidate takes the `use` out from `use` to the `}`, leaving the line break after it; the check of the
/// text after it is clean.
#[test]
fn an_empty_list_over_two_lines_has_the_candidate_that_takes_out_the_use() {
    let rest = "pub fn twice(x: I32) -> I32 {\n  x * 2\n}\n";
    let text = format!("use std.time.{{\n}}\n{rest}");
    let name = "main.onsa";
    let c = check_file(name, &text);
    assert!(ended_well(&c), "{}", c.stderr);
    assert_eq!(c.diags.len(), 1, "one diagnostic: {:?}", c.diags.iter().map(|d| &d.code).collect::<Vec<_>>());
    let d = &c.diags[0];
    assert_eq!((d.code.as_str(), d.line, d.col), ("E0002", 1, 14), "{}", d.message);
    assert_eq!(d.fixes.len(), 1, "{}", d.message);
    let mut texts = Texts::new();
    texts.insert(name.to_string(), text.clone());
    apply_fix_texts(&mut texts, &d.fixes[0]);
    assert_eq!(texts[name], format!("\n{rest}"));
    let after = check_file(name, &texts[name]);
    assert!(ended_well(&after) && after.diags.is_empty(), "after the candidate: {:?}", after.diags.len());
}

/// S-598, `spec/tools.md` §3.3: the text of a list of one bare name after `onsa fmt`, on one line, with a `,`
/// after the name, in the block form, after `pub`, and after a path that ends at a package; and the same
/// program for `diff --ast`.
#[test]
fn a_list_of_one_bare_name_is_written_without_the_list() {
    let cases = [
        ("one line", "use std.math.{sqrt}\n", "use std.math.sqrt\n"),
        ("a `,` after the name", "use std.math.{pow,}\n", "use std.math.pow\n"),
        ("the block form", "use std.math.{\n  floor,\n}\n", "use std.math.floor\n"),
        ("after `pub`", "pub use a.{b}\n", "pub use a.b\n"),
        ("a path that ends at a package", "use std.{math}\n", "use std.math\n"),
    ];
    expect_fmt("use_one_name", &cases);
    for (what, input, output) in cases {
        assert_eq!(diff_ast(input, output).0, 0, "{what}: diff --ast tells the two forms apart");
    }
}

/// `spec/tools.md` §3.4: a comment at the end of the line of the `}` belongs to the `}`, the last code of its line,
/// which the rewrite drops, so the list stays: on one line, after `pub`, and in the block form. `diff --ast` reads
/// the list as the form without it all the same (§3.4, §3.5).
#[test]
fn a_comment_after_the_closing_brace_keeps_the_list() {
    let cases = [
        ("one line", "use std.math.{sqrt} // t\n"),
        ("after `pub`", "pub use a.{b} // t\n"),
        ("the block form", "use std.math.{\n  floor,\n} // t\n"),
    ];
    let same: Vec<_> = cases.iter().map(|&(what, input)| (what, input, input)).collect();
    expect_fmt("use_one_name_kept", &same);
    assert_eq!(diff_ast("use std.math.{sqrt} // t\n", "use std.math.sqrt // t\n").0, 0, "diff --ast tells them apart");
}
