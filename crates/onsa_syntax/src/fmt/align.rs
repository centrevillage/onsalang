//! The alignment of `onsa fmt` (`docs/onsa-tools.md` §3.2, S-07, S-89,
//! S-122): after the lines are printed, the `=` of the runs of single-line
//! `let` and `var` statements and the trailing comments of consecutive
//! lines are put in one column each. Only the columns of single-line
//! statements move, so that the columns the printer set in multi-line ones
//! (their continuation lines) stay and a second pass changes nothing.

use crate::lexer::BLANKS;

/// The ` = ` of a single-line `let` or `var` statement of a multi-line block
/// (one alone on its line): its output line and the column before the ` = `.
pub(super) struct LetMark {
    pub(super) line: usize,
    pub(super) col: usize,
}

/// The printed text `out` with its alignment done, ending in one line break
/// (or empty). `comment_marks` are `(line, comment text)`.
pub(super) fn finish(mut out: String, mut let_marks: Vec<LetMark>, mut comment_marks: Vec<(usize, String)>) -> String {
    while out.ends_with(' ') || out.ends_with('\n') {
        out.pop();
    }
    let mut lines: Vec<String> = out.split('\n').map(|l| l.trim_end_matches(BLANKS).to_string()).collect();

    // Align ` = ` in each run of single-line `let` / `var` statements (S-07, S-89).
    // Every run is aligned (gofmt style): the canonical form does not depend on what the
    // author wrote. Two marks are in one run when only lines of comments are between them: a
    // blank line, a statement of another kind, a multi-line statement, a `let` with an
    // attribute (none has a mark) and the line of a `{` or `}` of another block cut it (S-122).
    let_marks.sort_by_key(|m| m.line);
    let only_comments =
        |lines: &[String], a: usize, b: usize| lines[a + 1..b].iter().all(|l| l.trim_start().starts_with("//"));
    let mut i = 0;
    while i < let_marks.len() {
        let mut j = i;
        while j + 1 < let_marks.len() && only_comments(&lines, let_marks[j].line, let_marks[j + 1].line) {
            j += 1;
        }
        let max = let_marks[i..=j].iter().map(|m| m.col).max().unwrap_or(0);
        for m in &let_marks[i..=j] {
            if m.col < max {
                let l = &lines[m.line];
                let byte = l.char_indices().nth(m.col).map(|(b, _)| b).unwrap_or(l.len());
                let mut s = l[..byte].to_string();
                s.extend(std::iter::repeat_n(' ', max - m.col));
                s.push_str(&l[byte..]);
                lines[m.line] = s;
            }
        }
        i = j + 1;
    }

    // Align trailing comments in runs of consecutive lines: exactly one space after the
    // longest code of the run (gofmt style, S-07).
    comment_marks.sort_by_key(|m| m.0);
    let mut i = 0;
    while i < comment_marks.len() {
        let mut j = i;
        while j + 1 < comment_marks.len() && comment_marks[j + 1].0 == comment_marks[j].0 + 1 {
            j += 1;
        }
        let run = &comment_marks[i..=j];
        let code_of = |lines: &[String], m: &(usize, String)| -> String {
            let l = &lines[m.0];
            l[..l.len() - m.1.len()].trim_end_matches(BLANKS).to_string()
        };
        let longest = run.iter().map(|m| code_of(&lines, m).chars().count()).max().unwrap_or(0);
        let col = longest + 1;
        for m in run {
            let code = code_of(&lines, m);
            let width = code.chars().count();
            let mut s = code;
            s.extend(std::iter::repeat_n(' ', col - width));
            s.push_str(&m.1);
            lines[m.0] = s;
        }
        i = j + 1;
    }

    let mut out = lines.join("\n");
    if out.is_empty() {
        return out;
    }
    out.push('\n');
    out
}
