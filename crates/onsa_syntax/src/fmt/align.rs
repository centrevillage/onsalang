//! The alignment of `onsa fmt` (`spec/tools.md` §3.2, S-07): after the
//! lines are printed, the trailing comments of consecutive lines are put in
//! one column. The `=` of `let` and `var` is in no column: it has one space
//! on each side, as the printer writes it (S-970).

use crate::lexer::BLANKS;

/// The printed text `out` with its alignment done, ending in one line break
/// (or empty). `comment_marks` are `(line, comment text)`.
pub(super) fn finish(mut out: String, mut comment_marks: Vec<(usize, String)>) -> String {
    while out.ends_with(' ') || out.ends_with('\n') {
        out.pop();
    }
    let mut lines: Vec<String> = out.split('\n').map(|l| l.trim_end_matches(BLANKS).to_string()).collect();

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
