//! The ranges of the runs of §2.4 (S-856): a marker of a case holds the line and the column of the main
//! position, so the column where a range ends is pinned here. `data/run_ranges.tsv` was written by hand from
//! the spec: a row is the case under `tests/spec/lex/`, the line, the column of the start, the column right
//! after the end, and the text of the range. Its cases are only read.

use onsa_diag::Code;

/// The row `(file, line, start, end, found)` of `data/run_ranges.tsv`.
type Row<'a> = (&'a str, u32, u32, u32, &'a str);

/// The row of the line `line` of the data.
fn row(line: &str) -> Row<'_> {
    let parts: Vec<&str> = line.splitn(5, '\t').collect();
    let [file, at, start, end, found] = parts[..] else { panic!("no row of five columns: {line}") };
    let number = |s: &str| s.parse::<u32>().unwrap_or_else(|e| panic!("{e}: {line}"));
    (file, number(at), number(start), number(end), found)
}

/// What differs between the E0002 the check reports at the rows `rows` of the case `file` and those rows.
fn differences(file: &str, rows: &[&Row]) -> Vec<String> {
    let path = onsa_tests::case::repo_root().join("tests/spec/lex").join(file);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let checked = onsa_tests::fix_loop::check(&text).unwrap_or_else(|e| panic!("{file}: {e}"));
    let mut wrong = Vec::new();
    for &&(_, line, start, end, found) in rows {
        let at = checked.diagnostics.iter().find_map(|d| {
            let source = checked.sources.file(d.span.file);
            let (from, to) = (source.line_col(d.span.start), source.line_col(d.span.end));
            (d.code == Code::E0002 && from.line == line && from.col == start).then_some((
                to.line,
                to.col,
                &source.text()[d.span.start as usize..d.span.end as usize],
            ))
        });
        if at != Some((line, end, found)) {
            wrong.push(format!("{file}:{line}:{start}-{end} `{found}`: got {at:?}"));
        }
    }
    wrong
}

#[test]
fn the_range_of_a_run_is_the_whole_run_or_to_the_opening_delimiter() {
    let data = include_str!("data/run_ranges.tsv");
    let rows: Vec<Row> = data.lines().map(row).collect();
    assert!(!rows.is_empty(), "no row of the ranges");
    let mut files: Vec<&str> = rows.iter().map(|r| r.0).collect();
    files.dedup();
    let wrong: Vec<String> = files
        .iter()
        .flat_map(|file| differences(file, &rows.iter().filter(|r| r.0 == *file).collect::<Vec<_>>()))
        .collect();
    assert!(wrong.is_empty(), "{} of {} rows differ:\n{}", wrong.len(), rows.len(), wrong.join("\n"));
}
