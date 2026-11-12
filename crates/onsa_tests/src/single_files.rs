//! Single-file inputs checked as `onsa check` checks them, for the tools of
//! the fix candidates (`onsa_cases --fix-same-place`, `--fix-contract`, `--fix-loop`): reading
//! one, and running the inputs on threads with the stack of a command; and
//! formatted as `onsa fmt` formats them (`onsa_cases --fmt`, tools/fmt_props.py).

/// The text of an input file, or why it cannot be read (as `onsa check`).
pub fn read_input(path: &str) -> Result<String, String> {
    text_of(std::fs::read(path))
}

/// The text of the bytes of an input, or why they cannot be read ([`read_input`]).
pub fn text_of(bytes: std::io::Result<Vec<u8>>) -> Result<String, String> {
    match bytes.map(String::from_utf8) {
        Err(e) => Err(e.to_string()),
        Ok(Err(_)) => Err("not UTF-8".into()),
        Ok(Ok(text)) => Ok(text),
    }
}

/// What `onsa_cases --fmt` ends with on the file `path` whose reading gave
/// `text` (the files, or the texts of `onsa_cases --serve`): the text `onsa
/// fmt` would write, or its exit code and its standard error. It formats
/// with the command's function and ends as `onsa fmt` does: 2 when the file
/// cannot be read or has a syntax diagnostic, 101 on an internal error.
pub fn fmt(path: &str, text: std::io::Result<String>) -> Result<String, (u8, String)> {
    let text = text.map_err(|e| (2, format!("{}\n", onsa_cli::fmt_cannot_read(std::path::Path::new(path), &e))))?;
    let mut sources = onsa_diag::SourceMap::default();
    let file = sources.add(onsa_driver::slash_path(std::path::Path::new(path)), text);
    // The diagnostics are made inside the guard, as the command makes them: a broken span is an internal error.
    let formatted = onsa_driver::guard_on_stack(|| {
        onsa_driver::format_file(&sources, file).map(|f| match f {
            onsa_driver::Formatted::Text(out) => Ok(out),
            onsa_driver::Formatted::Syntax(d) => Err(onsa_diag::to_text(&sources, &d)),
        })
    });
    match formatted.and_then(|r| r) {
        Ok(Ok(out)) => Ok(out),
        Ok(Err(diagnostics)) => Err((2, diagnostics)),
        Err(e) => Err((101, format!("onsa: {}", e.render(&sources)))),
    }
}

/// What `onsa_cases --fix-same-place` prints for `files`, read by `read`
/// (the files, or the texts of `onsa_cases --serve`): the near "same place"
/// of each file, each on a thread with the stack of a command, in parallel.
pub fn fix_same_place(files: &[String], read: impl Fn(&str) -> Result<String, String> + Sync) -> String {
    let items = on_stacks(files.len(), |i| {
        let path = &files[i];
        match read(path) {
            Err(e) => serde_json::json!({"file": path, "unreadable": e}),
            // A panic outside the driver's stages is an internal error too.
            Ok(text) => match onsa_driver::guard(|| crate::fix_contract::same_place(&text)) {
                Ok(r) => {
                    let mut v = serde_json::json!(r);
                    v["file"] = serde_json::json!(path);
                    v
                }
                Err(e) => serde_json::json!({"file": path, "candidates": 0, "violations": [], "internal": e.message}),
            },
        }
    });
    format!("{}\n", serde_json::to_string_pretty(&items).expect("serializes"))
}

/// What `onsa_cases --fix-contract` prints for `files`, read by `read`, and
/// whether they pass: every candidate of every diagnostic of each file,
/// checked as a single-file package, applied alone and checked against the
/// contract of §18.1 as a case's are ([`crate::fix_contract::check_candidate`],
/// with no `[[test.fix]]` entry: the reported diagnostic is the only error of
/// its unit). A line per problem, `<file>:<line>:<col> <code> fix<K> `<title>`:
/// <its first line>` (a candidate that cannot be checked too; a file that cannot be
/// read or whose check ends in an internal error, `<file>: …`), then a line of
/// the counts. They pass when there is no problem and a candidate was checked.
pub fn fix_contract(files: &[String], read: impl Fn(&str) -> Result<String, String> + Sync) -> (String, bool) {
    let found = on_stacks(files.len(), |i| {
        let path = &files[i];
        match read(path) {
            Err(e) => (0, vec![format!("{path}: cannot be read: {e}")]),
            // A panic outside the driver's stages is an internal error too.
            Ok(text) => onsa_driver::guard(|| contract_lines(path, &text))
                .unwrap_or_else(|e| (0, vec![format!("{path}: internal error: {}", first_line(&e.message))])),
        }
    });
    let candidates: usize = found.iter().map(|f| f.0).sum();
    let lines: Vec<&String> = found.iter().flat_map(|f| &f.1).collect();
    let mut out: String = lines.iter().map(|l| format!("{l}\n")).collect();
    out.push_str(&format!(
        "fix-contract: {} file(s), {candidates} candidate(s), {} problem(s)\n",
        files.len(),
        lines.len()
    ));
    (out, candidates > 0 && lines.is_empty())
}

/// The candidates of the file `path` whose text is `text` ([`fix_contract`]):
/// how many, and a line per problem.
fn contract_lines(path: &str, text: &str) -> (usize, Vec<String>) {
    let run = match crate::fix_contract::check_text(text) {
        Ok(run) => run,
        Err(e) => return (0, vec![format!("{path}: the check ends in an internal error: {}", first_line(&e))]),
    };
    let (sources, ds) = (&run.loaded.sources, &run.analyzed.diagnostics);
    let (mut candidates, mut lines) = (0, Vec::new());
    for d in onsa_diag::printed_order(sources, ds).into_iter().map(|i| &ds[i]) {
        let lc = sources.file(d.span.file).line_col(d.span.start);
        for (k, fix) in d.fixes.iter().enumerate() {
            candidates += 1;
            let at = format!("{path}:{}:{} {} fix{} `{}`", lc.line, lc.col, d.code.as_str(), k + 1, fix.title());
            match crate::fix_contract::check_candidate(&run, d, fix) {
                // The first line of a problem names it; the rest renders the diagnostics.
                Ok(c) => lines.extend(c.problems.iter().map(|p| format!("{at}: {}", first_line(p)))),
                Err(e) => lines.push(format!("{at}: cannot be checked: {}", first_line(&e))),
            }
        }
    }
    (candidates, lines)
}

fn first_line(text: &str) -> &str {
    text.lines().next().unwrap_or_default()
}

/// `f` of each index below `n`, on threads with the stack of a command, in
/// parallel; the results in the order of the indexes.
pub fn on_stacks<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let out: std::sync::Mutex<Vec<Option<T>>> = std::sync::Mutex::new((0..n).map(|_| None).collect());
    let workers = std::thread::available_parallelism().map_or(4, |w| w.get()).min(n.max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            onsa_diag::stack::spawn_scoped(s, "onsa-fix", || {
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if i >= n {
                        break;
                    }
                    let v = f(i);
                    out.lock().expect("results")[i] = Some(v);
                }
            })
            .expect("spawn a worker");
        }
    });
    out.into_inner().expect("results").into_iter().map(|v| v.expect("every index ran")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `onsa_cases --fix-contract` (W5-13 U9b): a candidate that leaves an
    /// error in a unit it touches is a line, as is an unreadable file; none
    /// checked does not pass.
    #[test]
    fn the_contract_of_one_file() {
        let one = "pub fn f(a: Bool, b: Bool, c: Bool) -> Bool {\n  a && b || c\n}\n";
        let two = "pub fn f(a: Bool, b: Bool, c: Bool) -> Bool {\n  let x = a && b || c\n  a && b || x\n}\n";
        let texts = [("one.onsa", one), ("two.onsa", two), ("clean.onsa", "pub fn f() -> I32 {\n  1\n}\n")];
        let read = |p: &str| texts.iter().find(|t| t.0 == p).map(|t| t.1.to_string()).ok_or_else(|| "none".to_string());
        let run = |files: &[&str]| fix_contract(&files.iter().map(|f| f.to_string()).collect::<Vec<_>>(), read);
        assert_eq!(run(&["one.onsa"]), ("fix-contract: 1 file(s), 2 candidate(s), 0 problem(s)\n".into(), true));
        assert_eq!(run(&["clean.onsa"]), ("fix-contract: 1 file(s), 0 candidate(s), 0 problem(s)\n".into(), false));
        let (out, passed) = run(&["two.onsa", "gone.onsa"]);
        let lines: Vec<&str> = out.lines().collect();
        assert!(!passed);
        assert_eq!(lines.len(), 4, "{out}");
        for (k, title) in [(1, "(a && b) || c"), (2, "a && (b || c)")] {
            let head =
                format!("two.onsa:2:11 E0010 fix{k} `read it as `{title}``: after it, the units its edits touch");
            assert!(lines[k - 1].starts_with(&head) && lines[k - 1].contains("3:3 E0010"), "{out}");
        }
        assert_eq!(
            &lines[2..],
            ["gone.onsa: cannot be read: none", "fix-contract: 2 file(s), 2 candidate(s), 3 problem(s)"]
        );
    }
}
