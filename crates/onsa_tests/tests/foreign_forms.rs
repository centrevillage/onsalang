//! The closed list of the forms of other languages against the compiler's
//! table, with the list of things pending (`onsa_tests::foreign_forms`, W3-15).
//! `UPDATE_GOLDEN=1` rewrites the `fixed` texts that differ (copies, Q-04, X-3),
//! but those the guard refuses; `UPDATE_GOLDEN=worse` rewrites those too.

#[test]
fn foreign_forms() {
    let update = onsa_tests::golden::Update::from_env();
    let report = onsa_tests::foreign_forms::check(&onsa_tests::case::repo_root(), update);
    println!(
        "{} rows, {} examples, {} `fixed` texts compared; not judged (listed rows): {}; pending: {}",
        report.rows,
        report.examples,
        report.copies,
        report.unjudged_copies,
        if report.pending.is_empty() { "none".to_string() } else { report.pending.join(", ") }
    );
    if !report.rewritten.is_empty() {
        println!("rewritten by UPDATE_GOLDEN=1 ({}): {}", report.rewritten.len(), report.rewritten.join(", "));
    }
    if !report.forced.is_empty() {
        println!(
            "rewritten over the guard by UPDATE_GOLDEN=worse ({}): {}",
            report.forced.len(),
            report.forced.join(", ")
        );
    }
    let failures: Vec<&String> = report.failures.iter().chain(&report.copy_failures).collect();
    assert!(failures.is_empty(), "{}", failures.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
}
