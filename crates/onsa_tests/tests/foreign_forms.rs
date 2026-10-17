//! The closed list of the forms of other languages against the compiler's
//! table, with the list of things pending (`onsa_tests::foreign_forms`, W3-15).
//! `UPDATE_GOLDEN=1` rewrites the `fixed` texts that differ (copies, Q-04, X-3).

#[test]
fn foreign_forms() {
    let report = onsa_tests::foreign_forms::check(&onsa_tests::case::repo_root());
    println!(
        "{} rows, {} examples, {} `fixed` texts compared; pending: {}",
        report.rows,
        report.examples,
        report.copies,
        if report.pending.is_empty() { "none".to_string() } else { report.pending.join(", ") }
    );
    if !report.rewritten.is_empty() {
        println!("rewritten by UPDATE_GOLDEN=1 ({}): {}", report.rewritten.len(), report.rewritten.join(", "));
    }
    let failures: Vec<&String> = report.failures.iter().chain(&report.copy_failures).collect();
    assert!(failures.is_empty(), "{}", failures.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
}
