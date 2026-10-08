//! The closed list of the forms of other languages against the compiler's
//! table, with the list of things pending (`onsa_tests::foreign_forms`, W3-15).

#[test]
fn foreign_forms() {
    let report = onsa_tests::foreign_forms::check(&onsa_tests::case::repo_root());
    println!(
        "{} rows, {} examples; pending: {}",
        report.rows,
        report.examples,
        if report.pending.is_empty() { "none".to_string() } else { report.pending.join(", ") }
    );
    assert!(report.failures.is_empty(), "{}", report.failures.join("\n"));
}
