//! Runs every file under `tests/spec` (repository root) against the driver.

use std::path::Path;

#[test]
fn spec_files() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/spec");
    let files = onsa_tests::collect(&dir);
    assert!(!files.is_empty(), "no .onsa files under {}", dir.display());
    let failures: Vec<String> = files.iter().filter_map(onsa_tests::run_unit).collect();
    if !failures.is_empty() {
        panic!("{} of {} spec files failed:\n{}", failures.len(), files.len(), failures.join("\n"));
    }
}
