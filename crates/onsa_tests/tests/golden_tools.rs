//! Golden tests of `onsa interface` (T3-11) and `onsa graph` (T3-12):
//! `tests/golden/interface/<name>.txt` and `tests/golden/graph/<name>.dot`.
//! `UPDATE_GOLDEN=1` rewrites the expectations.

use std::path::Path;

fn analyzed(root: &Path, src: &str) -> (onsa_driver::Loaded, onsa_driver::Analyzed) {
    let path = root.join(src);
    let mut loaded = onsa_driver::load(std::slice::from_ref(&path)).unwrap_or_else(|e| panic!("{src}: {e}"));
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    assert!(
        analyzed.diagnostics.is_empty(),
        "{src}: check diagnostics:\n{}",
        onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics)
    );
    (loaded, analyzed)
}

fn compare(root: &Path, golden: &str, actual: &str, failures: &mut Vec<String>) {
    let golden = root.join(golden);
    if std::env::var("UPDATE_GOLDEN").is_ok() {
        std::fs::create_dir_all(golden.parent().unwrap()).unwrap();
        std::fs::write(&golden, actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&golden).unwrap_or_default();
    if expected != actual {
        failures.push(format!("{} differs (run with UPDATE_GOLDEN=1 to accept)", golden.display()));
    }
}

#[test]
fn interface_and_graph_match_goldens() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut failures = Vec::new();
    let (_l, a) = analyzed(&root, "tests/spec/examples/voice.onsa");
    let iface = onsa_driver::interface(&a);
    compare(&root, "tests/golden/interface/voice.txt", &onsa_driver::render_text(&iface), &mut failures);
    // The JSON form must parse and keep the same package name.
    let json: serde_json::Value = serde_json::from_str(&onsa_driver::render_json(&iface)).unwrap();
    assert_eq!(json["package"], "voice");
    let dot = onsa_driver::graph(&a, "voice").unwrap();
    compare(&root, "tests/golden/graph/voice.dot", &dot, &mut failures);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
