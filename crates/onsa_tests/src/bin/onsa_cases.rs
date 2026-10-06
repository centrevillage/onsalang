//! `onsa_cases`: the cases under `tests/` and their settings as JSON, for the
//! gate's tools (`tools/spec_sections.py`). Reads the fragments with the same
//! code as the test runner; exits 1 when a case cannot be read.
//!
//! ```text
//! [{"path": "tests/spec/fn/mean.onsa", "kind": "file", "name": "mean",
//!   "mode": "check", "spec": ["§6.1"], "golden": [], "golden_graph": [],
//!   "conformance": false, "targets": []}, ...]
//! ```

use std::process::ExitCode;

fn main() -> ExitCode {
    let root = match std::env::args().nth(1) {
        Some(r) => std::path::PathBuf::from(r),
        None => onsa_tests::case::repo_root(),
    };
    let mut items = Vec::new();
    let mut failed = false;
    let (cases, errors) = onsa_tests::case::collect(&root);
    for e in &errors {
        eprintln!("{e}");
        failed = true;
    }
    for c in cases {
        match &c.setup {
            Ok(s) => items.push(serde_json::json!({
                "path": c.path,
                "kind": c.kind,
                "name": c.name,
                "mode": s.test.mode,
                "spec": s.test.spec,
                "golden": s.test.golden,
                "golden_graph": s.test.golden_graph,
                "conformance": s.test.conformance,
                "targets": s.targets(),
            })),
            Err(e) => {
                eprintln!("{}: {e}", c.path);
                failed = true;
            }
        }
    }
    println!("{}", serde_json::to_string_pretty(&items).expect("serializes"));
    if failed { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}
