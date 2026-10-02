//! Golden tests of the Core dump (T3-2, T3-5): `tests/golden/core/<name>.core` is
//! the expected `onsa dump --core` of a source file. `UPDATE_GOLDEN=1`
//! rewrites the expectations.

use std::path::{Path, PathBuf};

const CASES: &[(&str, &str)] = &[
    ("tests/spec/examples/gcd.onsa", "gcd"),
    ("tests/spec/fn/methods.onsa", "methods"),
    ("tests/spec/rt/soft_clip.onsa", "soft_clip"),
    ("tests/spec/types/generics.onsa", "generics"),
    ("tests/golden/core/generics_use.onsa", "generics_use"),
    ("tests/golden/core/resonator.onsa", "resonator"),
    ("tests/golden/core/echo.onsa", "echo"),
    ("tests/spec/examples/voice.onsa", "voice"),
    ("tests/spec/flow/unison.onsa", "unison"),
];

#[test]
fn core_dumps_match_goldens() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let update = std::env::var("UPDATE_GOLDEN").is_ok();
    let mut failures = Vec::new();
    for (src, name) in CASES {
        let path: PathBuf = root.join(src);
        let mut loaded = onsa_driver::load(std::slice::from_ref(&path)).unwrap_or_else(|e| panic!("{src}: {e}"));
        let analyzed = onsa_driver::analyze_loaded(&mut loaded);
        assert!(
            analyzed.diagnostics.is_empty(),
            "{src}: check diagnostics:\n{}",
            onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics)
        );
        let module = match onsa_driver::lower_core(&analyzed) {
            Ok(m) => m,
            Err(d) => panic!("{src}: lowering diagnostics:\n{}", onsa_diag::to_text(&loaded.sources, &d)),
        };
        onsa_core::verify(&module).unwrap_or_else(|e| panic!("{src}: {e}"));
        let actual = onsa_core::dump(&module);
        let golden = root.join("tests/golden/core").join(format!("{name}.core"));
        if update {
            std::fs::write(&golden, &actual).unwrap();
            continue;
        }
        let expected = std::fs::read_to_string(&golden).unwrap_or_default();
        if expected != actual {
            failures.push(format!("{}: differs from {} (run with UPDATE_GOLDEN=1 to accept)", src, golden.display()));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
