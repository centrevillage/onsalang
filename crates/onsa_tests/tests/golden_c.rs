//! Golden tests of the C backend (T4-2, T4-3): `tests/golden/c/<name>.c` and
//! `<name>.h` (all headers of the unit, concatenated). `UPDATE_GOLDEN=1`
//! rewrites the expectations.

use std::path::Path;

use onsa_backend_c::PanicMode;
use onsa_tests::c::{emit_c_with, join_headers};

/// `(source, golden name, bulk_threshold, provides_alloc, panic)`
pub const CASES: &[(&str, &str, Option<u32>, bool, PanicMode)] = &[
    ("tests/golden/core/resonator.onsa", "resonator", None, false, PanicMode::Trap),
    ("tests/spec/examples/voice.onsa", "voice", None, true, PanicMode::Trap),
    ("tests/golden/core/echo.onsa", "echo", Some(4096), false, PanicMode::Trap),
    ("tests/spec/flow/unison.onsa", "unison", None, false, PanicMode::Trap),
    // T4-4: `panic = "poison"` adds the jmp_buf field, the setjmp wrappers and the S-26 size macros.
    ("tests/golden/core/echo.onsa", "echo_poison", Some(4096), true, PanicMode::Poison),
];

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
fn c_output_matches_goldens() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut failures = Vec::new();
    for (src, name, bulk, alloc, panic) in CASES {
        let unit = emit_c_with(&root, src, *bulk, *alloc, *panic);
        compare(&root, &format!("tests/golden/c/{name}.c"), &unit.source, &mut failures);
        compare(&root, &format!("tests/golden/c/{name}.h"), &join_headers(&unit), &mut failures);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
