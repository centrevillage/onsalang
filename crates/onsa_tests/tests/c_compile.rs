//! Compile the generated C with the host compiler (T4-2 acceptance): every
//! golden case must build with `-std=c11 -Wall -Wextra -Werror`. Skipped when
//! no `cc` is on the PATH.

use std::path::Path;
use std::process::Command;

use onsa_backend_c::PanicMode;
use onsa_tests::c::emit_c_with;

const CASES: &[(&str, &str, Option<u32>, bool, PanicMode)] = &[
    ("tests/golden/core/resonator.onsa", "resonator", None, false, PanicMode::Trap),
    ("tests/spec/examples/voice.onsa", "voice", None, true, PanicMode::Trap),
    ("tests/golden/core/echo.onsa", "echo", Some(4096), false, PanicMode::Trap),
    ("tests/spec/flow/unison.onsa", "unison", None, false, PanicMode::Trap),
    ("tests/golden/core/echo.onsa", "echo_poison", Some(4096), true, PanicMode::Poison),
    ("tests/spec/examples/voice.onsa", "voice_poison", None, false, PanicMode::Poison),
];

#[test]
fn generated_c_compiles() {
    if Command::new("cc").arg("--version").output().is_err() {
        eprintln!("no `cc` on the PATH; skipping the C compile check");
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let dir = std::env::temp_dir().join(format!("onsa_c_compile_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut failures = Vec::new();
    for (src, name, bulk, alloc, panic) in CASES {
        let unit = emit_c_with(&root, src, *bulk, *alloc, *panic);
        let case = dir.join(name);
        std::fs::create_dir_all(&case).unwrap();
        std::fs::write(case.join("onsa.h"), &unit.runtime_header).unwrap();
        for (hname, text) in &unit.headers {
            std::fs::write(case.join(hname), text).unwrap();
        }
        let c_path = case.join(format!("onsa_{name}.c"));
        std::fs::write(&c_path, &unit.source).unwrap();
        let out = Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-ffp-contract=off", "-fno-fast-math", "-c"])
            .arg(&c_path)
            .arg("-o")
            .arg(case.join("out.o"))
            .output()
            .unwrap();
        if !out.status.success() {
            failures.push(format!("{name}: cc failed:\n{}", String::from_utf8_lossy(&out.stderr)));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
