//! Shared helpers for the C of a build: the golden form of the headers and
//! the compile check with the host compiler (T4-2).

use std::path::Path;
use std::process::Command;
use std::sync::OnceLock;

use onsa_backend_c::CUnit;

/// `onsa_voice.h` etc. joined into one golden file.
pub fn join_headers(unit: &CUnit) -> String {
    let mut s = String::new();
    for (name, text) in &unit.headers {
        s.push_str(&format!("/* ==== {name} ==== */\n"));
        s.push_str(text);
    }
    s
}

/// Whether `cc` is on the PATH (asked once).
pub fn has_cc() -> bool {
    static CC: OnceLock<bool> = OnceLock::new();
    *CC.get_or_init(|| Command::new("cc").arg("--version").output().is_ok())
}

/// The flags every compile of generated C uses.
pub const CFLAGS: &[&str] = &["-std=c11", "-Wall", "-Wextra", "-Werror", "-ffp-contract=off", "-fno-fast-math"];

/// Write the files of a build into `dir`.
pub fn write_files(dir: &Path, files: &[(String, String)]) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    for (name, text) in files {
        std::fs::write(dir.join(name), text).map_err(|e| format!("cannot write {name}: {e}"))?;
    }
    Ok(())
}

/// Compile the C source of a build to an object in `dir` (the files must be written there).
pub fn compile_object(dir: &Path, source_name: &str) -> Result<(), String> {
    let out = Command::new("cc")
        .args(CFLAGS)
        .arg("-c")
        .arg(dir.join(source_name))
        .arg("-I")
        .arg(dir)
        .arg("-o")
        .arg(dir.join("out.o"))
        .output()
        .map_err(|e| format!("cannot run cc: {e}"))?;
    if !out.status.success() {
        return Err(format!("cc failed:\n{}", String::from_utf8_lossy(&out.stderr)));
    }
    Ok(())
}
