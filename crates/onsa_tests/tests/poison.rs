//! `panic = "poison"` end to end (T4-4, spec §9.2): a panic inside `process`
//! returns 1 with zeroed outputs, the instance stays poisoned until `reset`,
//! and an exported function that panics returns zero and reports it through
//! `onsa_take_panic`. Skipped without a host `cc`.

use std::process::Command;

const SRC: &str = r#"
pub flow boom(
  x: Sig[F32],
  @param(min: 0.0, max: 10000000000.0, default: 1.0)
  k: Ctl[F32],
) -> Sig[F32] {
  let n = k.trunc_u32()
  x * n.round_f32()
}

pub fn checked(a: I32, b: I32) -> I32 {
  a + b
}

/// `init` panics when `n` overflows (S-27): the instance stays uninitialized.
pub flow fragile(x: Sig[F32], n: Init[I32]) -> Sig[F32] {
  let m = n + 1
  x * m.round_f32()
}
"#;

const MANIFEST: &str = r#"
[package]
name = "poison"
edition = "2026"

[export]
prefix = "onsa_"
flows = ["poison.boom", "poison.fragile"]
fns = ["poison.checked"]

[targets.host]
kind = "source"
lang = "c"
platform = "host"
panic = "poison"
provides = []
"#;

const DRIVER: &str = r#"
#include "onsa_boom.h"
#include "onsa_fragile.h"
#include "onsa_poison.h"
#include <stdio.h>
static float in[64], out[64];
int main(void) {
  static unsigned char mem[ONSA_BOOM_SIZE] __attribute__((aligned(ONSA_BOOM_ALIGN)));
  onsa_boom* s = (onsa_boom*)mem;
  onsa_boom_params p;
  onsa_boom_init(s, NULL, 48000.0f);
  for (int i = 0; i < 64; i++) in[i] = 1.0f;
  p.k = 2.0f;
  printf("%d ", onsa_boom_process(s, &p, in, out, 64));          /* 0 */
  printf("%g ", out[5]);                                           /* 2 */
  p.k = 1e10f;                                                     /* trunc_u32 panics */
  printf("%d ", onsa_boom_process(s, &p, in, out, 64));          /* 1 */
  printf("%g ", out[5]);                                           /* 0 (zeroed) */
  p.k = 2.0f;
  printf("%d ", onsa_boom_process(s, &p, in, out, 64));          /* 1 (still poisoned) */
  onsa_boom_reset(s);
  printf("%d ", onsa_boom_process(s, &p, in, out, 64));          /* 0 */
  printf("%g ", out[5]);                                           /* 2 */
  printf("%d ", onsa_checked(1, 2));                               /* 3 */
  printf("%d ", onsa_take_panic());                                /* 0 */
  printf("%d ", onsa_checked(2147483647, 1));                      /* 0 (panicked) */
  printf("%d ", onsa_take_panic());                                /* 1 */
  /* S-27: a panic inside init */
  static unsigned char fmem[ONSA_FRAGILE_SIZE] __attribute__((aligned(ONSA_FRAGILE_ALIGN)));
  onsa_fragile* f = (onsa_fragile*)fmem;
  onsa_fragile_params fp;
  memset(&fp, 0, sizeof fp);
  printf("%d ", onsa_fragile_init(f, NULL, 2147483647, 48000.0f));  /* 1 (n + 1 overflows) */
  printf("%d ", onsa_fragile_process(f, &fp, in, out, 64));          /* 1 (uninitialized) */
  onsa_fragile_reset(f);
  printf("%d ", onsa_fragile_process(f, &fp, in, out, 64));          /* 1 (reset did nothing) */
  printf("%d ", onsa_fragile_init(f, NULL, 2, 48000.0f));            /* 0 */
  printf("%d ", onsa_fragile_process(f, &fp, in, out, 64));          /* 0 */
  printf("%g\n", out[5]);                                           /* 3 */
  return 0;
}
"#;

#[test]
fn poison_wrappers_recover_from_panics() {
    if Command::new("cc").arg("--version").output().is_err() {
        eprintln!("no `cc` on the PATH; skipping");
        return;
    }
    let dir = std::env::temp_dir().join(format!("onsa_poison_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // The build's own entry (R-89 (3)), with the manifest as a value.
    let (manifest, _) = onsa_driver::Manifest::parse(MANIFEST, &[]).unwrap();
    let input = onsa_driver::PackageInput {
        manifest: Some(manifest),
        files: vec![onsa_driver::SourceFile { path: "poison.onsa".into(), text: SRC.into() }],
        root: None,
    };
    let mut loaded = onsa_driver::Loaded::from_input(input);
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    let unit = match onsa_driver::build_analyzed(&loaded, &analyzed, "host") {
        Ok(out) => out.unit,
        Err(onsa_driver::BuildError::Usage(m)) => panic!("{m}"),
        Err(onsa_driver::BuildError::Diagnostics { sources, diagnostics }) => {
            panic!("{}", onsa_diag::to_text(&sources, &diagnostics))
        }
        Err(onsa_driver::BuildError::Verify(v)) => panic!("{}", v.report()),
    };
    std::fs::write(dir.join("onsa.h"), &unit.runtime_header).unwrap();
    for (h, t) in &unit.headers {
        std::fs::write(dir.join(h), t).unwrap();
    }
    std::fs::write(dir.join("unit.c"), &unit.source).unwrap();
    std::fs::write(dir.join("driver.c"), DRIVER).unwrap();
    let exe = dir.join("run");
    let out = Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-ffp-contract=off", "-fno-fast-math"])
        .arg("-I")
        .arg(&dir)
        .arg(dir.join("unit.c"))
        .arg(dir.join("driver.c"))
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(out.status.success(), "cc failed:\n{}", String::from_utf8_lossy(&out.stderr));
    let run = Command::new(&exe).output().unwrap();
    assert!(run.status.success(), "driver failed with {}", run.status);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "0 2 1 0 1 0 2 3 0 0 1 1 1 1 0 0 3");
}
