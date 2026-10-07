//! The §17.5 example end to end (T4-8): `onsa build --target host` on
//! `examples/voice_host`, then the C host is compiled against the library,
//! run, and its WAV checked. Fails without a host `cc` (Q-07: nothing is
//! skipped silently).

use std::path::Path;
use std::process::Command;

#[test]
fn voice_host_writes_a_wav() {
    onsa_tests::c::require("cc").unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let example = root.join("examples/voice_host");
    let dir = onsa_tests::c::scratch_dir("onsa_test", "example_host");
    std::fs::create_dir_all(&dir).unwrap();
    let opts = onsa_driver::BuildOptions { target: "host".into(), out: Some(dir.join("lib")) };
    let report = match onsa_driver::build(&example, &opts) {
        Ok(r) => r,
        Err(onsa_driver::BuildError::Usage(m)) => panic!("build: {m}"),
        Err(onsa_driver::BuildError::Diagnostics { sources, diagnostics }) => {
            panic!("build: {}", onsa_diag::to_text(&sources, &diagnostics))
        }
        Err(onsa_driver::BuildError::Internal { sources, error }) => panic!("build: {}", error.render(&sources)),
    };
    assert_eq!(report.archive.as_deref(), Some("libonsa_voice.a"), "{report:?}");
    assert!(report.files.iter().any(|f| f == "onsa_voice.h"));
    let exe = dir.join("voice_host");
    let out = Command::new("cc")
        .args(onsa_tests::c::CFLAGS)
        .arg("-O2")
        .arg(example.join("host.c"))
        .arg("-I")
        .arg(dir.join("lib"))
        .arg("-L")
        .arg(dir.join("lib"))
        .arg("-lonsa_voice")
        .arg("-lm")
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(out.status.success(), "cc host.c failed:\n{}", String::from_utf8_lossy(&out.stderr));
    let run = Command::new(&exe).current_dir(&dir).output().unwrap();
    assert!(run.status.success(), "voice_host failed with {}", run.status);
    let wav = std::fs::read(dir.join("out.wav")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(&wav[0..4], b"RIFF");
    assert_eq!(&wav[8..12], b"WAVE");
    let rate = u32::from_le_bytes([wav[24], wav[25], wav[26], wav[27]]);
    assert_eq!(rate, 48000);
    let data = u32::from_le_bytes([wav[40], wav[41], wav[42], wav[43]]);
    assert_eq!(data, 96000);
    let samples: Vec<i16> = wav[44..].chunks_exact(2).map(|b| i16::from_le_bytes([b[0], b[1]])).collect();
    assert_eq!(samples.len(), 48000);
    let peak = samples.iter().map(|s| s.unsigned_abs()).max().unwrap();
    assert!(peak > 1000, "the voice is silent (peak {peak})");
}
