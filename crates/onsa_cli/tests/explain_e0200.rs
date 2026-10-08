//! `onsa explain E0200` lists what this version does not support (spec §18.1,
//! S-224, W2-07): every feature of `onsa_diag::unsupported`, the list every
//! E0200 comes from, once.

use std::process::Command;

use onsa_diag::unsupported::{Feature, list_line};

#[test]
fn explain_e0200_lists_every_unsupported_feature() {
    let out = Command::new(env!("CARGO_BIN_EXE_onsa")).args(["explain", "E0200"]).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).expect("UTF-8 output");
    assert!(text.starts_with("# E0200: "), "{text}");
    assert!(!text.contains("No long explanation"), "{text}");
    assert!(!Feature::ALL.is_empty());
    for &f in Feature::ALL {
        let line = list_line(f);
        assert_eq!(text.lines().filter(|l| *l == line).count(), 1, "{line}\n---\n{text}");
    }
    for want in ["the value of a `match`", "`?` inside an anonymous function", "`return` inside an anonymous function"]
    {
        assert!(text.contains(want), "{want}\n---\n{text}");
    }
}

/// An E0200 of lowering names the offending source (`found`, §18.1) and
/// carries the form this version accepts as a note.
#[test]
fn a_lowering_e0200_has_found_and_a_note() {
    let dir = std::env::temp_dir().join(format!("onsa_e0200_found_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("m.onsa");
    std::fs::write(
        &file,
        "pub fn f(n: I32) -> I32 {\n  match n { 1 => 10, _ => 20 }\n}\n\ntest \"t\" {\n  assert f(1) == 10\n}\n",
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_onsa"))
        .args(["test", "--json", file.to_str().unwrap()])
        .output()
        .expect("run onsa");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("JSON");
    let d = &v[0];
    assert_eq!(d["code"], "E0200", "{v}");
    assert_eq!(d["found"], "match n { 1 => 10, _ => 20 }", "{v}");
    assert_eq!(d["notes"].as_array().map(Vec::len), Some(1), "{v}");
}
