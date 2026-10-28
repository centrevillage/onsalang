//! `onsa interface` reads a generic type under its arguments (R-30, R-310, W4-05 U1): the kind and
//! the size of a type that holds a generic type nested in itself (`Pair[Pair[I32]]`), and the floats
//! of a `const` of a generic struct, each in the type its argument gives.

use std::process::Command;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

const SOURCE: &str = "pub struct Pair[T] {
  a: T,
}

pub struct Outer {
  p: Pair[Pair[I32]],
}

pub struct Inner {
  p: Pair[I32],
}

pub const G: Pair[Pair[F32]] = Pair { a: Pair { a: 0.1 } }
";

#[test]
fn a_generic_type_nested_in_itself_has_its_kind_and_size() {
    let dir = std::env::temp_dir().join(format!("onsa_interface_generic_kinds_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("g.onsa");
    std::fs::write(&path, SOURCE).unwrap();
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> = text.lines().map(str::trim).filter(|l| l.starts_with("pub ")).collect();
    assert_eq!(
        lines,
        [
            "pub struct Pair[T]",
            "pub struct Outer  // Copy; size 4, align 4",
            "pub struct Inner  // Copy; size 4, align 4",
            // The F32 0.1, not the digits of the `f64` that holds it.
            "pub const G: Pair[Pair[F32]] = Pair { a: Pair { a: 0.1 } }",
        ]
    );
}
