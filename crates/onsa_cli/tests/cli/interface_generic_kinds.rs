//! `onsa interface` reads a generic type under its arguments (R-30, R-310, W4-05 U1): the kind and
//! the size of a type that holds a generic type nested in itself (`Pair[Pair[I32]]`), and the floats
//! of a `const` of a generic struct, each in the type its argument gives; and the type of a constant
//! of a generic `impl` by the names of its parameters (§15.1, R-375).

use crate::test_support::{Dir, ONSA};
use std::process::Command;

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
    let dir = Dir::bare("interface_generic_kinds");
    let path = dir.0.join("g.onsa");
    std::fs::write(&path, SOURCE).unwrap();
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
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

/// R-375: `Option[T]` as the method beside it has it, not the parameter's
/// number (`Option[<0>]`).
#[test]
fn a_constant_of_a_generic_impl_names_its_type_parameters() {
    let dir = Dir::bare("interface_generic_impl_const");
    let path = dir.0.join("w.onsa");
    let source = "pub struct W[T, const N: U32] {
  a: [T; N],
}

impl[T: Copy, const N: U32] W[T, N] {
  pub const NONE: Option[T] = None
  pub fn f(self) -> Option[T] {
    None
  }
}
";
    std::fs::write(&path, source).unwrap();
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> =
        text.lines().map(str::trim).filter(|l| l.starts_with("pub ") || l.starts_with("impl")).collect();
    assert_eq!(
        lines,
        [
            "pub struct W[T, const N: U32]",
            "impl[T: Copy, const N: U32] W[T, N]",
            "pub const NONE: Option[T]",
            "pub fn f(self) -> Option[T]",
        ]
    );
}
