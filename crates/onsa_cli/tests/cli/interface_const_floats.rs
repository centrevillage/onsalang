//! The floats of a `const` in `onsa interface` (§18.2): each value is shown in its type, as the
//! numbers of `@param` are, the shortest decimal that reads as it (`F32` 0.1 is `0.1`, not the digits
//! of the `f64` that holds the `F32` value), through arrays, tuples and structs (W3-05), each
//! written as in the source (`P { a: 0.1, b: 0.1 }`).

use crate::test_support::{Dir, ONSA};
use std::process::Command;

const SOURCE: &str = "pub struct P {
  a: F32,
  b: F64,
}

pub const K: F32 = 0.1
pub const A: [F32; 2] = [0.1, 1.00000005960464477539062501]
pub const S: P = P { a: 0.1, b: 0.1 }
pub const T: (F32, F64) = (0.3, 0.3)
pub const D: F64 = 0.1
";

#[test]
fn the_floats_of_a_const_are_shown_in_their_type() {
    let dir = Dir::bare("interface_const_floats");
    let path = dir.0.join("c.onsa");
    std::fs::write(&path, SOURCE).unwrap();
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let consts: Vec<&str> = text.lines().map(str::trim).filter(|l| l.starts_with("pub const ")).collect();
    assert_eq!(
        consts,
        [
            "pub const K: F32 = 0.1",
            // The F32 value next above 1 (the literal rounds up to it once, R-20).
            "pub const A: [F32; 2] = [0.1, 1.0000001]",
            "pub const S: P = P { a: 0.1, b: 0.1 }",
            "pub const T: (F32, F64) = (0.3, 0.3)",
            "pub const D: F64 = 0.1",
        ]
    );
}
