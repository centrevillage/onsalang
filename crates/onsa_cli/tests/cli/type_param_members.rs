//! The E0302 of a name after a type parameter and a `.` in a heading and a type (spec §15.1; R-370;
//! W5-11 U10a/i).
//!
//! What is checked: a member that the bounds of the type parameter do not give is the name not found, in
//! the message and at the place, in the three places that are no body (a type `-> T.K`, a bound `U: T.x`,
//! an effect row `uses {T.e}`) and in the type of a local of a body, as it is in a body (`T.f()`). The type
//! parameter itself is found, so no message says it is not. The text of a message is not promised by the
//! spec (§18.1): this holds the one of the implementation, which names what was not found.

use crate::test_support;

use test_support::sweep::{Texts, check_input, ended_well, input_of};

/// A function of `main.onsa`, and the line in it (from 1), the name and the column (from 1) of its E0302.
const CASES: [(&str, u64, &str, u64); 5] = [
    ("fn a[T](x: T) -> T.K {\n  x\n}\n", 1, "K", 20),
    ("fn b[T, U: T.x](x: U) -> U {\n  x\n}\n", 1, "x", 14),
    ("fn c[T](x: T) -> U32 uses {T.e} {\n  1\n}\n", 1, "e", 30),
    ("fn d[T: Float](x: T) -> T.NOPE {\n  x\n}\n", 1, "NOPE", 27),
    ("fn e[T](x: T) {\n  let y: T.K = x\n}\n", 2, "K", 12),
];

#[test]
fn a_member_the_bounds_do_not_give_is_the_name_not_found() {
    let (mut text, mut want) = (String::new(), Vec::new());
    for (src, line, name, col) in CASES {
        want.push((text.lines().count() as u64 + line, format!("E0302 cannot find `{name}`"), col));
        text.push_str(src);
    }
    let mut texts = Texts::new();
    texts.insert("main.onsa".to_string(), text.clone());
    let checked = check_input(&input_of("demo", &texts));
    assert!(ended_well(&checked), "check did not end as a check does:\n{}", checked.stderr);
    let got: Vec<(u64, String, u64)> =
        checked.diags.iter().map(|d| (d.line, format!("{} {}", d.code, d.message), d.col)).collect();
    assert_eq!(got, want, "in:\n{text}");
}
