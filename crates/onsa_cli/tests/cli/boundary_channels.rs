//! S-1110, S-407 (§11.6, decided 2026-11-16, W7-12 U2a): a `sample` input or output has at least one channel, so
//! that an array of length 0 and a struct with no field are E0810 at the type of the heading. The case file
//! `negative/flow_boundary_zero_channels.onsa` pins the codes; this file asks what the messages tell, in words,
//! as the case markers do not compare them: a struct with no field, an array of length 0 (also as a field of the
//! struct of the output), and the length a `const` gives, by its value. None has a candidate. The nested array
//! keeps its own message.

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, str_of};
use onsa_driver::PackageInput;
use serde_json::Value;

const DECLS: &str = "pub struct Empty {}\n\npub struct Part {\n  l: F32,\n  e: [F32; 0],\n}\n\nconst NONE: U32 = 0\n\n";

/// The one diagnostic of the program, as `onsa check --json` prints it.
fn one_of(tail: &str) -> Value {
    let out = check_input_out(&PackageInput::single_file("main.onsa", format!("{DECLS}{tail}")));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}", out.code, out.stderr);
    match diagnostics(&doc_of(&out)).as_slice() {
        [d] => d.clone(),
        ds => panic!("want one diagnostic of {tail:?}: {ds:?}"),
    }
}

#[test]
fn the_e0810_of_no_channel_tells_why() {
    let forms = [
        ("pub flow f(x: F32 at sample) -> Empty at sample {\n  Empty {}\n}\n", &["`Empty`", "no field"][..]),
        ("pub flow f() -> [F32; 0] at sample {\n  []\n}\n", &["`[F32; 0]`", "length 0"]),
        ("pub flow f(x: [F32; 0] at sample) -> F32 at sample {\n  1.0\n}\n", &["`[F32; 0]`", "length 0"]),
        ("pub flow f(x: F32 at sample) -> Part at sample {\n  Part { l: x, e: [] }\n}\n", &["`e`", "length 0"]),
        ("pub flow f(x: F32 at sample) -> [F32; NONE] at sample {\n  []\n}\n", &["`[F32; 0]`", "length 0"]),
    ];
    for (tail, words) in forms {
        let d = one_of(tail);
        let message = str_of(&d, "message");
        assert_eq!(code_of(&d), "E0810", "{tail}: {message}");
        assert!(words.iter().all(|w| message.contains(w)), "{tail}: want {words:?} in {message}");
        assert!(message.contains("channel") && !message.contains("nested"), "{tail}: {message}");
        assert!(d["fixes"].as_array().is_none_or(Vec::is_empty), "{tail}: a candidate: {d}");
    }
    let nested = one_of("pub flow f(x: F32 at sample) -> [[F32; 2]; 2] at sample {\n  [[x, x], [x, x]]\n}\n");
    assert!(str_of(&nested, "message").contains("nested"), "{nested}");
}
