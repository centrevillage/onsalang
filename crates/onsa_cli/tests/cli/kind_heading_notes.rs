//! The note of the E0020 of a type that claims `Copy` (`struct W: Copy`, `impl Copy for W`, §4.6, §6.4): it
//! names the first field that is not Copy. A field whose type has a part that was not read (an E0416 of its
//! own) is not Copy when a part that was read is not (§18.1, S-1067 (2), W6-04 U16): `E1 { s: Str, e: <error> }`
//! is named as `E1 { s: Str, e: I32 }` is. The case files cannot pin it (the runner of the cases compares no
//! note), and the spec does not fix the text of a note, so the test asks the line the note points at.

use crate::test_support::sweep::check_input_out;
use crate::test_support::{code_of, diagnostics, doc_of, notes_of, span_of};
use onsa_driver::PackageInput;
use serde_json::Value;

/// The diagnostics of the program (the document `onsa check --json` prints).
fn diagnostics_of(text: &str) -> Vec<Value> {
    let out = check_input_out(&PackageInput::single_file("main.onsa", text));
    assert!(out.code == 0 || out.code == 1, "the command ended with {}: {}", out.code, out.stderr);
    diagnostics(&doc_of(&out)).clone()
}

#[test]
fn a_field_not_copy_by_the_parts_read_is_named_by_the_note_of_a_copy_heading() {
    // Line 1 is `E1`, line 3 the field `x` of `W`; the E0020 is at the heading or at the `impl`.
    let fields = ["e: Buf[Str]", "e: I32"];
    let claims = [
        ("pub struct W: Copy {\n  x: E1,\n  n: I32,\n}\n", 2),
        ("pub struct W {\n  x: E1,\n  n: I32,\n}\nimpl Copy for W {}\n", 6),
    ];
    let mut checked = 0;
    for field in fields {
        for (claim, at) in claims {
            let text = format!("pub struct E1 {{ s: Str, {field} }}\n{claim}");
            let diags = diagnostics_of(&text);
            let e0020: Vec<&Value> = diags.iter().filter(|d| code_of(d) == "E0020").collect();
            assert_eq!(e0020.len(), 1, "{text}: {diags:?}");
            assert_eq!(span_of(&e0020[0]["span"]).line, at, "{text}");
            let lines: Vec<u64> =
                notes_of(e0020[0]).iter().filter_map(|n| n.get("span")).map(|s| span_of(s).line).collect();
            assert!(lines.contains(&3), "{text}: the note does not point at the field `x`: {}", e0020[0]);
            checked += 1;
        }
    }
    assert_eq!(checked, 4);
}
