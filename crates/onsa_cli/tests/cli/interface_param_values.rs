//! The values of `@param` in `onsa interface` (spec §18.2, §11.7; S-87 (2), S-1120 (provisional (2)), R-487; W7-13 U4b/t).
//!
//! What the spec fixes, and so what is checked:
//! - §11.7: the value of a key is a value of the value type of the input (a text key's is a `Str`) and `onsa interface` does not show
//!   the keys that are not written. S-87 (2) and S-1120 (the reading of the parent, provisional): the interface shows the value that
//!   the key has, in the form of the type of the input: the integers and `Bool` of an input are shown as they are written
//!   (`min: 0, max: 10, default: 2` for an `I32`, `default: true` for a `Bool`), as a float is for `F32` and `F64` (`min: -60.0`).
//!   The keys are written here as plain literals in the order of the list of §11.7, so that the form that the line takes does not
//!   depend on how the shown value is chosen (the text written or the value evaluated, S-1120): the shown line is the same.
//! - §2.4 and §11.7 (R-487): a text key is shown as a literal of Onsa that reads as the value it has (a `"`, a `\`, a newline, a `{`
//!   and a `}` in it are escaped so that the literal reads back to the same text), in one line of the output.
//! - the JSON (`--json`) is not fixed by the spec as a whole; what is checked is only what S-87 asks of the values of `@param` in it: the
//!   value of an integer input is an integer and not a float, the value of a `Bool` input is a boolean, and a float input has a float.
//!   The attribute is the `param` object of the input in the JSON as it is today.
//!
//! Not asked: the rest of the text of a line, the other keys of the JSON, and what `interface` shows of a value that is not a literal
//! (the values that are names are E0200 until W9-03).

use crate::test_support::{Dir, ONSA};
use serde_json::Value;
use std::process::Command;

const SOURCE: &str = "\
pub flow mix(
  x: F32 at sample,
  @param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\")
  level: F32 at block,
  @param(min: 0.0, max: 4.0, default: 0.1, step: 0.5)
  wide: F64 at block,
  @param(min: 0, max: 10, default: 2, step: 1, unit: \"n\", id: \"steps\")
  steps: I32 at block,
  @param(min: -128, max: 127, default: -1)
  small: I8 at block,
  @param(min: -32768, max: 32767, default: 0, label: \"Offset\")
  offset: I16 at block,
  @param(min: 0, max: 255, default: 128)
  byte: U8 at block,
  @param(min: 0, max: 65535, default: 4096)
  half: U16 at block,
  @param(min: 0, max: 4294967295, default: 480, step: 16)
  ticks: U32 at block,
  @param(default: true, label: \"Bypass\")
  bypass: Bool at block,
  @param(default: false, unit: \"on/off\", id: \"mute\")
  mute: Bool at block,
  @param(min: 20.0, max: 20000.0, default: 1000.0, step: 1.0, unit: \"Hz\", scale: \"log\", label: \"Cutoff\", id: \"cutoff\")
  cutoff: F32 at block,
) -> F32 at sample {
  x
}
";

/// The lines of the interface that are the attributes of the inputs, trimmed.
fn param_lines(path: &str) -> Vec<String> {
    let out = Command::new(ONSA).arg("interface").arg(path).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    text.lines().map(str::trim).filter(|l| l.starts_with("@param(")).map(str::to_string).collect()
}

fn write(tag: &str, source: &str) -> (Dir, String) {
    let dir = Dir::bare(tag);
    let path = dir.0.join("m.onsa");
    std::fs::write(&path, source).unwrap();
    let arg = path.to_string_lossy().into_owned();
    (dir, arg)
}

#[test]
fn the_values_of_every_type_of_input_are_shown_in_the_form_of_the_type() {
    let (_dir, path) = write("interface_param_values", SOURCE);
    assert_eq!(
        param_lines(&path),
        [
            "@param(min: -60.0, max: 12.0, default: 0.0, unit: \"dB\")",
            "@param(min: 0.0, max: 4.0, default: 0.1, step: 0.5)",
            "@param(min: 0, max: 10, default: 2, step: 1, unit: \"n\", id: \"steps\")",
            "@param(min: -128, max: 127, default: -1)",
            "@param(min: -32768, max: 32767, default: 0, label: \"Offset\")",
            "@param(min: 0, max: 255, default: 128)",
            "@param(min: 0, max: 65535, default: 4096)",
            "@param(min: 0, max: 4294967295, default: 480, step: 16)",
            "@param(default: true, label: \"Bypass\")",
            "@param(default: false, unit: \"on/off\", id: \"mute\")",
            "@param(min: 20.0, max: 20000.0, default: 1000.0, step: 1.0, unit: \"Hz\", scale: \"log\", label: \"Cutoff\", id: \"cutoff\")",
        ]
    );
}

/// The inputs of the flows of the JSON document, with the `param` of each that has one.
fn params_of_inputs(v: &Value, out: &mut Vec<(String, Value)>) {
    match v {
        Value::Object(m) => {
            if let Some(Value::Array(inputs)) = m.get("inputs") {
                for i in inputs {
                    if let (Some(Value::String(n)), Some(p)) = (i.get("name"), i.get("param")) {
                        out.push((n.clone(), p.clone()));
                    }
                }
            }
            m.values().for_each(|x| params_of_inputs(x, out));
        }
        Value::Array(xs) => xs.iter().for_each(|x| params_of_inputs(x, out)),
        _ => {}
    }
}

#[test]
fn the_json_has_an_integer_for_an_integer_input_a_boolean_for_a_bool_and_a_float_for_a_float() {
    let (_dir, path) = write("interface_param_json", SOURCE);
    let out = Command::new(ONSA).args(["interface", "--json", &path]).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let doc: Value = serde_json::from_slice(&out.stdout).unwrap();
    let mut params = Vec::new();
    params_of_inputs(&doc, &mut params);
    let get = |n: &str| {
        params.iter().find(|(k, _)| k == n).unwrap_or_else(|| panic!("no param of {n}: {params:?}")).1.clone()
    };

    // An integer input: the numbers are integers (`2`, not `2.0`), the text keys are the text.
    let steps = get("steps");
    assert_eq!(steps["min"].as_i64(), Some(0), "{steps}");
    assert_eq!(steps["max"].as_i64(), Some(10), "{steps}");
    assert_eq!(steps["default"].as_i64(), Some(2), "{steps}");
    assert_eq!(steps["step"].as_i64(), Some(1), "{steps}");
    assert_eq!(steps["unit"].as_str(), Some("n"), "{steps}");
    assert_eq!(steps["id"].as_str(), Some("steps"), "{steps}");
    // The negative and the unsigned ones, to the ends of their ranges.
    assert_eq!(get("small")["default"].as_i64(), Some(-1));
    assert_eq!(get("small")["min"].as_i64(), Some(-128));
    assert_eq!(get("offset")["max"].as_i64(), Some(32767));
    assert_eq!(get("byte")["default"].as_u64(), Some(128));
    assert_eq!(get("half")["max"].as_u64(), Some(65535));
    assert_eq!(get("ticks")["max"].as_u64(), Some(4294967295));
    assert_eq!(get("ticks")["step"].as_u64(), Some(16));
    // `Bool`: `default` is a boolean, the text keys are the text, the keys that are not written are not there.
    let bypass = get("bypass");
    assert_eq!(bypass["default"], Value::Bool(true), "{bypass}");
    assert_eq!(bypass["label"].as_str(), Some("Bypass"), "{bypass}");
    assert_eq!(get("mute")["default"], Value::Bool(false));
    for key in ["min", "max", "step", "scale"] {
        assert!(bypass.get(key).is_none(), "{key} of a Bool: {bypass}");
    }
    // A float input: the numbers are floats.
    let level = get("level");
    assert_eq!(level["min"].as_f64(), Some(-60.0), "{level}");
    assert!(level["min"].is_f64(), "{level}");
    assert!(level["default"].is_f64(), "{level}");
    assert_eq!(get("wide")["default"].as_f64(), Some(0.1));
    assert_eq!(get("cutoff")["scale"].as_str(), Some("log"));
    // A key that is not written is not in the object.
    assert!(steps.get("scale").is_none() && steps.get("label").is_none(), "{steps}");
    assert!(level.get("step").is_none() && level.get("id").is_none(), "{level}");
}

/// The value of an Onsa string literal (the escapes of §2.4 and the braces `{{` and `}}`), or None if the text is not one such literal.
fn read_literal(lit: &str) -> Option<String> {
    let cs: Vec<char> = lit.chars().collect();
    if cs.len() < 2 || cs[0] != '"' || *cs.last().unwrap() != '"' {
        return None;
    }
    let mut out = String::new();
    let mut i = 1;
    while i < cs.len() - 1 {
        match cs[i] {
            '"' => return None,
            '\\' => {
                i += 1;
                match *cs.get(i)? {
                    'n' => out.push('\n'),
                    't' => out.push('\t'),
                    'r' => out.push('\r'),
                    '0' => out.push('\0'),
                    '\\' => out.push('\\'),
                    '"' => out.push('"'),
                    '\'' => out.push('\''),
                    'u' => {
                        if *cs.get(i + 1)? != '{' {
                            return None;
                        }
                        let end = (i + 2..cs.len()).find(|&j| cs[j] == '}')?;
                        let hex: String = cs[i + 2..end].iter().collect();
                        out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                        i = end;
                    }
                    _ => return None,
                }
            }
            '{' => {
                if cs.get(i + 1) != Some(&'{') {
                    return None;
                }
                out.push('{');
                i += 1;
            }
            '}' => {
                if cs.get(i + 1) != Some(&'}') {
                    return None;
                }
                out.push('}');
                i += 1;
            }
            c => out.push(c),
        }
        i += 1;
    }
    Some(out)
}

/// The text keys of the flows, the literal as it is written in the source and the value it has.
const TEXTS: &[(&str, &str)] = &[
    (r#""plain""#, "plain"),
    (r#""a\"b""#, "a\"b"),
    (r#""back\\slash""#, "back\\slash"),
    (r#""two\nlines""#, "two\nlines"),
    (r#""tab\there""#, "tab\there"),
    (r#""{{braces}} and {{""#, "{braces} and {"),
    (r#""a\"b\\c\nd {{e}} \u{3b1}""#, "a\"b\\c\nd {e} \u{3b1}"),
    (r#""ゲイン""#, "ゲイン"),
    ("\"\"", ""),
];

fn text_source() -> String {
    let mut s = String::new();
    for (i, (lit, _)) in TEXTS.iter().enumerate() {
        s += &format!(
            "pub flow f{i}(\n  x: F32 at sample,\n  @param(default: 0.5, label: {lit})\n  p: F32 at block,\n) -> F32 at sample {{\n  x * p\n}}\n\n"
        );
    }
    s
}

#[test]
fn a_text_key_is_shown_as_a_literal_that_reads_back_to_its_value_in_one_line() {
    let (_dir, path) = write("interface_param_text", &text_source());
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let attrs: Vec<(usize, &str)> = lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.trim_start().starts_with("@param("))
        .map(|(i, l)| (i, l.trim()))
        .collect();
    assert_eq!(attrs.len(), TEXTS.len(), "{text}");
    for ((i, line), (lit, value)) in attrs.iter().zip(TEXTS) {
        // The attribute is one line, and the line after it is the input that it is of.
        assert!(
            lines[i + 1].trim().starts_with("p: F32 at block"),
            "{lit}: the attribute is split by a line break: {text}"
        );
        let shown = line
            .strip_prefix("@param(default: 0.5, label: ")
            .and_then(|r| r.strip_suffix(')'))
            .unwrap_or_else(|| panic!("{lit}: the line is not `@param(default: 0.5, label: <literal>)`: {line}"));
        assert_eq!(read_literal(shown).as_deref(), Some(*value), "{lit}: shown as {shown}");
    }
}

#[test]
fn what_is_shown_for_a_text_key_is_a_literal_that_the_compiler_reads_to_the_same_line() {
    // The shown literal is put back in a source: the interface of that source shows the same attribute (the literal is a
    // fixed point of the rule, and the compiler accepts it).
    let (_dir, path) = write("interface_param_text_fixed", &text_source());
    let out = Command::new(ONSA).arg("interface").arg(&path).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let shown: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter_map(|l| l.strip_prefix("@param(default: 0.5, label: "))
        .map(|r| r.strip_suffix(')').unwrap().to_string())
        .collect();
    assert_eq!(shown.len(), TEXTS.len(), "{text}");
    let mut again = String::new();
    for (i, lit) in shown.iter().enumerate() {
        again += &format!(
            "pub flow f{i}(\n  x: F32 at sample,\n  @param(default: 0.5, label: {lit})\n  p: F32 at block,\n) -> F32 at sample {{\n  x * p\n}}\n\n"
        );
    }
    let (_dir2, path2) = write("interface_param_text_fixed2", &again);
    assert_eq!(param_lines(&path2), param_lines(&path));
}

#[test]
fn the_reader_of_the_literals_of_this_file_reads_the_forms_of_the_spec() {
    // The reader is of §2.4: the escapes `\n \t \r \0 \\ \" \' \u{…}` and the braces `{{` `}}`; a bare `"` or a single brace is not a literal.
    for (lit, value) in TEXTS {
        assert_eq!(read_literal(lit).as_deref(), Some(*value), "{lit}");
    }
    assert_eq!(read_literal(r#""a\u{1F600}b\0\'""#).as_deref(), Some("a\u{1F600}b\0'"));
    for bad in [r#""a"b""#, r#""a{b}""#, r#""a}""#, r#""\x41""#, r#"abc"#, r#""\u{110000}""#] {
        assert_eq!(read_literal(bad), None, "{bad}");
    }
}
