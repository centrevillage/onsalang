//! A function type as a return type before an effect row, in the signatures of `onsa interface`
//! (W3-20/b, spec §8.1, §18.2). `fn a() -> (fn()) uses {Alloc}` (the effect row of `a`) and
//! `fn b() -> fn() uses {Alloc}` (the effect row of the returned type) are different types since
//! R-43 lets the parentheses be written; the signature keeps them apart by writing the returned
//! function type in parentheses when a `uses` follows it, and so does a function type inside a type
//! (`fn() -> (fn()) uses {Alloc}`). A signature read again as a declaration gives the same one: the
//! repair loop reads this output.

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

const ONSA: &str = env!("CARGO_BIN_EXE_onsa");

/// The functions: (the header written in the source, its body). The headers are the signatures
/// `onsa interface` writes.
const FNS: &[(&str, &str)] = &[
    ("pub fn a() -> (fn()) uses {Alloc}", "fn() { }"),
    ("pub fn b() -> fn() uses {Alloc}", "fn() { }"),
    ("pub fn c() -> fn()", "fn() { }"),
    ("pub fn d() -> (fn() uses {Alloc}) uses {Alloc}", "fn() { }"),
    ("pub fn e(f: fn() -> (fn()) uses {Alloc}) -> I32", "1"),
    ("pub fn g(f: fn() -> fn() uses {Alloc}) -> I32", "1"),
    ("pub fn h() -> fn(fn() -> (fn()) uses {Alloc}) -> I32", "e"),
];

struct Dir(PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let d = std::env::temp_dir().join(format!("onsa_interface_fn_return_{}_{tag}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        Dir(d)
    }

    fn file(&self, name: &str, text: &str) -> String {
        let p = self.0.join(name);
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn onsa(args: &[&str]) -> Output {
    let out = Command::new(ONSA).args(args).output().expect("run onsa");
    assert_eq!(out.status.code(), Some(0), "{args:?}: {out:?}");
    out
}

fn source(headers: &[String]) -> String {
    headers.iter().zip(FNS).map(|(h, (_, body))| format!("{h} {{\n  {body}\n}}\n")).collect::<Vec<_>>().join("\n")
}

/// The lines of the text output that are signatures of functions.
fn text_signatures(path: &str) -> Vec<String> {
    let out = String::from_utf8(onsa(&["interface", path]).stdout).unwrap();
    out.lines().filter(|l| l.starts_with("pub fn ")).map(str::to_string).collect()
}

fn json_signatures(v: &Value, out: &mut Vec<String>) {
    match v {
        Value::Object(m) => {
            for (k, x) in m {
                match x {
                    Value::String(s) if k == "signature" => out.push(s.clone()),
                    _ => json_signatures(x, out),
                }
            }
        }
        Value::Array(xs) => xs.iter().for_each(|x| json_signatures(x, out)),
        _ => {}
    }
}

#[test]
fn a_returned_function_type_before_uses_is_in_parentheses_and_reads_back() {
    let d = Dir::new("sig");
    let headers: Vec<String> = FNS.iter().map(|(h, _)| h.to_string()).collect();
    let path = d.file("p.onsa", &source(&headers));
    let text = text_signatures(&path);
    assert_eq!(text, headers, "the text signatures");
    let json: Value = serde_json::from_slice(&onsa(&["interface", "--json", &path]).stdout).unwrap();
    let mut sigs = Vec::new();
    json_signatures(&json, &mut sigs);
    assert_eq!(sigs, headers, "the signatures of the JSON");
    // `a` and `b` are different signatures.
    assert_ne!(text[0], text[1]);
    // The signatures, written back as the headers, give the same signatures.
    let again = d.file("q.onsa", &source(&text));
    assert_eq!(text_signatures(&again), text);
}
