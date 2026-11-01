//! The settings of a case: an `onsa.toml` fragment at the head of a file
//! (plan D-05, R-80 (5)).
//!
//! ```text
//! // onsa.toml
//! // [package]
//! // name = "echo"
//! // edition = "2026"
//! //
//! // [test]
//! // mode = "test"
//! // spec = ["§11.4"]
//!
//! pub flow echo(...
//! ```
//!
//! The fragment starts on line 1 with the line `// onsa.toml`. Each following
//! line is `//` (an empty line of the TOML) or starts with `// `; a blank line
//! ends it. A fragment with only `[test]` has no manifest (a single file
//! without `onsa.toml`, spec §15.1); any other table makes it the manifest of
//! a package holding only this file, so `[package]` is then required as in
//! `onsa.toml`. The manifest is read by the compiler's own reader, once, when
//! the case loads (`onsa_driver::Loaded::from_input`, with
//! `ManifestForm::Fragment`, which skips the `[test]` table: the real
//! `onsa.toml` has none).

use serde::{Deserialize, Serialize};

use onsa_driver::manifest::table::FRAGMENT_TEST;

/// The first line of a fragment.
pub const HEADER: &str = "// onsa.toml";

/// How far a case runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Mode {
    /// Recorded only, never run (fragments with `...`, pseudo code).
    None,
    /// Only parsing.
    Parse,
    /// `check`, then the build of every target (default).
    #[default]
    Check,
    /// As `check`, then every `test` block in the interpreter.
    Test,
}

/// An output compared with a golden file (Q-04, plan D-05).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum GoldenKind {
    /// `onsa dump --core`: `tests/golden/core/<case>.core`.
    Core,
    /// `onsa interface`: `tests/golden/interface/<case>.txt`.
    Interface,
    /// The C of every target: `tests/golden/c/<case>.<target>.c` and `.h`.
    C,
}

/// The `[test]` table: closed (an unknown key or a wrong type is an error of the case).
#[derive(Debug, Clone, Default, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestSettings {
    #[serde(default)]
    pub mode: Mode,
    /// Spec sections the case tests (`"§11.4"`, Q-05).
    #[serde(default)]
    pub spec: Vec<String>,
    #[serde(default)]
    pub golden: Vec<GoldenKind>,
    /// Flows whose `onsa graph` is compared: `tests/golden/graph/<case>.<flow>.dot`.
    #[serde(default)]
    pub golden_graph: Vec<String>,
    /// Run every exported flow of every target in the interpreter and in C (§13.4).
    #[serde(default)]
    pub conformance: bool,
    /// The fix candidates the check's diagnostics give, as files next to each
    /// source file: `<file>.fix1` .. `<file>.fix<N>` hold the file after the
    /// K-th candidate of every diagnostic is applied (W3-02, [`crate::fixes`]).
    /// `None`: not written, and the candidates are not counted; a written
    /// `fixes = 0` checks that no diagnostic has a candidate (X-15).
    #[serde(default)]
    pub fixes: Option<u32>,
    /// `[[test.host]]`: sequences of calls at the C boundary of a target (K-14, [`crate::host`]).
    #[serde(default, deserialize_with = "crate::host::de_seqs")]
    pub host: Vec<crate::host::Seq>,
    /// `[[test.fix]]`: what one fix candidate leaves after it, or promises
    /// more (`clean`, `same_code`), against the contract of §18.1 (W3-17,
    /// [`crate::fix_contract`]).
    #[serde(default, deserialize_with = "crate::fix_contract::de_specs")]
    pub fix: Vec<crate::fix_contract::FixSpec>,
    /// `canonical = false`: a file without markers that `fmt` rewrites (a
    /// line break the formatter moves, W3-11). It is not compared with the
    /// normal form; fmt must still take it, change it, and give a text it
    /// takes again unchanged and that parses ([`crate::run`]).
    /// Not written: the file is canonical (`Some(true)` says so again).
    #[serde(default)]
    pub canonical: Option<bool>,
}

impl TestSettings {
    /// Whether a file of the case without markers is in the normal form of fmt.
    pub fn canonical(&self) -> bool {
        self.canonical != Some(false)
    }
}

/// A parsed fragment.
#[derive(Debug, Clone, Default)]
pub struct Fragment {
    /// The manifest as its TOML text: the head of the file, whose bytes it
    /// keeps (it holds the `[test]` table too).
    pub manifest: Option<String>,
    pub test: TestSettings,
}

impl Fragment {
    /// The manifest of the case file `path`, which the text points into.
    pub fn manifest_source(&self, path: &str) -> Option<onsa_driver::ManifestSource> {
        self.manifest.as_ref().map(|text| onsa_driver::ManifestSource {
            path: path.to_string(),
            text: text.clone(),
            form: onsa_driver::ManifestForm::Fragment,
        })
    }
}

/// Read the fragment of a file: `Ok(None)` when the file has none.
pub fn parse(text: &str) -> Result<Option<Fragment>, String> {
    let lines: Vec<&str> = text.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if looks_like_mode(line) {
            return Err(format!(
                "line {}: `//! mode:` is gone; write `mode` in the `[test]` table of a `{HEADER}` fragment",
                i + 1
            ));
        }
    }
    if let Some(first) = lines.first()
        && *first != HEADER
        && looks_like_header(first)
    {
        return Err(format!("line 1: the first line of a fragment is exactly `{HEADER}` (found `{first}`)"));
    }
    if lines.first().is_none_or(|l| *l != HEADER) {
        return Ok(None);
    }
    // The TOML is the head of the file with its comment marks made spaces
    // (the header, `//` and `// `; indentation is whitespace in TOML) and its
    // line ends kept (CR LF too): a place in the TOML is the same byte of
    // the file.
    let mut toml_text = String::new();
    let mut end = lines.len();
    for (i, raw) in text.split_inclusive('\n').enumerate() {
        let line = raw.strip_suffix('\n').unwrap_or(raw);
        let line = line.strip_suffix('\r').unwrap_or(line);
        if i == 0 {
            toml_text.push_str(&" ".repeat(line.len()));
            toml_text.push_str(&raw[line.len()..]);
            continue;
        }
        let body = if line == "//" {
            ""
        } else if let Some(b) = line.strip_prefix("// ") {
            b
        } else if line.trim().is_empty() {
            end = i;
            break;
        } else {
            return Err(format!(
                "line {}: a fragment line is `//` or starts with `// `; end the fragment with a blank line",
                i + 1
            ));
        };
        if body.contains("//~") {
            return Err(format!("line {}: no `//~` marker inside the fragment", i + 1));
        }
        toml_text.push_str(&" ".repeat(line.len() - body.len()));
        toml_text.push_str(body);
        toml_text.push_str(&raw[line.len()..]);
    }
    if end == 1 {
        return Err(format!("line 1: the `{HEADER}` fragment is empty"));
    }
    let table: toml::Table = toml::from_str(&toml_text).map_err(|e| format!("fragment: {e}"))?;
    let manifest = (!table.keys().all(|k| k == FRAGMENT_TEST)).then(|| toml_text.clone());
    // `[test]` read from the text too, so its errors keep their position.
    #[derive(Deserialize)]
    struct TestTable {
        #[serde(default)]
        test: TestSettings,
    }
    let mut test = toml::from_str::<TestTable>(&toml_text).map_err(|e| format!("fragment: [test]: {e}"))?.test;
    crate::host::locate(&mut test.host, &toml_text);
    crate::fix_contract::locate(&mut test.fix, &toml_text);
    check_settings(&test, &lines[..end])?;
    crate::host::check(&test.host, test.mode).map_err(|e| format!("fragment: {e}"))?;
    crate::fix_contract::check_specs(&test.fix, test.mode).map_err(|e| format!("fragment: {e}"))?;
    Ok(Some(Fragment { manifest, test }))
}

/// A first line that means to be the fragment's header: a comment naming
/// `onsa` and `toml` or `config` (`//onsa.toml`, `// ONSA.toml`,
/// `// onsa.toml:`, `// onsa-config`). Checked on line 1 only: further down,
/// such a line is an ordinary comment.
fn looks_like_header(line: &str) -> bool {
    let t = line.trim();
    let Some(rest) = t.strip_prefix("//") else { return false };
    let lower = rest.to_lowercase();
    lower.contains("onsa") && (lower.contains("toml") || lower.contains("config"))
}

/// A line that is the old header `//! mode:`, up to the spaces and the case
/// (`//!mode:`, `//! Mode :`). Only `//!` lines: `// mode: …` is an ordinary comment.
fn looks_like_mode(line: &str) -> bool {
    let Some(rest) = line.trim_start().strip_prefix("//!") else { return false };
    let lower = rest.trim_start().to_lowercase();
    lower.strip_prefix("mode").is_some_and(|r| r.trim_start().starts_with(':'))
}

/// The forms inside `[test]` that need no other part of the case.
fn check_settings(t: &TestSettings, lines: &[&str]) -> Result<(), String> {
    let at = |key: &str| test_key_line(lines, key);
    for s in &t.spec {
        if !is_section(s) {
            return Err(format!("line {}: fragment: [test] spec: `{s}` is not a section (`§11.4`)", at("spec")));
        }
    }
    dups("spec", &t.spec).map_err(|e| format!("line {}: {e}", at("spec")))?;
    dups("golden", &t.golden).map_err(|e| format!("line {}: {e}", at("golden")))?;
    dups("golden_graph", &t.golden_graph).map_err(|e| format!("line {}: {e}", at("golden_graph")))?;
    if !t.canonical() && t.mode == Mode::None {
        return Err(format!("line {}: fragment: [test] canonical = false needs a mode that runs", at("canonical")));
    }
    if matches!(t.mode, Mode::Parse | Mode::None) && t.fixes.is_some_and(|n| n > 0) {
        return Err(format!(
            "line {}: fragment: [test] fixes needs `mode = \"check\"` or `\"test\"` (not {:?})",
            at("fixes"),
            t.mode
        ));
    }
    if matches!(t.mode, Mode::Parse | Mode::None)
        && (!t.golden.is_empty() || !t.golden_graph.is_empty() || t.conformance)
    {
        return Err(format!(
            "line {}: {}",
            at("mode"),
            format_args!(
                "fragment: [test] golden and conformance need `mode = \"check\"` or `\"test\"` (not {:?})",
                t.mode
            )
        ));
    }
    Ok(())
}

/// The line of `key` in the fragment's `[test]` table (else of `[test]`, else 1).
fn test_key_line(lines: &[&str], key: &str) -> usize {
    let body = |l: &str| l.trim_start_matches('/').trim().to_string();
    let Some(start) = lines.iter().position(|l| body(l) == "[test]") else { return 1 };
    lines[start + 1..]
        .iter()
        .take_while(|l| !body(l).starts_with('['))
        .position(|l| body(l).strip_prefix(key).is_some_and(|r| r.trim_start().starts_with('=')))
        .map_or(start + 1, |i| start + i + 2)
}

fn dups<T: PartialEq + std::fmt::Debug>(key: &str, xs: &[T]) -> Result<(), String> {
    for (i, x) in xs.iter().enumerate() {
        if xs[..i].contains(x) {
            return Err(format!("fragment: [test] {key}: {x:?} is written twice"));
        }
    }
    Ok(())
}

/// `§<n>(.<n>)*`.
pub fn is_section(s: &str) -> bool {
    s.strip_prefix('§').is_some_and(|r| {
        r.split('.')
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()) && !(p.len() > 1 && p.starts_with('0')))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_fragment() {
        assert!(parse("pub fn f() {}\n").unwrap().is_none());
        assert!(parse("").unwrap().is_none());
    }

    #[test]
    fn test_only() {
        let f = parse("// onsa.toml\n// [test]\n// mode = \"parse\"\n// spec = [\"§8.1\"]\n\nfn f() {}\n")
            .unwrap()
            .unwrap();
        assert!(f.manifest.is_none());
        assert_eq!(f.test.mode, Mode::Parse);
        assert_eq!(f.test.spec, vec!["§8.1".to_string()]);
    }

    #[test]
    fn with_manifest() {
        let text = "// onsa.toml\n// [package]\n// name = \"echo\"\n// edition = \"2026\"\n//\n// [targets.t]\n// kind = \"source\"\n// lang = \"c\"\n// platform = \"host\"\n//\n// [test]\n// golden = [\"c\"]\n";
        let f = parse(text).unwrap().unwrap();
        let m = onsa_driver::manifest::read(&f.manifest_source("m.onsa").unwrap()).unwrap();
        assert_eq!(m.package.value.name.value, "echo");
        assert!(m.targets.contains_key("t"));
        assert_eq!(f.test.golden, vec![GoldenKind::C]);
    }

    /// The TOML of a fragment is the head of the file byte for byte, with LF
    /// or CR LF line ends: the places the manifest's reader gives are places
    /// of the file (W4-02).
    #[test]
    fn the_manifest_keeps_the_bytes_of_the_file() {
        for eol in ["\n", "\r\n"] {
            let text = [
                "// onsa.toml",
                "// [package]",
                "// name = \"echo\"",
                "//",
                "// [targets.t]",
                "// kind = \"source\"",
                "// platform = \"host\"",
                "// [test]",
                "// mode = \"check\"",
                "",
                "fn f() {}",
                "",
            ]
            .join(eol);
            let f = parse(&text).unwrap().unwrap();
            let toml = f.manifest.clone().unwrap();
            // Every byte is the file's, or a space over a comment mark.
            assert_eq!(toml.len(), text.find(&format!("{eol}{eol}")).unwrap() + eol.len(), "{eol:?}");
            assert!(
                toml.bytes().zip(text.bytes()).all(|(a, b)| a == b || (a == b' ' && !matches!(b, b'\n' | b'\r'))),
                "{toml:?}"
            );
            let m = onsa_driver::manifest::read(&f.manifest_source("m.onsa").unwrap()).unwrap();
            let name = &m.package.value.name;
            assert_eq!(&text[name.key.clone()], "name", "{eol:?}");
            assert_eq!(&text[name.span.clone()], "\"echo\"", "{eol:?}");
            let t = &m.targets["t"];
            assert_eq!(&text[t.key.clone()], "t", "{eol:?}");
            assert_eq!(&text[t.value.platform.span.clone()], "\"host\"", "{eol:?}");
        }
    }

    /// The manifest of a fragment is not read here: its errors are those of
    /// the manifest's reader when the case loads, at the places of the file.
    #[test]
    fn the_manifest_is_read_by_the_reader_of_the_compiler() {
        for text in [
            "// onsa.toml\n// [targets.t]\n// kind = \"source\"\n// platform = \"host\"\n",
            "// onsa.toml\n// [tests]\n// mode = \"parse\"\n",
        ] {
            let f = parse(text).unwrap().unwrap();
            let e = onsa_driver::manifest::read(&f.manifest_source("m.onsa").unwrap()).unwrap_err();
            assert!(e.starts_with("m.onsa: missing table `[package]`"), "{e}");
        }
        let f = parse("// onsa.toml\n// [package]\n// name = 3\n").unwrap().unwrap();
        let e = onsa_driver::manifest::read(&f.manifest_source("m.onsa").unwrap()).unwrap_err();
        assert!(e.contains("line 3, column 11"), "{e}");
    }

    #[test]
    fn errors() {
        let bad = [
            "//! mode: parse\nfn f() {}\n",
            "// onsa.toml\n\nfn f() {}\n",
            "// onsa.toml\n// [test]\n//mode = \"parse\"\n",
            "// onsa.toml\n// [test]\nfn f() {}\n",
            "// onsa.toml\n// [test]\n// moed = \"parse\"\n",
            "// onsa.toml\n// [test]\n// mode = \"run\"\n",
            "// onsa.toml\n// [test]\n// spec = [\"11.4\"]\n",
            "// onsa.toml\n// [test]\n// spec = [\"§11.4\", \"§11.4\"]\n",
            "// onsa.toml\n// [test]\n// mode = \"parse\"\n// golden = [\"core\"]\n",
            "// onsa.toml\n// [test]\n// mode = \"parse\" //~ E0010\n",
            "// onsa.toml\n// test = 1\n",
            "//onsa.toml\n// [test]\n// mode = \"parse\"\n",
            "// ONSA.toml\n// [test]\n",
            "// onsa toml\n// [test]\n",
            "//  onsa.toml\n// [test]\n",
            "//!mode: parse\n",
            "//! mode : parse\n",
        ];
        for b in bad {
            assert!(parse(b).is_err(), "{b:?}");
        }
    }

    #[test]
    fn ordinary_comments_are_not_headers() {
        // `//! mode:` is the old header only on a `//!` line; `// onsa.toml`
        // means a fragment only on line 1.
        let text = "// Filter.\n// mode: bypass means the filter is skipped\n/// Mode: 0 is off\n\
                    pub fn f() -> I32 {\n  1\n}\n// onsa.toml\n";
        assert!(parse(text).unwrap().is_none());
        let with = format!("// onsa.toml\n// [test]\n// spec = [\"§7\"]\n\n{text}");
        assert_eq!(parse(&with).unwrap().unwrap().test.spec, ["§7"]);
        for old in ["//! mode: parse\n", "//!mode: parse\n", "//! Mode : parse\n", "fn f() {}\n  //!  MODE:none\n"] {
            assert!(parse(old).unwrap_err().contains("`//! mode:` is gone"), "{old:?}");
        }
    }

    #[test]
    fn misspelled_first_lines_fail() {
        for first in
            ["//onsa.toml", "// ONSA.toml", "// onsa toml", "// onsa.toml:", "// onsa.toml fragment", "// onsa-config"]
        {
            let text = format!("{first}\n// [test]\n// mode = \"parse\"\n\nfn f() {{}}\n");
            let e = parse(&text).unwrap_err();
            assert!(e.starts_with("line 1:"), "{first:?}: {e}");
        }
    }

    #[test]
    fn errors_of_test_keys_have_lines() {
        let e = parse("// onsa.toml\n// [test]\n// mode = \"parse\"\n// spec = [\"11.4\"]\n").unwrap_err();
        assert!(e.starts_with("line 4:"), "{e}");
        let e = parse("// onsa.toml\n// [test]\n// spec = [\"§1\", \"§1\"]\n").unwrap_err();
        assert!(e.starts_with("line 3:"), "{e}");
        let e = parse("// onsa.toml\n// [test]\n//\n// golden = [\"core\"]\n// mode = \"none\"\n").unwrap_err();
        assert!(e.starts_with("line 5:"), "{e}");
    }

    #[test]
    fn errors_keep_the_position_of_the_file() {
        let e = parse("// onsa.toml\n// [test]\n// mode = \"run\"\n").unwrap_err();
        assert!(e.contains("line 3, column 11"), "{e}");
    }

    #[test]
    fn sections() {
        assert!(is_section("§11.4") && is_section("§7") && is_section("§17.10"));
        assert!(
            !is_section("11.4") && !is_section("§") && !is_section("§11.") && !is_section("§1a") && !is_section("§01")
        );
    }
}
