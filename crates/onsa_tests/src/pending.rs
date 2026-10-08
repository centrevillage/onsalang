//! Reader of the list of things expected not to pass yet, `tests/pending.toml`
//! (plan D-16 7, Q-08), for the test runners (W1-03) to ask whether a target
//! is pending.
//!
//! This module does not validate the list. The validation (the forms of the
//! targets, the S / R numbers, the work IDs, duplicates, paths) is only in the
//! gate's Python, `tools/pending.py`; the gate runs it on every check. Here a
//! list is only decoded into the fields and the kinds.

use std::path::Path;

use serde::Deserialize;

/// The file, relative to the repository root.
pub const PATH: &str = "tests/pending.toml";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    SpecExample,
    DiagCode,
    Gate,
    TestCase,
    FuzzInput,
    /// One fix candidate that breaks the contract of §18.1 (S-236):
    /// `"<file from the root>:<line>:<col> <code> fix<K>"` (W3-17,
    /// [`crate::fix_contract`]).
    FixContract,
}

/// What a `test-case` entry expects of its case, other than a failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Expect {
    /// The case ends in an internal error (S-67). Without it, an internal
    /// error is never silenced by the list (W1-04).
    Internal,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub kind: Kind,
    pub target: String,
    pub reasons: Vec<String>,
    pub until: String,
    pub note: String,
    #[serde(default)]
    pub expect: Option<Expect>,
    /// The failing rows the entry holds (the test vectors' items, W2-02).
    #[serde(default)]
    pub rows: Option<usize>,
    /// Which rows fail (the test vectors' items, with `rows`).
    #[serde(default)]
    pub digest: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Pending {
    #[serde(default)]
    pub pending: Vec<Entry>,
}

impl Pending {
    pub fn parse(text: &str) -> Result<Pending, String> {
        toml::from_str(text).map_err(|e| e.to_string())
    }

    /// Read `tests/pending.toml` under the repository root.
    pub fn load(root: &Path) -> Result<Pending, String> {
        let path = root.join(PATH);
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        Pending::parse(&text).map_err(|e| format!("{}: {e}", path.display()))
    }

    /// The entry for `target` of `kind`, if it is pending.
    pub fn get(&self, kind: Kind, target: &str) -> Option<&Entry> {
        self.pending.iter().find(|e| e.kind == kind && e.target == target)
    }

    pub fn of_kind(&self, kind: Kind) -> impl Iterator<Item = &Entry> {
        self.pending.iter().filter(move |e| e.kind == kind)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_repository_list() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        // Only that it reads: the list becomes empty when the work is done.
        Pending::load(&root).unwrap();
    }

    #[test]
    fn reads_every_kind() {
        let text = r#"
[[pending]]
kind = "spec-example"
target = "§3.1 d235a27a: let a = x + y - z"
reasons = ["S-45"]
until = "W3-07"
note = "n"

[[pending]]
kind = "diag-code"
target = "E0812"
reasons = ["S-110"]
until = "W7-06"
note = "n"

[[pending]]
kind = "gate"
target = "c-header/span_const"
reasons = ["R-65"]
until = "W10-04"
note = "n"

[[pending]]
kind = "test-case"
target = "tests/spec/flow/x.onsa::name"
reasons = ["R-12"]
until = "W2-08"
note = "n"

[[pending]]
kind = "fuzz-input"
target = "tests/fuzz/x.onsa"
reasons = ["R-03"]
until = "W2-06"
note = "n"

[[pending]]
kind = "test-case"
target = "tests/spec/flow/y.onsa"
reasons = ["R-77"]
until = "W7-03"
note = "n"
expect = "internal"

[[pending]]
kind = "fix-contract"
target = "tests/spec/negative/types.onsa:59:3 E0411 fix1"
reasons = ["S-236"]
until = "W5-02"
note = "n"
"#;
        let list = Pending::parse(text).unwrap();
        let kinds: Vec<Kind> = list.pending.iter().map(|e| e.kind).collect();
        assert_eq!(
            kinds,
            [
                Kind::SpecExample,
                Kind::DiagCode,
                Kind::Gate,
                Kind::TestCase,
                Kind::FuzzInput,
                Kind::TestCase,
                Kind::FixContract
            ]
        );
        assert_eq!(list.pending[3].expect, None);
        assert_eq!(list.pending[5].expect, Some(Expect::Internal));
        assert_eq!(list.get(Kind::DiagCode, "E0812").unwrap().until, "W7-06");
        assert!(list.get(Kind::Gate, "E0812").is_none());
        assert!(Pending::parse("").unwrap().pending.is_empty());
    }

    #[test]
    fn rejects_unknown_kinds_and_fields() {
        let entry =
            "[[pending]]\nkind = \"spec\"\ntarget = \"x\"\nreasons = [\"S-1\"]\nuntil = \"W1-01\"\nnote = \"n\"\n";
        assert!(Pending::parse(entry).is_err());
        let extra = entry.replace("\"spec\"", "\"gate\"") + "line = 3\n";
        assert!(Pending::parse(&extra).is_err());
        let missing = entry.replace("\"spec\"", "\"gate\"").replace("note = \"n\"\n", "");
        assert!(Pending::parse(&missing).is_err());
    }
}
