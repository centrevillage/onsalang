//! The guard on rewriting the copies of the texts after the candidates (the
//! `.fixK` files, [`crate::fixes`]; the `fixed` texts of
//! `spec/foreign-forms.toml`, [`crate::foreign_forms`]; Q-04, X-3).
//!
//! A copy may hold a rule of the spec that no promise states (a copy written
//! from the spec, or kept from an output that was right). Before
//! `UPDATE_GOLDEN` changes or removes a copy, the old side (every copy of
//! the candidate, each in place of its file; a file without a copy as it is)
//! and the new side (the output) are each checked through the entry of the
//! case, and the rewriting is refused when the new side reports a diagnostic
//! the old one does not ([`new_only`]): the copy held a rule, which moves to
//! a promise (`[[test.fix]]`, `property`) before the copy is rewritten with
//! `UPDATE_GOLDEN=worse` (the guard does not read the promises).
//! Creating a copy (no old one) is not guarded: the contract of the
//! candidates sees that output ([`crate::fix_contract`]).
//!
//! `UPDATE_GOLDEN=worse` ([`crate::golden::Update::Worse`]) rewrites a
//! refused copy anyway, and the summary lists it. A check that ends in an
//! internal error rewrites nothing, `worse` or not.

use std::collections::BTreeMap;

use onsa_diag::{Code, FileId, SourceMap};
use onsa_driver::{Analyzed, Loaded};

use crate::case::Setup;
use crate::fix_contract::{check_text, check_texts};

/// The guard of the copies of one candidate of a case: `old` and `new` hold
/// the texts that replace files of `loaded` (the others stay). `Ok`: the
/// diagnostics only the new side reports ([`new_only`]); `Err`: a check
/// that cannot be made.
pub(crate) fn case(
    setup: &Setup,
    loaded: &Loaded,
    old: &BTreeMap<FileId, String>,
    new: &BTreeMap<FileId, String>,
) -> Result<Vec<String>, String> {
    let (old_loaded, old_analyzed) =
        check_texts(setup, loaded, old).map_err(|e| format!("the check of the copies {e}"))?;
    let (new_loaded, new_analyzed) =
        check_texts(setup, loaded, new).map_err(|e| format!("the check of the texts after the candidates {e}"))?;
    Ok(new_only((&old_loaded.sources, &old_analyzed), (&new_loaded.sources, &new_analyzed)))
}

/// The guard of one copy of a single-file example: `old` is the copy, `new`
/// the text after its candidate (each checked by [`check_text`]).
pub(crate) fn text(old: &str, new: &str) -> Result<Vec<String>, String> {
    let old = check_text(old).map_err(|e| format!("the check of the copy ends in an internal error: {e}"))?;
    let new = check_text(new).map_err(|e| format!("the check of the text after it ends in an internal error: {e}"))?;
    Ok(new_only((&old.loaded.sources, &old.analyzed), (&new.loaded.sources, &new.analyzed)))
}

/// What a refused rewriting says: `what` is the copies, `to` where their rule moves.
pub(crate) fn refused(what: &str, found: &[String], to: &str) -> String {
    format!(
        "UPDATE_GOLDEN=1 does not rewrite {what}: after the candidate the check reports {}, which the copies do \
         not leave. The copies hold a rule of the spec: move it to {to}, then rewrite them with \
         `UPDATE_GOLDEN=worse` (the guard compares the copies with the output only; the summary lists them)",
        found.join(", ")
    )
}

/// The key of a diagnostic: its file, its unit (the position among the
/// units of the file; `None` outside every unit, or when the two sides do
/// not have as many units in the file) and its code. Never its place.
type Key = (String, Option<usize>, Code);

/// The number of units of each file, and the position of each unit among
/// those of its file.
fn positions(sources: &SourceMap, a: &Analyzed) -> (BTreeMap<String, usize>, Vec<usize>) {
    let mut count: BTreeMap<String, usize> = BTreeMap::new();
    let pos = a
        .units
        .iter()
        .map(|u| {
            let n = count.entry(sources.file(u.span.file).name().to_string()).or_default();
            *n += 1;
            *n - 1
        })
        .collect();
    (count, pos)
}

/// The diagnostics of `new` that `old` does not report, compared as
/// multisets of [`Key`] (every stage): `E0302 at main.onsa:14:11`.
pub(crate) fn new_only(old: (&SourceMap, &Analyzed), new: (&SourceMap, &Analyzed)) -> Vec<String> {
    let (old_count, old_pos) = positions(old.0, old.1);
    let (new_count, new_pos) = positions(new.0, new.1);
    let keys = |(sources, a): (&SourceMap, &Analyzed), pos: &[usize]| -> Vec<(Key, String)> {
        a.diagnostics
            .iter()
            .zip(&a.diagnostic_units)
            .map(|(d, unit)| {
                let f = sources.file(d.span.file);
                let name = f.name().to_string();
                let same = old_count.get(&name) == new_count.get(&name);
                let unit = unit.filter(|_| same).map(|u| pos[u]);
                let lc = f.line_col(d.span.start);
                let shown = format!("{} at {name}:{}:{}", d.code.as_str(), lc.line, lc.col);
                ((name, unit, d.code), shown)
            })
            .collect()
    };
    let mut left: BTreeMap<Key, usize> = BTreeMap::new();
    for (k, _) in keys(old, &old_pos) {
        *left.entry(k).or_default() += 1;
    }
    let mut out = Vec::new();
    for (k, shown) in keys(new, &new_pos) {
        match left.get_mut(&k) {
            Some(n) if *n > 0 => *n -= 1,
            _ => out.push(shown),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The keys: a place that moves is the same diagnostic; another unit
    /// of the file, or another code, is not; a file whose number of units
    /// differs compares by file and code.
    #[test]
    fn diagnostics_compare_by_file_unit_and_code() {
        let check = |old: &str, new: &str| text(old, new).unwrap();
        let f = "pub fn f() -> I32 {\n  x\n}\n";
        let g = "pub fn g() -> I32 {\n  1\n}\n";
        let g_bad = "pub fn g() -> I32 {\n  y\n}\n";
        // The same error, moved down two lines: nothing new.
        assert_eq!(check(&format!("{f}\n{g}"), &format!("\n\n{f}\n{g}")), Vec::<String>::new());
        // The same code in another unit: new.
        assert_eq!(check(&format!("{f}\n{g}"), &format!("{f}\n{g_bad}")), ["E0302 at m.onsa:6:3"]);
        // Fewer errors: nothing new.
        assert_eq!(check(&format!("{f}\n{g_bad}"), &format!("{f}\n{g}")), Vec::<String>::new());
        // A unit more on the new side: by file and code, the error of `f` moved into the third unit is the same ...
        let h = |body: &str| format!("pub fn h() -> I32 {{\n  {body}\n}}\n");
        assert_eq!(check(&format!("{g}\n{f}"), &format!("{}\n{g}\n{f}", h("1"))), Vec::<String>::new());
        // ... and a second one is new.
        assert_eq!(check(&format!("{g}\n{f}"), &format!("{}\n{g}\n{f}", h("x"))).len(), 1);
        // Another code at the same place: new.
        assert_eq!(check(f, "pub fn f() -> I32 {\n  1.5\n}\n").len(), 1);
    }
}
