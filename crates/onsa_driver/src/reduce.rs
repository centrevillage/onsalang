//! Reducing the diagnostics: the one place that decides which diagnostics a
//! command reports (S-59, plan §3.6 "診断を減らす処理 | driver の一か所").
//!
//! - [`per_unit`]: the check stages (syntax, names, types, ...) report one
//!   diagnostic for each unit (spec §18.1). The units are the declarations
//!   (`onsa_syntax::units`, made once by the parse); this module puts the
//!   units of the files of a package in one table and chooses in each unit
//!   the diagnostic of the earliest stage of [`Stage::CHECK_ORDER`], then the
//!   first in the text (S-214).
//! - [`syntax_report`]: what `fmt` and `diff --ast` report for a file the
//!   syntax stage fails: the same choice, of which the syntax ones
//!   (`docs/onsa-tools.md` §3.1).
//! - [`exact`]: lowering and the build (code generation, layout, link) run
//!   only on units that passed the checks, so their diagnostics do not
//!   cascade: every one is reported, and only those with the same position,
//!   code and message are one (S-67, R-77). Diagnostics of the whole package
//!   or target (E1011, E0820, policies) go through it too, and so are never
//!   grouped into a declaration's unit.
//!
//! None of them orders its output: the order of the diagnostics is decided
//! once, where they are rendered (`onsa_diag::to_json`, `onsa_diag::to_text`,
//! S-234).

use std::collections::{HashMap, HashSet};

use onsa_diag::{Diagnostic, FileId, Span, Stage};
use onsa_syntax::units::Units;

/// One unit of the package's table (spec §18.1): the tests read it to know
/// which units an edit touches (W3-17, D-15).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unit {
    pub span: Span,
    /// The unit of the `impl`, `trait`, ... of a member.
    pub parent: Option<usize>,
}

/// The diagnostics a command reports and the units of the package.
#[derive(Debug, Clone, Default)]
pub struct Reduced {
    pub diagnostics: Vec<Diagnostic>,
    /// For each of `diagnostics`, its unit in `units` (`None` for one outside
    /// every unit, reported as it is).
    pub diagnostic_units: Vec<Option<usize>>,
    pub units: Vec<Unit>,
}

/// The diagnostics of lowering and the build: every one, once (S-67).
pub fn exact(mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen: HashSet<(Span, onsa_diag::Code, String)> = HashSet::new();
    diagnostics.retain(|d| seen.insert((d.span, d.code, d.message.clone())));
    diagnostics
}

/// One diagnostic for each unit of the files `files` (spec §18.1, S-59,
/// S-214). A diagnostic of a member goes to the unit of its `impl` (`trait`,
/// ...) when the heading of the item (up to the `{` of its members) has one: a
/// heading with an error makes the whole item one unit. A diagnostic of the
/// item outside its heading and its members (a `;` after its `}`, S-254) is
/// the item's own and does not take its members. In a unit, the diagnostic of the earliest check stage
/// is reported, and among those the first in the text. A diagnostic outside
/// every unit (another file, `std`, no check stage) is reported as it is.
pub fn per_unit<'a>(files: impl IntoIterator<Item = (FileId, &'a Units)>, diagnostics: Vec<Diagnostic>) -> Reduced {
    let mut units: Vec<Unit> = Vec::new();
    let mut tables: Vec<&onsa_syntax::units::Unit> = Vec::new();
    let mut of_file: HashMap<FileId, (usize, &Units)> = HashMap::new();
    for (file, table) in files {
        let offset = units.len();
        units.extend(table.list.iter().map(|u| Unit { span: u.span, parent: u.parent.map(|p| p + offset) }));
        tables.extend(table.list.iter());
        of_file.insert(file, (offset, table));
    }
    let mut assigned: Vec<Option<usize>> = diagnostics
        .iter()
        .map(|d| {
            d.stage.check_rank()?;
            let (offset, table) = of_file.get(&d.span.file)?;
            table.of(d.span).map(|u| u + offset)
        })
        .collect();
    // A diagnostic of the heading of an item with members (from its start to
    // the `{` of its members): the whole item is then one unit (§18.1).
    let mut heading_error = vec![false; units.len()];
    for (d, a) in diagnostics.iter().zip(&assigned) {
        if let Some(u) = *a
            && tables[u].heading_holds(d.span.start)
        {
            heading_error[u] = true;
        }
    }
    for a in assigned.iter_mut() {
        if let Some(u) = *a
            && let Some(p) = units[u].parent
            && heading_error[p]
        {
            *a = Some(p);
        }
    }
    // The earliest stage, then the first in the text.
    // SPEC-GAP(S-281): among diagnostics of one stage that start at the same
    // place, the one found first (the lexer's before the parser's: the E0020 of
    // `1.` before the E0002 at it), as before W3-03, until S-281 is decided.
    let key = |i: usize| (diagnostics[i].stage.check_rank().unwrap_or(usize::MAX), diagnostics[i].span.start, i);
    let mut best: Vec<Option<usize>> = vec![None; units.len()];
    for (i, a) in assigned.iter().enumerate() {
        if let Some(u) = *a
            && best[u].is_none_or(|b| key(i) < key(b))
        {
            best[u] = Some(i);
        }
    }
    let chosen: HashSet<usize> = best.iter().flatten().copied().collect();
    let mut out = Reduced { units, ..Reduced::default() };
    for (i, d) in diagnostics.into_iter().enumerate() {
        if assigned[i].is_none() || chosen.contains(&i) {
            out.diagnostics.push(d);
            out.diagnostic_units.push(assigned[i]);
        }
    }
    out
}

/// What `fmt` and `diff --ast` report for a file with a diagnostic of the
/// syntax stage: `check`'s choice of one diagnostic per unit, of which those of
/// the syntax stage (`docs/onsa-tools.md` §3.1; a naming error E0320 does not
/// stop them, and is not reported).
pub fn syntax_report(parsed: &onsa_syntax::Parsed, file: FileId) -> Vec<Diagnostic> {
    let reduced = per_unit([(file, &parsed.units)], parsed.diagnostics.clone());
    reduced.diagnostics.into_iter().filter(|d| d.stage == Stage::Syntax).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use onsa_diag::{Code, Stage};

    fn d(start: u32, code: Code, message: &str) -> Diagnostic {
        Diagnostic::new(Stage::Types, code, Span::new(FileId(0), start, start + 1), message.to_string())
    }

    #[test]
    fn exact_keeps_every_distinct_diagnostic_once() {
        let out = exact(vec![
            d(9, Code::E0200, "a"),
            d(3, Code::E0200, "a"),
            d(9, Code::E0200, "a"), // the same: one
            d(9, Code::E0200, "b"), // another message: kept
            d(9, Code::E0401, "a"), // another code: kept
        ]);
        let got: Vec<(u32, Code, &str)> = out.iter().map(|d| (d.span.start, d.code, d.message.as_str())).collect();
        assert_eq!(got, [(9, Code::E0200, "a"), (3, Code::E0200, "a"), (9, Code::E0200, "b"), (9, Code::E0401, "a")]);
    }

    fn reduced(src: &str, extra: Vec<Diagnostic>) -> Vec<(u32, Code)> {
        let parsed = onsa_syntax::parse(FileId(0), src);
        let mut all = parsed.diagnostics.clone();
        all.extend(extra);
        let r = per_unit([(FileId(0), &parsed.units)], all);
        assert_eq!(r.diagnostics.len(), r.diagnostic_units.len());
        let mut out: Vec<(u32, Code)> = r.diagnostics.iter().map(|d| (d.span.start, d.code)).collect();
        out.sort();
        out
    }

    #[test]
    fn the_earliest_stage_wins_in_a_unit_wherever_it_is() {
        // E0320 (names) on the heading, E0010 (syntax) later: the syntax one.
        let src = "fn f(badName: I32) -> I32 {\n  1 + 2 * 3 % 4\n}\n";
        let got = reduced(src, Vec::new());
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].1, Code::E0010);
        // A type error before a name error of the same unit: the name error.
        let src = "fn g() -> I32 {\n  let x: Bool = 1\n  missing\n}\n";
        let ty = Diagnostic::new(Stage::Types, Code::E0401, Span::new(FileId(0), 18, 19), "t");
        let name = Diagnostic::new(Stage::Names, Code::E0302, Span::new(FileId(0), 36, 37), "n");
        assert_eq!(reduced(src, vec![ty, name]), vec![(36, Code::E0302)]);
    }

    #[test]
    fn a_heading_with_a_diagnostic_takes_the_diagnostics_of_its_members() {
        let src = "impl Missing {\n  fn a(self) -> I32 {\n    1\n  }\n}\n";
        let heading = Diagnostic::new(Stage::Names, Code::E0302, Span::new(FileId(0), 5, 12), "h");
        let member = Diagnostic::new(Stage::Types, Code::E0401, Span::new(FileId(0), 40, 41), "m");
        assert_eq!(reduced(src, vec![member.clone(), heading]), vec![(5, Code::E0302)]);
        // Without a diagnostic of the heading, the member is a unit of its own.
        assert_eq!(reduced(src, vec![member.clone()]), vec![(40, Code::E0401)]);
        // A diagnostic of the item after its members (a `;` after its `}`, S-254) is not of the
        // heading: the members stay units of their own.
        let src = "impl Missing {\n  fn a(self) -> I32 {\n    1\n  }\n};\n";
        let got = reduced(src, vec![member]);
        assert_eq!(got.iter().map(|g| g.1).collect::<Vec<_>>(), [Code::E0401, Code::E0020]);
    }

    #[test]
    fn an_unclosed_brace_of_the_members_does_not_take_them() {
        // W3-03/b N-2: the E0002 at the `{` is the item's own, and each member keeps its own.
        let src = "impl S {\n  fn a(self) -> I32 { 1 }\n  fn b(self) -> I32 { missing }\n";
        let at = src.find("missing").unwrap() as u32;
        let member = Diagnostic::new(Stage::Names, Code::E0302, Span::new(FileId(0), at, at + 7), "m");
        let got = reduced(src, vec![member]);
        assert_eq!(got.iter().map(|g| g.1).collect::<Vec<_>>(), [Code::E0002, Code::E0302]);
    }

    #[test]
    fn of_one_stage_at_one_place_the_one_found_first() {
        // SPEC-GAP(S-281): the lexer's E0020 of `1.` before the parser's E0002 at it.
        assert_eq!(reduced("1.\n", Vec::new()), vec![(0, Code::E0020)]);
    }
}
