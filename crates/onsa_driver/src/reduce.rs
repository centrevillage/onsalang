//! Reducing the diagnostics: the one place that decides which diagnostics a
//! command reports (S-59, plan §3.6 "診断を減らす処理 | driver の一か所").
//!
//! - [`per_unit`]: the check stages (syntax, names, types, ...) report the
//!   first diagnostic of each unit (spec §18.1). W3-03 makes the unit the
//!   declaration (S-59); until then it is the top-level item (P-01).
//! - [`exact`]: lowering and the build (code generation, layout, link) run
//!   only on units that passed the checks, so their diagnostics do not
//!   cascade: every one is reported, and only those with the same position,
//!   code and message are one (S-67, R-77). Diagnostics of the whole package
//!   or target (E1011, E0820, policies) go through it too, and so are never
//!   grouped into a declaration's unit.

use std::collections::{HashMap, HashSet};

use onsa_diag::{Diagnostic, FileId, Span};
use onsa_sema::Package;

/// The diagnostics of lowering and the build: every one, once (S-67), in
/// the order of their position.
pub fn exact(mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen: HashSet<(Span, onsa_diag::Code, String)> = HashSet::new();
    diagnostics.retain(|d| seen.insert((d.span, d.code, d.message.clone())));
    diagnostics.sort_by_key(|d| (d.span.file, d.span.start, d.span.end, d.code));
    diagnostics
}

/// P-01: one diagnostic per item. Parser diagnostics win over analysis
/// diagnostics for the same item; otherwise the earliest wins.
pub fn per_unit(pkg: &Package, sema: Vec<Diagnostic>) -> Vec<Diagnostic> {
    // Item spans of every user module, keyed by file.
    let mut items: HashMap<FileId, Vec<Span>> = HashMap::new();
    let mut out: Vec<Diagnostic> = Vec::new();
    let mut parser_items: HashSet<(FileId, usize)> = HashSet::new();
    for m in &pkg.modules {
        let spans: Vec<Span> = m.parsed.ast.root.iter().map(|&i| m.parsed.ast.item(i).span).collect();
        for d in &m.parsed.diagnostics {
            if let Some(i) = spans.iter().position(|s| s.contains(d.span.start) || (s.start == d.span.start)) {
                parser_items.insert((m.file, i));
            }
            out.push(d.clone());
        }
        items.insert(m.file, spans);
    }
    let mut best: HashMap<(FileId, usize), Diagnostic> = HashMap::new();
    for d in sema {
        let Some(spans) = items.get(&d.span.file) else {
            // Diagnostics inside `std` (none expected) are kept as is.
            out.push(d);
            continue;
        };
        match spans.iter().position(|s| s.contains(d.span.start) || s.start == d.span.start) {
            Some(i) => {
                if parser_items.contains(&(d.span.file, i)) {
                    continue;
                }
                let key = (d.span.file, i);
                let replace = best.get(&key).is_none_or(|b| d.span.start < b.span.start);
                if replace {
                    best.insert(key, d);
                }
            }
            None => out.push(d),
        }
    }
    out.extend(best.into_values());
    out.sort_by_key(|d| (d.span.file, d.span.start));
    out
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
        assert_eq!(got, [(3, Code::E0200, "a"), (9, Code::E0200, "a"), (9, Code::E0200, "b"), (9, Code::E0401, "a")]);
    }
}
