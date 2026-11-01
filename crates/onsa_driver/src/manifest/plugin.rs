//! The `flow` of each `[[plugin]]` (§15.3, S-718): its path resolved once
//! after the analysis, and the E0320 of the names it names (§2.3).

use std::collections::HashMap;

use onsa_diag::{Code, Diagnostic, Note, Span};
use onsa_sema::def::DefKind;
use onsa_sema::{Analysis, DefId, Package};

/// The path a `flow` of a `[[plugin]]` writes, and the place of its value.
pub(crate) type PluginFlow = (String, Span);

/// The flow of the package itself each path names, by its qualified name
/// (`dsp.voice.lp`, as `onsa graph` reads one): none when it names none
/// (the E1103 of S-641, at M10). The table of the paths is made once.
pub(crate) fn resolve(a: &Analysis, flows: &[PluginFlow]) -> Vec<Option<DefId>> {
    if flows.is_empty() {
        return Vec::new();
    }
    // The package itself is the last of `flatten` (R-88).
    let own = a.modules.names.len() - 1;
    // Of two flows of a path (the later an E0305), the first, as `onsa graph`.
    let mut by_path: HashMap<String, DefId> = HashMap::new();
    for d in (0..a.defs.len() as u32).map(DefId) {
        if matches!(a.def(d).kind, DefKind::Flow(_)) && a.modules.pkg_of(a.def(d).module) == own {
            by_path.entry(a.qualified_name(d)).or_insert(d);
        }
    }
    flows.iter().map(|(path, _)| by_path.get(path).copied()).collect()
}

/// The E0320 of the names a `[[plugin]]` names (§2.3, S-718), before the
/// candidates of the E0320 are made: that of its flow (in `ds`, at the
/// name) loses its candidate, which edits the sources only; that of a module
/// on its path (in `paths`, with the module path its name ends) has none.
/// Each has a note at the `flow` of the manifest, with the name by the rule.
pub(crate) fn note_named(
    a: &Analysis,
    pkg: &Package,
    flows: &[PluginFlow],
    resolved: &[Option<DefId>],
    ds: &mut [Diagnostic],
    paths: &mut [(Diagnostic, Vec<String>)],
) {
    for ((_, at), d) in flows.iter().zip(resolved) {
        let Some(def) = d.map(|d| a.def(d)) else { continue };
        let note = |what: &str, to: Option<String>| {
            let to = to.map_or(String::new(), |t| format!(", to `{t}`"));
            let message =
                format!("the `flow` of a `[[plugin]]` names {what} here (§2.3, §15.3): rename it there too{to}");
            Note::at(*at, message)
        };
        for e in ds.iter_mut().filter(|e| e.code == Code::E0320 && e.span == def.name_span) {
            let to = e.fixes.first().map(|f| f.edits()[0].replace.clone());
            e.fixes.clear();
            e.notes.push(note("this flow", to));
        }
        let Some(segments) = a.modules.get(def.module).module.map(|i| &pkg.modules[i].segments) else { continue };
        let on_path = |m: &Vec<String>| !m.is_empty() && segments.starts_with(m);
        for (e, m) in paths.iter_mut().filter(|(e, m)| e.code == Code::E0320 && on_path(m)) {
            e.notes.push(note("this module", m.last().and_then(|n| onsa_syntax::module_name_by_rule(n))));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Analyzed, Loaded, ManifestForm, ManifestSource, PackageInput, SourceFile};

    const FLOWS: &str = "pub flow MyFlow(x: F32 at sample) -> F32 at sample {\n  x\n}\n\n\
                         pub flow Other(x: F32 at sample) -> F32 at sample {\n  MyFlow(x)\n}\n";

    /// The package of `files` whose one `[[plugin]]` names `flow`, analyzed.
    fn analyzed(flow: &str, files: &[(&str, &str)]) -> (Loaded, Analyzed) {
        let text = format!(
            "[package]\nname = \"p\"\nedition = \"2026\"\n\n[[plugin]]\nflow = \"{flow}\"\nid = \"i\"\nname = \"N\"\n\
             vendor = \"V\"\nversion = \"1.0.0\"\ncategory = \"effect\"\n"
        );
        let manifest = ManifestSource { path: "onsa.toml".into(), text, form: ManifestForm::File };
        let files = files.iter().map(|(p, t)| SourceFile { path: p.to_string(), text: t.to_string() }).collect();
        let input = PackageInput { manifest: Some(manifest), files, ..PackageInput::default() };
        let mut loaded = Loaded::from_input(input).unwrap();
        let analyzed = crate::analyze_loaded(&mut loaded).unwrap();
        (loaded, analyzed)
    }

    /// For each E0320, the text it names (the file string for an empty span),
    /// its candidates, and the texts of the places of its notes.
    fn e0320(loaded: &Loaded, a: &Analyzed) -> Vec<(String, usize, Vec<String>)> {
        let text =
            |s: onsa_diag::Span| loaded.sources.file(s.file).text()[s.start as usize..s.end as usize].to_string();
        let mut out: Vec<_> = (a.diagnostics.iter().filter(|d| d.code == onsa_diag::Code::E0320))
            .map(|d| {
                let at = if d.span.is_empty() { d.message.clone() } else { text(d.span) };
                let notes = d.notes.iter().filter_map(|n| n.span.map(|s| format!("{}: {}", text(s), n.message)));
                (at, d.fixes.len(), notes.collect())
            })
            .collect();
        out.sort();
        out
    }

    /// Of two flows of the path a `[[plugin]]` names (the later an E0305),
    /// the first is the one named, as `onsa graph` reads a path.
    #[test]
    fn of_two_flows_of_a_path_the_first_is_named() {
        let src = "pub flow Bad(x: F32 at sample) -> F32 at sample {\n  x\n}\n\n\
                   pub flow Bad(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
        let (loaded, a) = analyzed("m.Bad", &[("m.onsa", src)]);
        let named = a.plugin_flows[0].map(|d| a.analysis.def(d).name_span).unwrap();
        let first = a.diagnostics.iter().find(|d| d.code == onsa_diag::Code::E0320).unwrap();
        assert_eq!((first.span, first.fixes.len()), (named, 0));
        assert_eq!(loaded.sources.file(named.file).text()[..named.start as usize].matches('\n').count(), 0);
    }

    const NOTE: &str = "the `flow` of a `[[plugin]]` names this flow here (§2.3, §15.3): rename it there too";

    /// §2.3, S-718: the E0320 of the flow a `[[plugin]]` names has no
    /// candidate (it would edit the sources only) and a note at the `flow`
    /// of the manifest, with the name by the rule; a flow it does not name
    /// keeps its candidate.
    #[test]
    fn the_e0320_of_a_flow_a_plugin_names_has_a_note_and_no_candidate() {
        let (loaded, a) = analyzed("m.MyFlow", &[("m.onsa", FLOWS)]);
        let note = format!("\"m.MyFlow\": {NOTE}, to `my_flow`");
        assert_eq!(e0320(&loaded, &a), [("MyFlow".to_string(), 0, vec![note]), ("Other".to_string(), 1, vec![])]);
        let toml = loaded.toml_file().unwrap();
        let d = a.diagnostics.iter().find(|d| d.found.as_deref() == Some("MyFlow")).unwrap();
        assert_eq!(d.notes.last().unwrap().span.unwrap().file, toml);
        assert_eq!(
            a.plugin_flows.iter().map(|d| d.map(|d| a.analysis.def(d).name.as_str())).collect::<Vec<_>>(),
            [Some("MyFlow")]
        );
    }

    /// S-718: the E0320 of each module on the path a `[[plugin]]` names (a
    /// directory, a file: no candidate of their own) has the note, with the
    /// name by the rule; a module off the path has none.
    #[test]
    fn the_e0320_of_a_module_on_the_path_has_a_note() {
        let flow = "pub flow lp(x: F32 at sample) -> F32 at sample {\n  x\n}\n";
        let (loaded, a) =
            analyzed("Dsp.Voice.lp", &[("Dsp/Voice.onsa", flow), ("Dsp/Off.onsa", flow), ("Odd/a.onsa", flow)]);
        let module = |n: &str| {
            format!(
                "\"Dsp.Voice.lp\": the `flow` of a `[[plugin]]` names this module here (§2.3, §15.3): rename it there too, to `{n}`"
            )
        };
        let found = e0320(&loaded, &a);
        let named: Vec<(&str, &[String])> =
            found.iter().map(|(at, _, notes)| (at.split('`').nth(1).unwrap_or(at), notes.as_slice())).collect();
        assert_eq!(
            named,
            [("Dsp", &[module("dsp")][..]), ("Odd", &[][..]), ("Off", &[][..]), ("Voice", &[module("voice")][..])]
        );
    }

    /// S-718: a path that names no flow of the package (S-641's E1103, at
    /// M10) changes no E0320.
    #[test]
    fn a_path_that_names_no_flow_changes_nothing() {
        for flow in ["m.missing", "MyFlow", "m", "m.MyFlow.x", "std.math.sqrt"] {
            let (loaded, a) = analyzed(flow, &[("m.onsa", FLOWS)]);
            assert_eq!(
                e0320(&loaded, &a),
                [("MyFlow".to_string(), 1, vec![]), ("Other".to_string(), 1, vec![])],
                "{flow}"
            );
            assert_eq!(a.plugin_flows, [None], "{flow}");
        }
    }
}
