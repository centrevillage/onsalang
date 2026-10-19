//! The builds of a case's targets and the host sequences on them.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

use onsa_diag::FileId;
use onsa_driver::{Analyzed, BuildError, Loaded};

use crate::Expected;
use crate::case::{self, Case, Setup};
use crate::fragment::GoldenKind;
use crate::golden::{self, Update};

use super::markers::compare;
use super::{Built, CaseRun, Problem, Stage, StageFailure, Stages, stage_problem};

/// A host sequence that did not run, for a reason of the whole case.
pub(super) fn host_not_run(run: &mut CaseRun, h: &crate::host::Seq, why: &str) {
    run.problems.push(Problem::Failed(format!("host \"{}\" did not run: {why}", h.name)));
    run.hosts.push(crate::host::SeqResult {
        name: h.name.clone(),
        target: h.target.clone(),
        outcome: crate::host::Outcome::NotRun(why.into()),
    });
}

/// Run the host sequences on the builds of their targets (K-14).
pub(super) fn run_hosts(run: &mut CaseRun, seqs: &[crate::host::Seq]) {
    let mut targets: Vec<&str> = Vec::new();
    for s in seqs {
        if !targets.contains(&s.target.as_str()) {
            targets.push(&s.target);
        }
    }
    for target in targets {
        let mine: Vec<&crate::host::Seq> = seqs.iter().filter(|s| s.target == target).collect();
        let Some(built) = run.builds.iter().find(|b| b.target == target).cloned() else {
            for h in mine {
                host_not_run(run, h, &format!("target `{target}` did not build"));
            }
            continue;
        };
        let r = crate::host::run_target(target, &mine, &built.output);
        run.problems.extend(r.case_errors.into_iter().map(Problem::Case));
        run.problems.extend(r.failures.into_iter().map(Problem::Failed));
        run.problems.extend(r.harness.into_iter().map(Problem::Harness));
        run.notes.extend(r.notes);
        for res in r.results {
            let seq = mine.iter().find(|s| s.name == res.name);
            match &res.outcome {
                crate::host::Outcome::Passed { .. } => {}
                crate::host::Outcome::Failed(m) => run.problems.push(Problem::Host {
                    name: res.name.clone(),
                    message: format!(
                        "host \"{}\" (line {}, target {target}, {}):\n  {}",
                        res.name,
                        seq.map_or(0, |s| s.line),
                        seq.map_or_else(String::new, |s| s.callee()),
                        m.replace('\n', "\n  ")
                    ),
                }),
                crate::host::Outcome::NotRun(why) => {
                    run.problems.push(Problem::Failed(format!("host \"{}\" did not run: {why}", res.name)))
                }
            }
            run.hosts.push(res);
        }
    }
}

/// What the builds of a case share.
pub(super) struct BuildCtx<'a> {
    pub(super) stages: &'a Stages,
    pub(super) root: &'a Path,
    pub(super) case: &'a Case,
    pub(super) setup: &'a Setup,
    pub(super) loaded: &'a Loaded,
    pub(super) analyzed: &'a Analyzed,
    pub(super) markers: &'a [(FileId, Expected)],
}

/// Build one target, compare its diagnostics with the markers that apply to
/// it, and check what it produced.
pub(super) fn build_target(ctx: &BuildCtx<'_>, target: &str, update: Update, run: &mut CaseRun) {
    let BuildCtx { stages, root, case, setup, loaded, analyzed, markers } = *ctx;
    let t = &setup.test;
    let expected: Vec<(FileId, Expected)> = markers
        .iter()
        .filter(|(_, m)| m.targets.as_ref().is_none_or(|ts| ts.iter().any(|x| x == target)))
        .cloned()
        .collect();
    if !expected.is_empty() && (t.golden.contains(&GoldenKind::C) || t.conformance) {
        run.problems.push(Problem::Case(format!(
            "target `{target}` expects build diagnostics, but the case declares its golden C or conformance"
        )));
    }
    if !expected.is_empty() && t.host.iter().any(|h| h.target == target) {
        run.problems.push(Problem::Case(format!(
            "target `{target}` expects build diagnostics, but host sequences run on it ([[test.host]])"
        )));
    }
    let out = match (stages.build)(loaded, analyzed, target) {
        Ok(out) => {
            compare(run, &loaded.sources, &expected, &[], Stage::Build, Some(target));
            out
        }
        Err(BuildError::Diagnostics { diagnostics, sources }) => {
            compare(run, &loaded.sources, &expected, &diagnostics, Stage::Build, Some(target));
            run.problems.extend(crate::fix_contract::unchecked(&sources, &diagnostics));
            return;
        }
        Err(error) => {
            run.problems.push(stage_problem(&loaded.sources, StageFailure::Build { target, error: &error }));
            return;
        }
    };
    if !expected.is_empty() {
        return;
    }
    if t.golden.contains(&GoldenKind::C) {
        let [c, h] = golden::c_paths(&case.name, target);
        for (rel, actual) in [(c, out.unit.source.clone()), (h, crate::c::join_headers(&out.unit))] {
            if let Some(p) = golden::compare(root, &rel, &actual, update) {
                run.problems.push(Problem::Failed(p));
            }
        }
    }
    run.builds.push(Built { target: target.to_string(), output: Arc::new(out), conformance: t.conformance });
}

/// `conformance = true` covers every `pub flow` of the case: each is in
/// `[export] flows`, which is not empty.
pub(super) fn conformance_scope(run: &mut CaseRun, loaded: &Loaded, analyzed: &Analyzed) {
    let export = onsa_driver::ExportSettings::from_manifest(loaded.manifest.as_ref().and_then(|m| m.export.as_ref()));
    if export.flows.is_empty() {
        run.problems.push(Problem::Case("`conformance` needs `[export] flows`".into()));
        return;
    }
    let user: BTreeSet<FileId> = loaded.modules.iter().map(|(f, _)| *f).collect();
    let a = &analyzed.analysis;
    for (i, d) in a.defs.iter().enumerate() {
        if matches!(d.kind, onsa_sema::def::DefKind::Flow(_))
            && d.vis == onsa_syntax::ast::Vis::Pub
            && d.owner.is_none()
            && user.contains(&d.span.file)
        {
            let name = a.qualified_name(onsa_sema::DefId(i as u32));
            if !export.flows.contains(&name) {
                run.problems.push(Problem::Case(format!(
                    "`conformance` covers every `pub flow`, but `{name}` is not in `[export] flows`"
                )));
            }
        }
    }
}

/// Where each source file of the case is on disk (in the order of `loaded.modules`).
pub(super) fn disk_files(
    root: &Path,
    case: &Case,
    setup: &Setup,
    loaded: &Loaded,
) -> Vec<(FileId, std::path::PathBuf)> {
    loaded
        .modules
        .iter()
        .zip(&setup.input.files)
        .map(|((file, _), f)| {
            let p = match case.kind {
                case::CaseKind::File => root.join(&case.path),
                case::CaseKind::Package => root.join(&case.path).join(&f.path),
            };
            (*file, p)
        })
        .collect()
}
