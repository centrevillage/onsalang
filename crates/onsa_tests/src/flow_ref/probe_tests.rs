//! The probe of the tables of the cases W1-09 holds back (W7-01 U2, the check of
//! the way 4 of the design memo): for each flow of the six cases, does
//! `BodyInfo::complete` hold, and which expressions of its body have no type in
//! the table? The evaluator reads the tables, so a flow of a case that the
//! check stops at (E0200) can be evaluated only if its body is complete.
//!
//! The expectations are of the tables of this version (W7-02 to W7-07 change
//! where the E0200 comes from): they fail when a work moves the tables, so that
//! the list of the cases the evaluator can take is read again.

use onsa_driver::{Loaded, PackageInput, analyze_loaded};
use onsa_sema::{DefKind, Ty};
use onsa_syntax::ast::{Ast, ExprId, ExprKind};
use onsa_syntax::dump::dump_expr;

use crate::case::repo_root;

/// The flow `name` of a case: `complete`, the expressions of its body, the ones
/// whose type is left a variable or an error, and the ones with no type in the
/// table (`holes`: not a callee of a call and not the type before the `.` of an
/// associated item, `F32.INFINITY`: those two are names, not values).
#[derive(Debug, PartialEq, Eq)]
struct Row {
    name: String,
    complete: bool,
    exprs: usize,
    unresolved: usize,
    holes: Vec<String>,
}

fn all_exprs(ast: &Ast, e: ExprId, out: &mut Vec<ExprId>) {
    out.push(e);
    for c in ast.sub_exprs(e) {
        all_exprs(ast, c, out);
    }
}

fn probe(case: &str) -> Vec<Row> {
    let path = repo_root().join("tests/spec/flow_semantics").join(case);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let name = case.to_string();
    onsa_diag::stack::run(move || {
        let mut loaded = Loaded::from_input(PackageInput::single_file(&name, &text)).expect("the input loads");
        let analyzed = analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let a = &analyzed.analysis;
        let mut rows = Vec::new();
        for module in &analyzed.pkg.modules {
            let m = a.module_of_file(module.file).expect("the module of a file");
            let ast = &module.parsed.ast;
            for (id, def) in a.defs_of_module(m) {
                let DefKind::Flow(fd) = &def.kind else { continue };
                let info = &a.flows[&id];
                let mut all = Vec::new();
                all_exprs(ast, fd.body, &mut all);
                let names: Vec<ExprId> = all
                    .iter()
                    .filter_map(|e| match &ast.expr(*e).kind {
                        ExprKind::Call { callee, .. } => Some(*callee),
                        ExprKind::Field { base, .. } => Some(*base),
                        _ => None,
                    })
                    .collect();
                let unresolved = all
                    .iter()
                    .filter_map(|e| info.body.expr_types.get(e))
                    .filter(|t| matches!(a.types.get(**t), Ty::Var(_) | Ty::Error))
                    .count();
                let holes = all
                    .iter()
                    .filter(|e| !info.body.expr_types.contains_key(e) && !names.contains(e))
                    .map(|e| dump_expr(ast, *e))
                    .collect();
                rows.push(Row {
                    name: def.name.clone(),
                    complete: info.body.complete,
                    exprs: all.len(),
                    unresolved,
                    holes,
                });
            }
        }
        rows
    })
}

const COMPLETE_ONLY_AFTER_THE_BODY: [&str; 3] = ["prev_default_types.onsa", "par_branch.onsa", "branches_tilde.onsa"];

/// (case, the number of its flows, the number of the incomplete ones): the check
/// of the body stops at the E0200 of `lookback_nesting`, `par_lookback` and
/// `par_tilde_closed_range` (their incomplete flows are the flows the check
/// stops at); the E0200 of the other three comes from the stage of the flow,
/// after the body, so every body is complete.
const BODY_STOPS: [(&str, usize, usize); 3] =
    [("lookback_nesting.onsa", 11, 11), ("par_lookback.onsa", 2, 2), ("par_tilde_closed_range.onsa", 6, 5)];

#[test]
fn the_cases_the_check_stops_at_in_the_body_have_incomplete_tables() {
    for (case, flows, incomplete) in BODY_STOPS {
        let rows = probe(case);
        assert_eq!(rows.len(), flows, "{case}: {rows:#?}");
        assert_eq!(rows.iter().filter(|r| !r.complete).count(), incomplete, "{case}: {rows:#?}");
    }
}

#[test]
fn the_complete_flows_have_a_type_for_every_value() {
    let mut complete_flows = 0;
    for case in BODY_STOPS.iter().map(|c| c.0).chain(COMPLETE_ONLY_AFTER_THE_BODY) {
        for r in probe(case).iter().filter(|r| r.complete) {
            complete_flows += 1;
            assert_eq!(r.unresolved, 0, "{case}: {r:?}");
            assert!(r.holes.is_empty(), "{case}: {r:?}");
        }
    }
    // `par_tilde_closed_range` has one complete flow; the three others have 4, 2 and 11.
    assert_eq!(complete_flows, 1 + 4 + 2 + 11);
}
