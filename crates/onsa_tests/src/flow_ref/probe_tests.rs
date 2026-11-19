//! The probe of the tables of the cases W1-09 holds back (W7-01 U2, the check of
//! the way 4 of the design memo): for each flow of the six cases, does
//! `BodyInfo::complete` hold, and which expressions of its body have no type in
//! the table? The evaluator reads the tables, so a flow of a case that the
//! check stops at (E0200) can be evaluated only if its body is complete.
//!
//! The expectations are of the tables of this version (W7-02 to W7-07 change
//! where the E0200 comes from): they fail when a work moves the tables, so that
//! the list of the cases the evaluator can take is read again.
//! When the person of W7-04 (or W7-06, W7-07) moves the tables and these numbers
//! fail, they are to be changed to the new tables.

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

/// The cases whose E0200 comes from the stage of the flow, after the body
/// (R-329), so every body is complete.
const COMPLETE_ONLY_AFTER_THE_BODY: [&str; 2] = ["par_branch.onsa", "branches_tilde.onsa"];

/// The cases with no E0200 left in their flows: `par_tilde_closed_range`
/// stopped at the E0200 of `par~ ..=` until W7-14 U3, `par_lookback` (where
/// the check of the body stopped) and `lookback_nesting` at the E0200 of
/// `^` in a `par~` and of a delay inside a delay until W7-07 U1, and
/// `prev_default_types` had the E0200 of the omitted `init` of a value type
/// that is no number, after the body, until W7-07 U2. No case of these has a
/// body the check stops at now.
const COMPLETE: [&str; 4] =
    ["par_tilde_closed_range.onsa", "par_lookback.onsa", "lookback_nesting.onsa", "prev_default_types.onsa"];

#[test]
fn the_complete_flows_have_a_type_for_every_value() {
    let mut complete_flows = 0;
    for case in COMPLETE.into_iter().chain(COMPLETE_ONLY_AFTER_THE_BODY) {
        for r in probe(case).iter().filter(|r| r.complete) {
            complete_flows += 1;
            assert_eq!(r.unresolved, 0, "{case}: {r:?}");
            assert!(r.holes.is_empty(), "{case}: {r:?}");
        }
    }
    // Six, two, eleven and four of the complete cases; 2 and 11 of the others.
    assert_eq!(complete_flows, 6 + 2 + 11 + 4 + 2 + 11);
}
