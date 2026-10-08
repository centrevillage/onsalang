//! Post-parse checks on operator chains (spec §3.1): E0010 (groups mixed or a
//! non-chaining group chained), E0011 (`as` as a bare operand), E0012 (stacked
//! prefix operators). Binary chains are kept flat by the parser, so each check
//! looks at one node.

use std::collections::HashSet;

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::ast::{Ast, ExprId, ExprKind};

pub(crate) fn check(ast: &Ast, text: &str, diagnostics: &mut Vec<Diagnostic>) {
    let src = |s: Span| &text[s.start as usize..s.end as usize];
    // A stack of prefix operators is one form (S-248, S-297): the operators
    // inside the outermost one of a stack are not reported again.
    let stacked = |e: ExprId| match ast.expr(e).kind {
        ExprKind::Unary { expr: inner, .. } => matches!(ast.expr(inner).kind, ExprKind::Unary { .. }),
        _ => false,
    };
    let inner_of_a_stack: HashSet<ExprId> = (0..ast.exprs.len() as u32)
        .map(ExprId)
        .filter(|&e| stacked(e))
        .filter_map(|e| match ast.expr(e).kind {
            ExprKind::Unary { expr: inner, .. } => Some(inner),
            _ => None,
        })
        .collect();
    for (i, expr) in ast.exprs.iter().enumerate() {
        match &expr.kind {
            ExprKind::Binary { operands, ops } => {
                // E0011: a cast must be parenthesized inside a chain.
                for &operand in operands {
                    let e = ast.expr(operand);
                    if matches!(e.kind, ExprKind::Cast { .. }) {
                        let d = Diagnostic::new(
                            Stage::Syntax,
                            Code::E0011,
                            e.span,
                            "`as` is written in parentheses when it is an operand (§3.3)",
                        )
                        .with_found(src(e.span))
                        .with_fix(Fix::replace(
                            "parenthesize the cast",
                            e.span,
                            format!("({})", src(e.span)),
                        ));
                        diagnostics.push(d);
                    }
                }
                let groups: Vec<_> = ops.iter().map(|(op, _)| op.group()).collect();
                if let Some(i) = (1..ops.len()).find(|&i| groups[i] != groups[i - 1]) {
                    // E0010: parenthesize the run of the operator that first differs.
                    let g = groups[i];
                    let mut j = i;
                    while j + 1 < ops.len() && groups[j + 1] == g {
                        j += 1;
                    }
                    let run_start = ast.expr(operands[i]).span.start;
                    let run_end = ast.expr(operands[j + 1]).span.end;
                    let replace = format!(
                        "{}({}){}",
                        &text[expr.span.start as usize..run_start as usize],
                        &text[run_start as usize..run_end as usize],
                        &text[run_end as usize..expr.span.end as usize]
                    );
                    let msg = format!(
                        "`{}` and `{}` are operators of different groups; parenthesize one of them (§3.1)",
                        ops[i - 1].0.symbol(),
                        ops[i].0.symbol()
                    );
                    let d = Diagnostic::new(Stage::Syntax, Code::E0010, expr.span, msg)
                        .with_found(src(expr.span))
                        .with_fix(Fix::replace(format!("parenthesize the `{}`", ops[i].0.symbol()), expr.span, replace))
                        .with_note(ops[i].1, "second group starts here".to_string());
                    diagnostics.push(d);
                } else if ops.len() >= 2 && !ops[0].0.chains() {
                    let op = ops[0].0;
                    let hint = if op.group() == crate::ast::OpGroup::Comparison {
                        "write `(a < b) && (b < c)`"
                    } else {
                        "parenthesize each step"
                    };
                    let msg = format!("`{}` cannot be chained; {hint} (§3.1)", op.symbol());
                    let d = Diagnostic::new(Stage::Syntax, Code::E0010, expr.span, msg).with_found(src(expr.span));
                    diagnostics.push(d);
                }
            }
            ExprKind::Unary { .. } if stacked(ExprId(i as u32)) && !inner_of_a_stack.contains(&ExprId(i as u32)) => {
                // The operators of the stack, outermost first: each but the
                // last takes the rest in parentheses (`- - -x` is
                // `-(-(-x))`); the blanks between two operators give way
                // to the `(`.
                let mut ops = vec![expr.span];
                let mut e = ExprId(i as u32);
                while let ExprKind::Unary { expr: inner, .. } = ast.expr(e).kind {
                    e = inner;
                    if matches!(ast.expr(inner).kind, ExprKind::Unary { .. }) {
                        ops.push(ast.expr(inner).span);
                    }
                }
                let mut edits = Vec::new();
                for w in ops.windows(2) {
                    let op_end = w[0].start + 1;
                    let between = Span::new(w[0].file, op_end, w[1].start);
                    if src(between).trim().is_empty() && !between.is_empty() {
                        edits.push(Edit::replace(between, "("));
                    } else {
                        edits.push(Edit::insert(w[0].file, op_end, "("));
                    }
                }
                edits.push(Edit::insert(expr.span.file, expr.span.end, ")".repeat(ops.len() - 1)));
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0012,
                    expr.span,
                    "prefix operators are not stacked; parenthesize the inner one (§3.1)",
                )
                .with_found(src(expr.span))
                .with_fix(Fix::new("parenthesize the inner operator", edits));
                diagnostics.push(d);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    /// The diagnostics of `let v = <src>`, and the expression after the
    /// first candidate of each.
    fn check(src: &str) -> Vec<(Code, Option<String>)> {
        let text = format!("fn f() {{\n  let v = {src}\n}}");
        let p = crate::parse(FileId(0), &text);
        p.diagnostics
            .iter()
            .map(|d| {
                let fix = d.fixes.first().map(|f| {
                    let edits: Vec<&onsa_diag::Edit> = f.edits().iter().collect();
                    let after = onsa_diag::apply_text(&text, &edits).unwrap();
                    after["fn f() {\n  let v = ".len()..after.len() - "\n}".len()].to_string()
                });
                (d.code, fix)
            })
            .collect()
    }

    #[test]
    fn same_group_chains_are_fine() {
        assert!(check("x + y - z").is_empty());
        assert!(check("x + (y * z)").is_empty());
        assert!(check("(lo <= x) && (x < hi)").is_empty());
        assert!(check("a && b && c").is_empty());
        assert!(check("a +% b -| c").is_empty());
        assert!(check("((1.0 - r) * x) + (b1 * y1) - (b2 * y2)").is_empty());
    }

    #[test]
    fn mixed_groups() {
        assert_eq!(check("x + y * z"), vec![(Code::E0010, Some("x + (y * z)".into()))]);
        assert_eq!(check("a * b + c * d"), vec![(Code::E0010, Some("a * (b + c) * d".into()))]);
        assert_eq!(check("lo <= x && x < hi"), vec![(Code::E0010, Some("lo <= (x && x) < hi".into()))]);
    }

    #[test]
    fn non_chaining_groups() {
        assert_eq!(check("a < b < c"), vec![(Code::E0010, None)]);
        assert_eq!(check("a & b | c"), vec![(Code::E0010, None)]);
        assert!(check("(a & b) | c").is_empty());
    }

    #[test]
    fn cast_as_operand() {
        assert_eq!(check("acc + x as F64"), vec![(Code::E0011, Some("acc + (x as F64)".into()))]);
        assert!(check("acc + (x as F64)").is_empty());
        assert!(check("-x as F64").is_empty());
    }

    #[test]
    fn stacked_prefix() {
        assert_eq!(check("- -x"), vec![(Code::E0012, Some("-(-x)".into()))]);
        assert_eq!(check("-!x"), vec![(Code::E0012, Some("-(!x)".into()))]);
        // One stack is one form, fixed whole (S-248, S-297).
        assert_eq!(check("- - -x"), vec![(Code::E0012, Some("-(-(-x))".into()))]);
        assert_eq!(check("!- !x"), vec![(Code::E0012, Some("!(-(!x))".into()))]);
        assert!(check("-(-x)").is_empty());
        assert!(check("-x.abs()").is_empty());
        // `--x` without a space is an increment of another language (S-250).
        assert_eq!(check("--x"), vec![(Code::E0002, None)]);
    }
}
