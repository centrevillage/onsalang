//! Post-parse checks on operator chains (spec §3.1): E0010 (groups mixed or a
//! non-chaining group chained), E0011 (`as` as a bare operand), E0012 (stacked
//! prefix operators). Binary chains are kept flat by the parser, so each check
//! looks at one node.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};

use crate::ast::{Ast, ExprKind, UnOp};

pub(crate) fn check(ast: &Ast, text: &str, diagnostics: &mut Vec<Diagnostic>) {
    let src = |s: Span| &text[s.start as usize..s.end as usize];
    for expr in &ast.exprs {
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
            ExprKind::Unary { op, expr: inner } if matches!(ast.expr(*inner).kind, ExprKind::Unary { .. }) => {
                let inner_span = ast.expr(*inner).span;
                let sym = match op {
                    UnOp::Neg => "-",
                    UnOp::Not => "!",
                };
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0012,
                    expr.span,
                    "prefix operators are not stacked; parenthesize the inner one (§3.1)",
                )
                .with_found(src(expr.span))
                .with_fix(Fix::replace(
                    "parenthesize the inner operator",
                    expr.span,
                    format!("{sym}({})", src(inner_span)),
                ));
                diagnostics.push(d);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    fn check(src: &str) -> Vec<(Code, Option<String>)> {
        let p = crate::parse(FileId(0), &format!("fn f() {{\n  let v = {src}\n}}"));
        p.diagnostics
            .iter()
            .map(|d| {
                let fix = d.fixes.first().map(|f| f.edits()[0].replace.clone());
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
        assert_eq!(check("acc + x as F64"), vec![(Code::E0011, Some("(x as F64)".into()))]);
        assert!(check("acc + (x as F64)").is_empty());
        assert!(check("-x as F64").is_empty());
    }

    #[test]
    fn stacked_prefix() {
        assert_eq!(check("--x"), vec![(Code::E0012, Some("-(-x)".into()))]);
        assert_eq!(check("-!x"), vec![(Code::E0012, Some("-(!x)".into()))]);
        assert!(check("-(-x)").is_empty());
        assert!(check("-x.abs()").is_empty());
    }
}
