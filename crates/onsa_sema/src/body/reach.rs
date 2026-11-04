//! What a statement drops and what is never carried out: the value of a
//! statement in a block (E0418, §6.1, S-127, S-848) and a form that diverges
//! in a part that is always evaluated (E0503, §7, S-291, S-889).

use onsa_diag::Edit;

use super::*;

impl<'a> Checker<'a> {
    /// After the statement `i` of the block `b`, with the deferred items of
    /// the statement seen: the type of a statement's value is decided to be
    /// `()` by now, or it never is (no later statement is waited for, S-848).
    /// `expected` is the type of the block.
    pub(super) fn after_stmt(&mut self, b: &Block, i: usize, expected: Option<TyId>) -> R<()> {
        let StmtKind::Expr(e) = self.ast.stmt(b.stmts[i]).kind else { return Ok(()) };
        if self.info.diverging.expr(e) {
            return Ok(());
        }
        let t = self.shallow(self.info.expr_types[&e]);
        let ty = self.ty(t);
        if matches!(ty, Ty::Error) || t == self.unit() {
            return Ok(());
        }
        let span = self.expr(e).span;
        let msg = if matches!(ty, Ty::Var(_)) && self.infer.lit_of(&self.a.types, t).is_none() {
            "the type of this statement is not decided to be `()` here; a statement gives no value (§6.1)".to_string()
        } else {
            format!("the type of this statement is `{}`, not `()`; a statement gives no value (§6.1)", self.display(t))
        };
        let mut d = Diagnostic::new(Stage::Types, Code::E0418, span, msg).with_found(self.src(span));
        // `let _ = e` gives what is open nothing that decides it.
        d = if self.infer.has_undefaulted_vars(&self.a.types, t) {
            let written = Some(self.src(span)).filter(|s| !s.contains('\n')).unwrap_or_else(|| "…".to_string());
            d.with_note(span, format!("discard it with its type written: `let _: T = {written}`"))
        } else {
            d.with_fix(Fix::insert("discard the value with `let _`", span.file, span.start, "let _ = "))
        };
        if let Some(fix) = self.joined_line(b, i, t, expected) {
            d = d.with_fix(fix);
        }
        Err(self.diag(d))
    }

    /// The candidate that joins the statement `i` of `b`, a value `a` of type
    /// `t`, and the last expression `-x` of the block into `a - x` (§6.1,
    /// §2.5), when `a` is read as the left operand there and `a - x` fits.
    /// Of the forms that start with a `-`, only `-x` keeps its operand
    /// (`-x * y` would be another tree to check). The trial binds what it
    /// fits, and this body stops at the E0418 the candidate is for.
    fn joined_line(&mut self, b: &Block, i: usize, t: TyId, expected: Option<TyId>) -> Option<Fix> {
        let StmtKind::Expr(a) = self.ast.stmt(b.stmts[i]).kind else { return None };
        let last = b.tail.filter(|_| i + 1 == b.stmts.len())?;
        let ExprKind::Unary { op: UnOp::Neg, expr: x } = self.expr(last).kind else { return None };
        let on_the_left = match &self.expr(a).kind {
            ExprKind::If { .. } | ExprKind::Match { .. } | ExprKind::Block(_) => false,
            ExprKind::Binary { op, .. } => matches!(op.group(), OpGroup::Additive | OpGroup::Multiplicative),
            _ => true,
        };
        if !on_the_left {
            return None;
        }
        let at = self.expr(last).span;
        self.quietly(|ck| {
            if let Some(expected) = expected {
                ck.unify_at(at, t, expected)?;
            }
            ck.check_expr(x, Some(t))?;
            ck.require_op(OpNeed::Binary(BinOp::Sub), t, at)?;
            ck.check_deferred_now()
        })?;
        let decided = !self.infer.has_undefaulted_vars(&self.a.types, t);
        decided.then(|| self.join_edits(self.expr(a).span.end, at, self.expr(x).span))
    }

    /// The edits that bring `-x` at `minus` up to `end`, the end of the line
    /// before, as ` - x`: the line break becomes the operator, or with a
    /// comment in it, which stays where it is (§18.1, as `edits::move_up`),
    /// `x` moves before that comment and takes its line with it.
    fn join_edits(&self, end: u32, minus: Span, x: Span) -> Fix {
        let (title, file) = ("join it to the line before", minus.file);
        if self.src(Span::new(file, end, minus.start)).trim().is_empty() {
            return Fix::replace(title, Span::new(file, end, minus.start + 1), " - ");
        }
        let (before, after) = (&self.text[..minus.start as usize], &self.text[minus.end as usize..]);
        let line_start = before.rfind('\n').map_or(0, |n| n + 1);
        let blanks = after.len() - after.trim_start_matches([' ', '\t', '\r']).len();
        let rest = minus.end as usize + blanks;
        let removed = match after[blanks..].starts_with('\n') {
            true => Span::new(file, line_start as u32, rest as u32 + 1),
            false => Span::new(file, minus.start, rest as u32),
        };
        Fix::new(title, vec![Edit::insert(file, end, format!(" - {}", self.src(x))), Edit::delete(removed)])
    }

    /// The E0503 of the expression or statement at `span`, whose part `part`
    /// diverges (§7).
    pub(super) fn never_carried_out(&mut self, span: Span, part: ExprId) -> Stop {
        let msg = "this is never carried out: a part of it that is evaluated first leaves (§7)";
        let note = "this is evaluated first and does not come back";
        let d = Diagnostic::new(Stage::Types, Code::E0503, span, msg).with_found(self.src(span));
        self.diag(d.with_note(self.expr(part).span, note))
    }
}
