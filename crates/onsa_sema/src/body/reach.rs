//! What a statement drops and what is never carried out: the value of a
//! statement in a block (E0418, §6.1, S-127, S-848), what follows a statement
//! that diverges (E0503, §7, S-128, S-268) and a form that diverges in a part
//! that is always evaluated (E0503, S-291, S-889). The candidates that take
//! the rest of a block away ask [`Checker::may_end_here`] and are read in
//! [`super::reread`] (§18.1, S-876). The E0503 of an arm is in `arms.rs`.

use onsa_diag::Edit;
use onsa_diag::hash::HashMap;

use super::reread::Try;
use super::*;

const RETURN_ENDS_ITS_LINE: &str = "`return` ends at the end of its line; a value is written on the same line (§2.5)";

impl<'a> Checker<'a> {
    /// The block being checked: its node, itself and the item it is at.
    pub(super) fn open_block(&self) -> (ExprId, &'a Block, usize) {
        *self.blocks.last().unwrap()
    }

    /// The span of the item `k` of `b`, a statement or the last expression.
    fn item(&self, b: &Block, k: usize) -> Option<Span> {
        match b.stmts.get(k) {
            Some(&s) => Some(self.ast.stmt(s).span),
            None => b.tail.filter(|_| k == b.stmts.len()).map(|t| self.expr(t).span),
        }
    }

    /// The items of `b` after the statement `i`, from the first token of the
    /// next one: a comment at the end of the statement stays (§18.1).
    fn rest_of(&self, b: &Block, i: usize) -> Option<Span> {
        let (first, last) = (self.item(b, i + 1)?, self.item(b, b.stmts.len() - usize::from(b.tail.is_none()))?);
        Some(Span::new(first.file, first.start, last.end))
    }

    /// After a statement of the open block, with the deferred items of the
    /// statement seen: nothing follows one that diverges (§7), and the type
    /// of a statement's value is decided to be `()` by now, or it never is
    /// (no later statement is waited for, S-848). `expected` is the type of
    /// the block.
    pub(super) fn after_stmt(&mut self, expected: Option<TyId>) -> R<()> {
        let (_, b, i) = self.open_block();
        if self.info.diverging.stmt(self.ast, b.stmts[i]) {
            return match self.item(b, i + 1) {
                Some(next) => Err(self.unreached(next)),
                None => Ok(()),
            };
        }
        let StmtKind::Expr(e) = self.ast.stmt(b.stmts[i]).kind else { return Ok(()) };
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
        // `let _ = e` gives what is open nothing that decides it, and a
        // literal the type its default is (`5000000000` does not fit it).
        let literal = matches!(ty, Ty::Var(_));
        d = if self.infer.has_undefaulted_vars(&self.a.types, t) {
            let written = Some(self.src(span)).filter(|s| !s.contains('\n')).unwrap_or_else(|| "…".to_string());
            d.with_note(span, format!("discard it with its type written: `let _: T = {written}`"))
        } else if literal && !self.end_is_clean() {
            d
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
            // `x as T - y` is an E0011 of the syntax stage.
            ExprKind::Cast { .. } | ExprKind::At { .. } => false,
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
        let (end, x) = (self.expr(a).span.end, self.expr(x).span);
        decided.then(|| {
            self.join_edits("join it to the line before", end, at, Span::new(x.file, at.start + 1, x.end), " - ")
        })
    }

    /// The edits that bring `line`, an item, up to `end`, the end of the line
    /// before, with `lead` for all before `kept`, its end: the line break
    /// becomes `lead`, or with a comment in it, which stays where it is
    /// (§18.1, as `edits::move_up`), the item moves before that comment and
    /// takes its line with it.
    fn join_edits(&self, title: &str, end: u32, line: Span, kept: Span, lead: &str) -> Fix {
        let file = line.file;
        if self.src(Span::new(file, end, line.start)).trim().is_empty() {
            return Fix::replace(title, Span::new(file, end, kept.start), lead);
        }
        let (before, after) = (&self.text[..line.start as usize], &self.text[line.end as usize..]);
        let line_start = before.rfind('\n').map_or(0, |n| n + 1);
        let blanks = after.len() - after.trim_start_matches([' ', '\t', '\r']).len();
        let rest = line.end as usize + blanks;
        let removed = match after[blanks..].starts_with('\n') {
            true => Span::new(file, line_start as u32, rest as u32 + 1),
            false => Span::new(file, line.start, rest as u32),
        };
        let moved = self.src(kept);
        Fix::new(title, vec![Edit::insert(file, end, format!("{lead}{}", moved.trim_start())), Edit::delete(removed)])
    }

    /// E0503 at `next`, the item after the diverging statement the open
    /// block is at (§7, S-128): one in a body, as the check stops here
    /// (§18.1), so the candidate takes all the items after the statement.
    fn unreached(&mut self, next: Span) -> Stop {
        let (id, b, i) = self.open_block();
        let stmt = self.ast.stmt(b.stmts[i]);
        let msg = "this is never reached: the statement before it does not come back (§7)";
        let d = Diagnostic::new(Stage::Types, Code::E0503, next, msg).with_found(self.src(next));
        let mut d = d.with_note(stmt.span, "this does not come back");
        if matches!(stmt.kind, StmtKind::Return(None)) {
            d = d.with_note(stmt.span, RETURN_ENDS_ITS_LINE);
        }
        let mut tries = Vec::new();
        if let Some(rest) = self.rest_of(b, i).filter(|_| self.may_end_here()) {
            let (stmts, tail) = match stmt.kind {
                StmtKind::Expr(e) => (&b.stmts[..i], Some(e)),
                _ => (&b.stmts[..=i], None),
            };
            let patch = Patch::Block(id, Block { stmts: stmts.to_vec(), tail });
            tries.push(Try { fix: Fix::delete("remove what is never reached", rest), patch });
        }
        let ret = self.frames.last().unwrap().ret;
        if let Some(fix) = self.joined_return(ret) {
            d = d.with_fix(fix);
        }
        self.stop_with(d, tries)
    }

    /// E0503 at `binding`, of the `let` or `var` the open block is at, whose
    /// whole initializer `init` diverges (§7, S-268).
    pub(super) fn never_bound(&mut self, binding: Span, init: ExprId) -> Stop {
        let (id, b, i) = self.open_block();
        let value = self.expr(init).span;
        let msg = "this is never bound: its initializer does not come back (§7)";
        let d = Diagnostic::new(Stage::Types, Code::E0503, binding, msg).with_found(self.src(binding));
        let d = d.with_note(value, "this does not come back");
        let mut tries = Vec::new();
        if self.may_end_here() {
            let head = Span::new(value.file, self.ast.stmt(b.stmts[i]).span.start, value.start);
            let edits = [Some(head), self.rest_of(b, i)].into_iter().flatten().map(Edit::delete).collect();
            let patch = Patch::Block(id, Block { stmts: b.stmts[..i].to_vec(), tail: Some(init) });
            tries.push(Try { fix: Fix::new("keep the initializer as a statement", edits), patch });
        }
        self.stop_with(d, tries)
    }

    /// A `return` with no value, of the function that returns `ret`: E0401
    /// when that is not `()` (§7, S-886), which the line after it may mean
    /// to be the value of.
    pub(super) fn bare_return(&mut self, span: Span, ret: TyId) -> R<()> {
        let unit = self.unit();
        let Some(mut d) = self.mismatch_at(span, unit, ret) else { return Ok(()) };
        let (_, b, i) = self.open_block();
        if self.item(b, i + 1).is_some() {
            d = d.with_note(span, RETURN_ENDS_ITS_LINE);
        }
        if let Some(fix) = self.joined_return(ret) {
            d = d.with_fix(fix);
        }
        Err(self.diag(d))
    }

    /// The candidate that joins the `return` with no value the open block is
    /// at and its last expression `x` into `return x`, when `x` fits `ret`
    /// (§7, §2.5, S-886). No statement goes, so no type waits (S-876 is not
    /// asked), but the block now diverges.
    fn joined_return(&mut self, ret: TyId) -> Option<Fix> {
        let (id, b, i) = self.open_block();
        let stmt = self.ast.stmt(b.stmts[i]);
        let x = b.tail.filter(|_| i + 1 == b.stmts.len())?;
        let fits = self.makes_candidates()
            && matches!(stmt.kind, StmtKind::Return(None))
            && !self.info.diverging.expr(x)
            && self.stays_reached(id);
        if !fits {
            return None;
        }
        self.quietly(|ck| {
            ck.check_expr(x, Some(ret))?;
            ck.check_deferred_now()
        })?;
        let at = self.expr(x).span;
        Some(self.join_edits("join it to the `return`", stmt.span.end, at, at, " "))
    }

    /// Whether a candidate may end the open block at the item it is at, by
    /// its form (§18.1): none of the rest is the `break` that makes a loop
    /// come back (it would become a `while true` that diverges), and what is
    /// around the block is reached when the block diverges.
    fn may_end_here(&self) -> bool {
        let (id, b, i) = self.open_block();
        let breaks = b.stmts[i + 1..].iter().any(|&s| self.ast.stmt_leaves_loop(s))
            || b.tail.is_some_and(|t| self.ast.leaves_loop(t));
        self.makes_candidates() && !breaks && self.stays_reached(id)
    }

    /// Whether what is around the block `block` stays reached when it ends
    /// in a diverging form (`let k = { return 1` and `2 }` would be an E0503
    /// at `k`). Up the parents, a table made once for each candidate, linear
    /// in a body the error stops. What gives the block's end to its parent
    /// goes on up; a branch stops at one that comes back; the rest is a part
    /// of something, or an item with others after it, which it stops.
    pub(super) fn stays_reached(&self, block: ExprId) -> bool {
        let mut parents: HashMap<ExprId, ExprId> = HashMap::default();
        let mut todo = vec![self.root];
        while let Some(x) = todo.pop() {
            for c in self.ast.sub_exprs(x) {
                parents.insert(c, x);
                todo.push(c);
            }
        }
        let diverging = &self.info.diverging;
        let mut at = block;
        while let Some(&parent) = parents.get(&at) {
            match &self.expr(parent).kind {
                ExprKind::Paren(_) => {}
                ExprKind::Closure { .. } => return true,
                ExprKind::Block(b) if b.tail == Some(at) => {}
                ExprKind::Block(b) => return b.stmts.iter().any(|&s| self.is_loop_body(s, at)),
                ExprKind::If { then, else_, .. } if at == *then || Some(at) == *else_ => {
                    let other = if at == *then { *else_ } else { Some(*then) };
                    if !other.is_some_and(|x| diverging.expr(x)) {
                        return true;
                    }
                }
                ExprKind::Match { arms, .. } if arms.iter().any(|a| a.body == at) => {
                    if !arms.iter().all(|a| a.body == at || diverging.expr(a.body)) {
                        return true;
                    }
                }
                _ => return false,
            }
            at = parent;
        }
        true
    }

    fn is_loop_body(&self, s: StmtId, e: ExprId) -> bool {
        matches!(self.ast.stmt(s).kind, StmtKind::For { body, .. } | StmtKind::While { body, .. } if body == e)
    }

    /// Whether the end of the body has no error with what has been checked
    /// so far. A trial, as [`Checker::quietly`], which the end of the body
    /// leaves nothing in the tables of: what it decides and looks at is undone.
    pub(super) fn end_is_clean(&mut self) -> bool {
        if self.failed {
            return false;
        }
        let kept = (self.infer.clone(), self.deferred.clone(), self.deferred_end.clone());
        let mark = self.a.diagnostics.len();
        let clean = self.quietly(|ck| {
            ck.failed = false;
            ck.end_checks();
            if ck.failed { Err(Stop) } else { Ok(()) }
        });
        self.a.diagnostics.truncate(mark);
        (self.infer, self.deferred, self.deferred_end) = kept;
        clean.is_some()
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
