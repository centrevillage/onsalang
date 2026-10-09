//! The rows of the flow syntax (W3-09): the `~` of `if~` / `match~` with a
//! blank (S-354), the `~` on a later `if` of a chain (S-355), and the clocks
//! written on a binding or in a type (S-102, S-356).

use onsa_diag::{Diagnostic, Edit, Fix, Span};

use super::{Cursor, Hit, RowId, Want, bit_not, diagnostic, hit};
use crate::cst::{Cst, NodeId, NodeKind, TokenIdx};
use crate::lower::{Class, class};
use crate::token::{Gap, TokenKind};

// ------------------------------------------------------------ `if~`, `match~`

/// Where an `if` or a `match` stands whose `~` the parser failed at
/// ([`Cursor::branch`]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Branch {
    /// A `match`, or the first `if` of a chain: its `~` is the mark of
    /// `match~` / `if~` (§2.6).
    First,
    /// The `if` after an `else`: a later link of the chain of the first `if`
    /// (§11.5).
    Later,
}

impl Cursor<'_> {
    /// The place of the keyword at token `kw` when the parser failed right
    /// after it, in the expression it opened: the one judgment of the table
    /// of whether a `~` after `kw` belongs to `if~` / `match~` (S-354, S-355).
    /// The parser opens the node of an `if` or a `match` at the keyword (the
    /// `if` of a guard opens none, so it is no branch: its `~` is the prefix
    /// `~` of `faust_bit_not`), and reads the `if` after an `else` as the
    /// later link of the same chain (`Parser::parse_if`).
    pub(super) fn branch(&self, kw: usize) -> Option<Branch> {
        let k = self.open.len().checked_sub(1)?;
        let (node, start) = self.open[k];
        if start != self.span(kw).start {
            return None;
        }
        match (node, self.kind(kw)) {
            (NodeKind::MatchExpr, TokenKind::KwMatch) => Some(Branch::First),
            (NodeKind::IfExpr, TokenKind::KwIf) if self.later_link(k) => Some(Branch::Later),
            (NodeKind::IfExpr, TokenKind::KwIf) => Some(Branch::First),
            _ => None,
        }
    }

    /// The open `if` node `k` is the `if` after the `else` of the open `if`
    /// node around it.
    fn later_link(&self, k: usize) -> bool {
        k > 0
            && self.open[k - 1].0 == NodeKind::IfExpr
            && self.sig_before(self.index_at(self.open[k].1)).is_some_and(|e| self.kind(e) == TokenKind::KwElse)
    }

    /// The first `if` of the chain of the open `if` node `k`.
    fn chain_head(&self, mut k: usize) -> usize {
        while self.later_link(k) {
            k -= 1;
        }
        self.index_at(self.open[k].1)
    }
}

/// `if ~ c`, `if ~c`, `match ~ x` (S-354): the `~` of the first `if` of a
/// chain, or of a `match`, after a blank on the line. The first candidate
/// takes the blank out (`if~ c`); a `~` that touches its operand is also the
/// bitwise negation of C, whose candidate (`if !c`) is the second.
pub(super) fn space_after_branch_keyword(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr || c.kind(c.at) != TokenKind::Tilde || c.gap(c.at) != Gap::Space {
        return None;
    }
    let kw = c.before(c.at)?;
    if c.branch(kw) != Some(Branch::First) {
        return None;
    }
    let mut edits = vec![Edit::delete(c.space_before(c.at)?)];
    if c.gap(c.at + 1) == Gap::None {
        edits.push(Edit::insert(c.file, c.span(c.at).end, " "));
    }
    let mut fixes = vec![Fix::new(format!("write `{}~`", c.src(kw)), edits)];
    fixes.extend(bit_not(c).unwrap_or_default());
    hit(c.span(c.at), fixes)
}

/// `else if~ d` (S-355): a `~` on a later `if` of a chain. The candidate takes
/// it out when the first `if` has one, else moves it to the first `if`; a
/// `~` that touches its operand has the bitwise negation as the second.
pub(super) fn else_if_tilde(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Expr || c.kind(c.at) != TokenKind::Tilde || c.gap(c.at) == Gap::Newline {
        return None;
    }
    let kw = c.before(c.at)?;
    if c.branch(kw) != Some(Branch::Later) {
        return None;
    }
    let head = c.chain_head(c.open.len() - 1);
    // The blanks around the `~` become one blank between `if` and the condition.
    let next = c.at + 1;
    let out = if matches!(c.kind(next), TokenKind::Newline | TokenKind::Eof) {
        Edit::delete(c.span(c.at))
    } else {
        Edit::replace(c.file_span(c.span(kw).end, c.span(next).start), " ")
    };
    let head_tilde = c.kind(head + 1) == TokenKind::Tilde && c.gap(head + 1) == Gap::None;
    let fix = if head_tilde {
        Fix::new("remove the `~`", vec![out])
    } else {
        Fix::new("write the `~` on the first `if`", vec![Edit::insert(c.file, c.span(head).end, "~"), out])
    };
    let mut fixes = vec![fix];
    fixes.extend(bit_not(c).unwrap_or_default());
    hit(c.span(c.at), fixes)
}

// ------------------------------------------------------------ clocks

/// The clocks the parser read where no clock goes (§11.3): on the type of a
/// `let` or `var` (`clock_on_binding`), and in a type or after the type of
/// a declaration that is no input or output (`clock_in_type`, S-356). Each
/// clock is an error of its own (one type may hold several). A clock whose
/// node, or the node its candidate reads, a syntax error left unfinished is
/// not reported: that error is the unit's. `deepest` is the deepest unit of
/// the file in levels (spec §2.5): no candidate goes over the limit.
pub(crate) fn clocks(cst: &Cst, text: &str, deepest: u32, out: &mut Vec<Diagnostic>) {
    for (i, t) in cst.tokens().iter().enumerate() {
        if t.kind != TokenKind::KwAt {
            continue;
        }
        let clock = cst.token_parent(TokenIdx(i as u32));
        if cst.kind(clock) != NodeKind::Clock || !cst.is_complete(clock) {
            continue;
        }
        let Some(parent) = cst.parent(clock) else { continue };
        let found = match cst.kind(parent) {
            NodeKind::AtExpr | NodeKind::Param | NodeKind::Fn | NodeKind::Flow | NodeKind::ClosureExpr => None,
            NodeKind::LetStmt | NodeKind::VarStmt => {
                to_value(cst, text, clock, parent).map(|fixes| (RowId::ClockOnBinding, fixes))
            }
            _ => in_type(cst, text, clock).map(|fixes| (RowId::ClockInType, fixes)),
        };
        let Some((id, fixes)) = found else { continue };
        // A candidate that would nest deeper than the limit is not made
        // (§18.1): the note says how to split the form.
        let span =
            cst.ancestors(clock).find(|&a| cst.kind(a) == NodeKind::Item).map_or(cst.span(clock), |a| cst.span(a));
        let too_deep = fixes.iter().any(|f| {
            let added = f.edits().iter().map(|e| e.replace.matches('(').count() as u32).sum::<u32>() + 1;
            crate::groups::nests_too_deep(text, span, f.edits(), added, deepest)
        });
        let fixes = if too_deep { Vec::new() } else { fixes };
        let d = diagnostic(text, id, Hit { span: cst.span(clock), fixes, misplaced: false });
        out.push(if too_deep { d.with_rule(crate::groups::TOO_DEEP_RULE) } else { d });
    }
}

/// The text a clock is written with after a value or a type: ` at name`,
/// from its name token.
fn clock_text(cst: &Cst, text: &str, clock: NodeId) -> String {
    let name = cst.child_tokens(clock).map(|t| cst.token(t)).find(|t| t.kind == TokenKind::Ident);
    let name = name.map_or("", |t| &text[t.span.start as usize..t.span.end as usize]);
    format!(" at {name}")
}

/// How a clock is taken out of the text ([`take_out`]).
struct Out {
    /// The end of the token before the clock.
    before: u32,
    /// The clock, `at` and its name.
    clock: Span,
    /// A comment lies between the token before and the clock: it stays, and
    /// so do the blanks around it (§18.2, S-216: an edit holds no comment).
    commented: bool,
}

impl Out {
    /// The edits that take the clock out and write `after` right after the
    /// token before it (`)` that closes a function type, a clock moved).
    fn edits(&self, after: &str) -> Vec<Edit> {
        let file = self.clock.file;
        if !self.commented {
            let whole = Span::new(file, self.before, self.clock.end);
            return vec![if after.is_empty() { Edit::delete(whole) } else { Edit::replace(whole, after) }];
        }
        let mut edits = Vec::new();
        if !after.is_empty() {
            edits.push(Edit::insert(file, self.before, after));
        }
        edits.push(Edit::delete(self.clock));
        edits
    }
}

/// How `clock` is taken out, with the blanks before it when no comment lies
/// there. `None` when a comment is inside the clock (`at // c` and the name
/// on the next line): no edit takes it out without the comment, and the
/// diagnostic has no candidate (S-48).
fn take_out(cst: &Cst, clock: NodeId) -> Option<Out> {
    let range = cst.token_range(clock);
    if range.clone().any(|k| matches!(cst.tokens()[k].kind, TokenKind::Comment | TokenKind::DocComment)) {
        return None;
    }
    let mut commented = false;
    let mut before = 0;
    for k in (0..range.start).rev() {
        let t = cst.tokens()[k];
        match t.kind {
            TokenKind::Comment | TokenKind::DocComment | TokenKind::BlockComment => commented = true,
            k if k.is_trivia() => {}
            _ => {
                before = t.span.end;
                break;
            }
        }
    }
    Some(Out { before, clock: cst.span(clock), commented })
}

/// The candidates that move `clock` to the value of the binding `stmt`
/// (§11.3: `let y: F32 = x at sample`). A value that is no plain operand
/// takes parentheses ([`crate::ast::Operand::bare_before_as_at`], E0011).
/// A value that has a clock already (in parentheses or not) is no place for
/// another: the candidate takes the clock out (S-356). `None` when the
/// statement was not read whole; no candidate when the value is `move x`
/// or the clock holds a comment.
fn to_value(cst: &Cst, text: &str, clock: NodeId, stmt: NodeId) -> Option<Vec<Fix>> {
    if !cst.is_complete(stmt) {
        return None;
    }
    let first_expr = |n: NodeId| cst.child_nodes(n).find(|&c| class(cst.kind(c)) == Class::Expr);
    let value = cst.child_nodes(stmt).filter(|&n| class(cst.kind(n)) == Class::Expr).last()?;
    let Some(out) = take_out(cst, clock) else { return Some(Vec::new()) };
    let mut inner = value;
    while cst.kind(inner) == NodeKind::ParenExpr {
        inner = first_expr(inner)?;
    }
    if cst.kind(inner) == NodeKind::AtExpr {
        return Some(vec![Fix::new("remove the clock", out.edits(""))]);
    }
    let s = cst.span(value);
    let at = clock_text(cst, text, clock);
    let kinds: Vec<TokenKind> = cst.token_range(value).map(|i| cst.tokens()[i].kind).collect();
    let mut edits = out.edits("");
    match cst.kind(value) {
        // SPEC-GAP(S-381): the operand of `move` takes no clock (§5.2), and
        // the spec gives no other place for it: no candidate.
        NodeKind::MoveExpr => return Some(Vec::new()),
        _ if !super::operand(&kinds).bare_before_as_at() => {
            edits.extend([Edit::insert(s.file, s.start, "("), Edit::insert(s.file, s.end, format!("){at}"))]);
        }
        _ => edits.push(Edit::insert(s.file, s.end, at)),
    }
    Some(vec![Fix::new("write the clock on the value", edits)])
}

/// The candidate of a clock in a type (S-356): moved after the type of the
/// input or output of a flow it is in, or to the value of the binding it is
/// in, when that place has no clock; else taken out. `None` when a type
/// around it was not read whole (`Option[F32 at sample at block]`: the
/// second `at` is the E0002 of the unit, as at the type of an input); no
/// candidate when the clock holds a comment.
fn in_type(cst: &Cst, text: &str, clock: NodeId) -> Option<Vec<Fix>> {
    let typeish = |n: NodeId| {
        class(cst.kind(n)) == Class::Type || matches!(cst.kind(n), NodeKind::TypeArgs | NodeKind::FnTypeParams)
    };
    let mut place = clock;
    while let Some(p) = cst.parent(place) {
        place = p;
        if !typeish(p) {
            break;
        }
        if !cst.is_complete(p) {
            return None;
        }
    }
    let has_clock = |n: NodeId| cst.child_nodes(n).any(|c| cst.kind(c) == NodeKind::Clock);
    let in_flow = |n: NodeId| {
        cst.kind(n) == NodeKind::Flow
            || (cst.kind(n) == NodeKind::Param
                && cst.parent(n).and_then(|l| cst.parent(l)).is_some_and(|f| cst.kind(f) == NodeKind::Flow))
    };
    let Some(out) = take_out(cst, clock) else { return Some(Vec::new()) };
    // The type of the input, the output or the binding: the type child of the node.
    let ty = cst.child_nodes(place).find(|&n| class(cst.kind(n)) == Class::Type && cst.is_complete(n));
    // A function type that no `uses` closes: a clock after it belongs to its
    // result (S-367), so the type is parenthesized to take one after it.
    let open = |t: NodeId| cst.kind(t) == NodeKind::FnType && !has_effects(cst, t);
    if in_flow(place)
        && !has_clock(place)
        && let Some(ty) = ty
    {
        let s = cst.span(ty);
        let at = clock_text(cst, text, clock);
        let edits = if !open(ty) {
            let mut e = out.edits("");
            e.push(Edit::insert(s.file, s.end, at));
            e
        } else if out.clock.end == s.end {
            // The clock was the end of the function type: the `)` goes where
            // the type ends without it.
            let mut e = vec![Edit::insert(s.file, s.start, "(")];
            e.extend(out.edits(&format!("){at}")));
            e
        } else {
            let mut e = vec![Edit::insert(s.file, s.start, "(")];
            e.extend(out.edits(""));
            e.push(Edit::insert(s.file, s.end, format!("){at}")));
            e
        };
        return Some(vec![Fix::new("write the clock after the type", edits)]);
    }
    if matches!(cst.kind(place), NodeKind::LetStmt | NodeKind::VarStmt)
        && !has_clock(place)
        && let Some(fixes) = to_value(cst, text, clock, place)
        && !fixes.is_empty()
    {
        return Some(fixes);
    }
    // Taken out of the end of a function type that no `uses` closes, the
    // clock after the type would become its result's (S-367): the function
    // type is parenthesized (`g: (fn(F32) -> F32) at sample`).
    if has_clock(place)
        && let Some(ty) = ty.filter(|&t| open(t))
        && cst.span(ty).end == out.clock.end
    {
        let s = cst.span(ty);
        let mut edits = vec![Edit::insert(s.file, s.start, "(")];
        edits.extend(out.edits(")"));
        return Some(vec![Fix::new("remove the clock", edits)]);
    }
    Some(vec![Fix::new("remove the clock", out.edits(""))])
}

/// The function type `ty` ends with its effect row (`uses {…}`), which closes
/// it: a clock after it is the clock of its position.
fn has_effects(cst: &Cst, ty: NodeId) -> bool {
    cst.child_nodes(ty).any(|n| cst.kind(n) == NodeKind::EffectRow)
}
