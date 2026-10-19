//! Post-parse checks on operator chains (spec §3.1): E0010 (an operator of a
//! chain with an operand the strengths of the groups do not allow), E0011
//! (`as` and `at` as a bare operand, and `as` / `at` chained), E0012
//! (stacked prefix operators).
//!
//! A chain is the tree of §3.1 in the AST ([`Chain`]). The candidates of
//! E0010 (S-60, §18.1) are the readings of the chain with temporary
//! strengths placed on the groups that clash, one per placement.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::ast::{Ast, BinOp, Chain, ExprId, ExprKind, Lit, OpGroup, Side, StrSeg};
use crate::cst::NodeKind;
use crate::nesting::{Limit, TOO_DEEP_RULE, parenthesized};

/// The checks of this module on the AST of one file. `kind_of` is the kind
/// of the CST node of an expression; `limit` the file and its units, for the
/// candidates that add parentheses (§2.5).
pub(crate) fn check(ast: &Ast, kind_of: &dyn Fn(ExprId) -> NodeKind, limit: Limit, diagnostics: &mut Vec<Diagnostic>) {
    let text = limit.text;
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
    // The operators under another one of their chain, and the casts and
    // clocks under another one (a chain of `as` / `at` is one form, as a stack
    // is).
    let mut inner = HashSet::new();
    for (i, e) in ast.exprs.iter().enumerate() {
        if let ExprKind::Binary { lhs, rhs, .. } = e.kind {
            inner.extend([lhs, rhs].into_iter().filter(|&c| matches!(ast.expr(c).kind, ExprKind::Binary { .. })));
        }
        if let Some(operand) = ast.as_or_at_operand(ExprId(i as u32))
            && ast.as_or_at_operand(operand).is_some()
        {
            inner.insert(operand);
        }
    }
    for (i, expr) in ast.exprs.iter().enumerate() {
        let id = ExprId(i as u32);
        match expr.kind {
            ExprKind::Binary { .. } => {
                if inner.contains(&id) {
                    continue;
                }
                let (ops, operands) = chain_nodes(ast, id);
                // E0011: a cast or a clock is parenthesized as an operand of
                // a chain.
                // SPEC-GAP(S-348): those of one chain are one form,
                // parenthesized whole.
                let casts: Vec<Span> = operands
                    .iter()
                    .filter(|&&o| ast.as_or_at_operand(o).is_some())
                    .map(|&o| ast.expr(o).span)
                    .collect();
                if let Some(&first) = casts.first() {
                    let edits = casts
                        .iter()
                        .flat_map(|s| [Edit::insert(s.file, s.start, "("), Edit::insert(s.file, s.end, ")")])
                        .collect();
                    let d = Diagnostic::new(
                        Stage::Syntax,
                        Code::E0011,
                        first,
                        "`as` and `at` are written in parentheses when they are an operand (§3.1)",
                    )
                    .with_found(src(first));
                    let span = ast.expr(id).span;
                    diagnostics.push(parenthesized(d, limit, span, "parenthesize it", edits));
                }
                let parts = clashes(ast, &ops);
                if !parts.is_empty() {
                    diagnostics.push(Flat::new(ast, text, id).e0010(parts, limit));
                }
            }
            // E0011: a cast or a clock is parenthesized as an end of a range
            // too: the range symbols are weaker than `as` and `at` (§3.1,
            // §3.3, S-340); those of one head are one form (S-348).
            ExprKind::Range(head) | ExprKind::Par { range: head, .. } => {
                let casts: Vec<Span> = [head.lo, head.hi]
                    .into_iter()
                    .filter(|&o| ast.as_or_at_operand(o).is_some())
                    .map(|o| ast.expr(o).span)
                    .collect();
                if let Some(&first) = casts.first() {
                    let edits = casts
                        .iter()
                        .flat_map(|s| [Edit::insert(s.file, s.start, "("), Edit::insert(s.file, s.end, ")")])
                        .collect();
                    let d = Diagnostic::new(
                        Stage::Syntax,
                        Code::E0011,
                        first,
                        "`as` and `at` are written in parentheses when they are an end of a range (§3.1)",
                    )
                    .with_found(src(first));
                    diagnostics.push(parenthesized(d, limit, expr.span, "parenthesize it", edits));
                }
            }
            ExprKind::Cast { .. } | ExprKind::At { .. }
                if !inner.contains(&id)
                    && ast.as_or_at_operand(id).is_some_and(|o| ast.as_or_at_operand(o).is_some()) =>
            {
                // E0011: `x as A as B` is `(x as A) as B` written out, and so
                // are `at` and the mixed chains (§3.1, S-118).
                let mut e = ast.as_or_at_operand(id).unwrap_or(id);
                let mut closes = Vec::new();
                while let Some(base) = ast.as_or_at_operand(e) {
                    closes.push(Edit::insert(expr.span.file, ast.expr(e).span.end, ")"));
                    e = base;
                }
                let mut edits = vec![Edit::insert(expr.span.file, expr.span.start, "(".repeat(closes.len()))];
                edits.extend(closes.into_iter().rev());
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0011,
                    expr.span,
                    "`as` and `at` are not chained; parenthesize the inner one (§3.1)",
                )
                .with_found(src(expr.span));
                diagnostics.push(parenthesized(d, limit, expr.span, "parenthesize the inner one", edits));
            }
            ExprKind::Unary { .. } if stacked(id) && !inner_of_a_stack.contains(&id) => {
                // The operators of the stack, outermost first: each but the
                // last takes the rest in parentheses (`- - -x` is
                // `-(-(-x))`); the blanks between two operators give way
                // to the `(` (S-410).
                let mut ops = vec![expr.span];
                let mut e = id;
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
                // The blank after the innermost operator goes too (S-410:
                // `- - x` is `-(-x)`, which leaves no blank after a prefix).
                let last = ops[ops.len() - 1];
                let operand = Span::new(last.file, last.start + 1, ast.expr(e).span.start);
                if !operand.is_empty() && src(operand).trim().is_empty() {
                    edits.push(Edit::delete(operand));
                }
                edits.push(Edit::insert(expr.span.file, expr.span.end, ")".repeat(ops.len() - 1)));
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0012,
                    expr.span,
                    "prefix operators are not stacked; parenthesize the inner operator (§3.1)",
                )
                .with_found(src(expr.span));
                diagnostics.push(parenthesized(d, limit, expr.span, "parenthesize the inner operator", edits));
            }
            _ => {}
        }
    }
    block_like_errors(ast, kind_of, limit, diagnostics);
}

/// The operands of `e` as an operator (§3.1, S-537): both sides of a binary
/// operator, the operand of a prefix, `as` and `at`, and the receiver of a
/// postfix (the callee of a call, the base of `.`, `::[`, `[` and `?`).
/// The arguments, the index and the parts of the other forms are no operands
/// (they are whole expressions).
fn operands(kind: &ExprKind) -> [Option<ExprId>; 2] {
    use ExprKind::*;
    match *kind {
        Binary { lhs, rhs, .. } => [Some(lhs), Some(rhs)],
        Unary { expr, .. } | Cast { expr, .. } | At { expr, .. } | Call { callee: expr, .. } => [Some(expr), None],
        Field { base, .. } | TypeArgs { base, .. } | TupleIndex { base, .. } | Index { base, .. } | Try(base) => {
            [Some(base), None]
        }
        Lit(_)
        | Path(_)
        | Hole
        | Error
        | Paren(_)
        | Tuple(_)
        | Array(_)
        | Repeat { .. }
        | Struct { .. }
        | Block(_)
        | If { .. }
        | Match { .. }
        | Closure { .. }
        | Handle { .. }
        | Unsafe(_)
        | Par { .. }
        | Feedback(_)
        | Move(_)
        | Range(_) => [None, None],
    }
}

/// The block-like operands of each expression that has some (§3.1, S-537):
/// the span of the expression (the operators joined by their operands, as
/// far as parentheses and whole positions; its root is the operand of no
/// other) and the spans of its block-like operands ([`NodeKind::block_like`],
/// `kind_of` the kind of the CST node of an expression), the first in the
/// text first. The one judgment of the form: E0013 here, and the
/// parentheses that the other candidates need (`crate::operands`).
pub(crate) fn block_like_operands(ast: &Ast, kind_of: &dyn Fn(ExprId) -> NodeKind) -> Vec<(Span, Vec<Span>)> {
    let under: HashSet<ExprId> = ast.exprs.iter().flat_map(|e| operands(&e.kind)).flatten().collect();
    let mut out = Vec::new();
    for (i, expr) in ast.exprs.iter().enumerate() {
        if under.contains(&ExprId(i as u32)) {
            continue;
        }
        // Without recursion (a chain is up to 256 levels high).
        let mut found = Vec::new();
        let mut todo: Vec<ExprId> = operands(&expr.kind).into_iter().flatten().collect();
        while let Some(o) = todo.pop() {
            if kind_of(o).block_like() {
                found.push(ast.expr(o).span);
            } else {
                todo.extend(operands(&ast.expr(o).kind).into_iter().flatten());
            }
        }
        if !found.is_empty() {
            found.sort_by_key(|s| s.start);
            out.push((expr.span, found));
        }
    }
    out
}

/// The parentheses round `operands` (insertions, S-251).
pub(crate) fn parenthesizing(operands: &[Span]) -> impl Iterator<Item = Edit> + '_ {
    operands.iter().flat_map(|s| [Edit::insert(s.file, s.start, "("), Edit::insert(s.file, s.end, ")")])
}

/// E0013 (§3.1, S-537): a block-like expression is parenthesized as an
/// operand. Those of one expression are one form, and the candidate
/// parenthesizes them all (S-236); the main span is the first (J-4).
fn block_like_errors(ast: &Ast, kind_of: &dyn Fn(ExprId) -> NodeKind, limit: Limit, diagnostics: &mut Vec<Diagnostic>) {
    let text = limit.text;
    for (span, found) in block_like_operands(ast, kind_of) {
        let at = found[0];
        let d = Diagnostic::new(
            Stage::Syntax,
            Code::E0013,
            at,
            "a block-like expression (`if`, `match`, a block, an anonymous function, `unsafe`, `handle`, `par`) is written in parentheses when it is an operand (§3.1)",
        )
        .with_found(&text[at.start as usize..at.end as usize]);
        diagnostics.push(parenthesized(d, limit, span, "parenthesize it", parenthesizing(&found).collect()));
    }
}

/// The operators of the chain whose root is `root` (its `Binary` nodes, in
/// the order the AST made them: the order of the joins of [`Chain`]) and
/// its operands, from the left.
fn chain_nodes(ast: &Ast, root: ExprId) -> (Vec<ExprId>, Vec<ExprId>) {
    let (mut ops, mut operands) = (Vec::new(), Vec::new());
    // Without recursion (a chain is up to 256 levels high); the left side
    // first.
    let mut todo = vec![root];
    while let Some(e) = todo.pop() {
        match ast.expr(e).kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                ops.push(e);
                todo.extend([rhs, lhs]);
            }
            _ => operands.push(e),
        }
    }
    // The ascending ids are the order of the joins: `lower::chain` reads the
    // chain with [`Chain`] and adds each `Binary` node (`add_expr`) at its
    // join, after its operands. The parts of the E0010 message follow it
    // (the test `the_parts_of_e0010_follow_the_joins`).
    ops.sort_unstable();
    (ops, operands)
}

/// The judgment of E0010 on the edges of the tree of a chain (the AST,
/// `ops` from [`chain_nodes`]): each operator with an operator operand the
/// strengths of §3.1 do not allow ([`BinOp::takes`]), said once per pair
/// of keys, in the order of `ops`. Empty when the chain is allowed.
// SPEC-GAP(S-344): groups without a strength between them that are not
// next to each other in the tree (`a % b == c + d`) pass: the judgment
// is on the edges of the tree.
fn clashes(ast: &Ast, ops: &[ExprId]) -> Vec<String> {
    let binary = |e: ExprId| match ast.expr(e).kind {
        ExprKind::Binary { op, op_span, .. } => Some((op, op_span)),
        _ => None,
    };
    let mut parts = Vec::new();
    let mut said = HashSet::new();
    for &e in ops {
        let ExprKind::Binary { op, op_span, lhs, rhs } = ast.expr(e).kind else { continue };
        for (side, c) in [(Side::Left, lhs), (Side::Right, rhs)] {
            let Some((child, child_span)) = binary(c) else { continue };
            if op.takes(side, child) {
                continue;
            }
            let (k, kc) = (key(op, op_span), key(child, child_span));
            let part = if k == kc {
                format!("`{}` cannot be chained", op.symbol())
            } else {
                let (a, b) = if child_span.start < op_span.start { (child, op) } else { (op, child) };
                format!("`{}` and `{}` have no strength between them", a.symbol(), b.symbol())
            };
            if said.insert((k.min(kc), k.max(kc))) {
                parts.push(part);
            }
        }
    }
    parts
}

/// The groups that are one key of strength each: every group of §3.1 but
/// the bitwise one. A key below `GROUPS.len()` is the group at its index.
const GROUPS: [OpGroup; 6] =
    [OpGroup::Additive, OpGroup::Multiplicative, OpGroup::Remainder, OpGroup::Comparison, OpGroup::And, OpGroup::Or];

/// The operators of the bitwise group, one key each (§18.1: its operators
/// clash as groups of their own; one operator chains with itself, S-61),
/// after the keys of [`GROUPS`].
const BITWISE: [BinOp; 5] = [BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor, BinOp::Shl, BinOp::Shr];

/// The number of keys of strength.
const KEYS: usize = GROUPS.len() + BITWISE.len();

/// The key of strength of `op` ([`GROUPS`], [`BITWISE`]), written at `at`.
fn key(op: BinOp, at: Span) -> usize {
    key_of(op)
        .unwrap_or_else(|| onsa_diag::internal::bug(Some(at), format!("`{}` has no key of strength", op.symbol())))
}

/// [`key`], `None` for an operator in neither table.
fn key_of(op: BinOp) -> Option<usize> {
    match op.group() {
        OpGroup::Bitwise => BITWISE.iter().position(|&b| b == op).map(|k| GROUPS.len() + k),
        group => GROUPS.iter().position(|&g| g == group),
    }
}

/// Strengths between keys: those of §3.1 ([`OpGroup::stronger`]) and the
/// temporary ones of a reading, closed under transitivity.
#[derive(Clone)]
struct Order([[bool; KEYS]; KEYS]);

impl Order {
    fn of_the_spec() -> Order {
        let mut gt = [[false; KEYS]; KEYS];
        for (a, ga) in GROUPS.iter().enumerate() {
            for (b, gb) in GROUPS.iter().enumerate() {
                gt[a][b] = ga.stronger(*gb);
            }
        }
        Order(gt)
    }

    /// Whether an operator of key `op` takes the operand of a waiting one of
    /// key `waiting` (it is stronger); a pair without a strength yet is kept
    /// in `undecided` (the first one) and read as left to right.
    fn tighter(&self, op: usize, waiting: usize, undecided: &mut Option<(usize, usize)>) -> bool {
        if op == waiting || self.0[waiting][op] {
            return false;
        }
        if !self.0[op][waiting] {
            undecided.get_or_insert((op, waiting));
        }
        self.0[op][waiting]
    }

    /// With `a` stronger than `b`, and what follows from it.
    fn with(&self, a: usize, b: usize) -> Order {
        let mut gt = self.0;
        for x in (0..KEYS).filter(|&x| x == a || self.0[x][a]) {
            for y in (0..KEYS).filter(|&y| y == b || self.0[b][y]) {
                gt[x][y] = true;
            }
        }
        Order(gt)
    }
}

/// A node of a reading: an operand (its index), or an operator (its index)
/// with its two operand nodes.
#[derive(Clone, Copy)]
enum Node {
    Operand(usize),
    Op(usize, usize, usize),
}

/// A reading of a chain: its nodes, the root last.
struct Reading(Vec<Node>);

/// Why a reading has no candidate: the middle of a chain of comparisons
/// would be evaluated twice (§18.1).
struct TwiceEvaluated;

/// One chain, flat: its operands and operators from the left.
struct Flat<'a> {
    ast: &'a Ast,
    text: &'a str,
    span: Span,
    operands: Vec<ExprId>,
    ops: Vec<BinOp>,
    /// The key of strength of each of `ops` ([`key`]).
    keys: Vec<usize>,
}

impl<'a> Flat<'a> {
    fn new(ast: &'a Ast, text: &'a str, root: ExprId) -> Flat<'a> {
        let (mut operands, mut ops, mut keys) = (Vec::new(), Vec::new(), Vec::new());
        // In order, without recursion (a chain is up to 256 levels high).
        let mut right = Vec::new();
        let mut e = root;
        loop {
            if let ExprKind::Binary { op, op_span, lhs, rhs } = ast.expr(e).kind {
                right.push((op, op_span, rhs));
                e = lhs;
                continue;
            }
            operands.push(e);
            let Some((op, op_span, rhs)) = right.pop() else { break };
            ops.push(op);
            keys.push(key(op, op_span));
            e = rhs;
        }
        Flat { ast, text, span: ast.expr(root).span, operands, ops, keys }
    }

    fn src(&self, e: ExprId) -> &'a str {
        let s = self.ast.expr(e).span;
        &self.text[s.start as usize..s.end as usize]
    }

    /// The chain read with the strengths of `order` ([`Chain`], the reading
    /// of the AST under the strengths of §3.1).
    fn read(&self, order: &Order, undecided: &mut Option<(usize, usize)>) -> Reading {
        let nodes = RefCell::new(vec![Node::Operand(0)]);
        let push = |n: Node| {
            let mut nodes = nodes.borrow_mut();
            nodes.push(n);
            nodes.len() - 1
        };
        let join = |l, o, r| push(Node::Op(o, l, r));
        let mut chain = Chain::new(0);
        for o in 0..self.ops.len() {
            chain.operator(o, |o: usize, w: usize| order.tighter(self.keys[o], self.keys[w], undecided), join);
            chain.operand(push(Node::Operand(o + 1)));
        }
        chain.finish(join);
        Reading(nodes.into_inner())
    }

    /// The readings of the chain, one per placement of strengths on the keys
    /// that clash (S-60), in an order the implementation chose (§18.1 does
    /// not promise one, X-3; S-347 was dropped): at each pair without a
    /// strength, met from the left, the key that appears first in the
    /// expression is taken as the stronger one first. Each pair decided one
    /// way or the other makes a different tree, so the readings differ;
    /// more than three are not all made.
    fn readings(&self) -> (Vec<Reading>, bool) {
        let mut first = [usize::MAX; KEYS];
        for (i, &k) in self.keys.iter().enumerate().rev() {
            first[k] = i;
        }
        let mut readings = Vec::new();
        let mut todo = vec![Order::of_the_spec()];
        while let Some(order) = todo.pop() {
            let mut undecided = None;
            let reading = self.read(&order, &mut undecided);
            match undecided {
                None if readings.len() == 3 => return (readings, true),
                None => readings.push(reading),
                Some((a, b)) => {
                    let (s, w) = if first[a] < first[b] { (a, b) } else { (b, a) };
                    todo.push(order.with(w, s));
                    todo.push(order.with(s, w));
                }
            }
        }
        (readings, false)
    }
}

/// The longest chain, in characters, whose readings the message and the
/// titles show (S-345: the implementation chooses it).
const READINGS_MAX: usize = 80;

/// Whether the message and the titles of the candidates show the readings of
/// the chain written `found`: it is on one line and short (S-345, §18.1; the
/// one decision for both).
fn shows_readings(found: &str) -> bool {
    found.chars().count() <= READINGS_MAX && !found.contains(['\n', '\r'])
}

/// Where a candidate inserts its text: offsets and what goes there (only
/// insertions, S-251).
type Inserts = BTreeMap<u32, String>;

/// `text` from `start` with the insertions.
fn inserted(text: &str, start: u32, ins: &Inserts) -> String {
    let mut out = String::new();
    let mut at = start as usize;
    for (&o, s) in ins {
        out.push_str(&text[at..o as usize]);
        out.push_str(s);
        at = o as usize;
    }
    out.push_str(&text[at..]);
    out
}

impl Flat<'_> {
    /// The E0010 of the chain, whose clashes are `parts` ([`clashes`]): one
    /// diagnostic for the chain (one form), with a candidate per reading
    /// (S-60).
    fn e0010(&self, parts: Vec<String>, limit: Limit) -> Diagnostic {
        let found = &self.text[self.span.start as usize..self.span.end as usize];
        let mut message = parts.join("; ");
        let (readings, more) = self.readings();
        let mut rule = None;
        let mut candidates = Vec::new();
        if more {
            rule = Some(
                "it has more than three readings: parenthesize the operators of groups without a strength between \
                 them, so that it reads one way",
            );
        }
        for r in readings.iter().filter(|_| !more) {
            match self.render(r) {
                // SPEC-GAP(S-346): a reading that cannot be written (a middle
                // evaluated twice) drops every candidate, and one over the
                // nesting limit drops itself.
                Err(TwiceEvaluated) => {
                    rule = Some(
                        "the middle operand of a chain of comparisons would be evaluated twice: bind it with `let`, \
                         then write `a < m && m < c`",
                    );
                    candidates.clear();
                    break;
                }
                Ok(ins) if self.nests_too_deep(&ins, limit) => {
                    rule = Some(TOO_DEEP_RULE);
                }
                Ok(ins) => candidates.push(ins),
            }
        }
        let texts: Vec<String> = candidates.iter().map(|ins| self.reading_text(ins)).collect();
        // A long chain, or one over lines, has its readings in the candidates
        // only, not in the message or the titles (S-345).
        let shown = shows_readings(found);
        if !texts.is_empty() && shown {
            let texts: Vec<String> = texts.iter().map(|t| format!("`{t}`")).collect();
            if texts.len() == 1 {
                message = format!("{message}; write {}", texts[0]);
            } else {
                message = format!("{message}: `{found}` reads as {}", texts.join(" or as "));
            }
        }
        let mut d =
            Diagnostic::new(Stage::Syntax, Code::E0010, self.span, format!("{message} (§3.1)")).with_found(found);
        if let Some(rule) = rule.filter(|_| candidates.is_empty()) {
            d = d.with_rule(rule);
        }
        let n = candidates.len();
        for (i, (ins, text)) in candidates.into_iter().zip(texts).enumerate() {
            let title = if shown { format!("read it as `{text}`") } else { format!("reading {} of {n}", i + 1) };
            let edits = ins.into_iter().map(|(at, s)| Edit::insert(self.span.file, at, s)).collect();
            d = d.with_fix(Fix::new(title, edits));
        }
        d
    }

    /// The candidate of a reading: the parentheses its edges need under the
    /// strengths of §3.1 (none where they are fixed), and each chain of
    /// comparisons written as `a < b && b < c` (§18.1), which is then an
    /// operand of the `&&` group.
    fn render(&self, r: &Reading) -> Result<Inserts, TwiceEvaluated> {
        let nodes = &r.0;
        let comparison = |o: usize| self.ops[o].group() == OpGroup::Comparison;
        let chained = |n: usize| match nodes[n] {
            Node::Op(o, l, _) => comparison(o) && matches!(nodes[l], Node::Op(lo, ..) if comparison(lo)),
            Node::Operand(_) => false,
        };
        let operator = |n: usize| match nodes[n] {
            Node::Op(_, _, _) if chained(n) => Some(BinOp::And),
            Node::Op(o, _, _) => Some(self.ops[o]),
            Node::Operand(_) => None,
        };
        let mut ins = Inserts::new();
        for (n, &node) in nodes.iter().enumerate() {
            let Node::Op(o, l, r) = node else { continue };
            if chained(n) {
                let Node::Op(_, _, middle) = nodes[l] else { unreachable!() };
                let Node::Operand(m) = nodes[middle] else { return Err(TwiceEvaluated) };
                if !self.evaluated_once(self.operands[m]) {
                    return Err(TwiceEvaluated);
                }
                let end = self.ast.expr(self.operands[m]).span.end;
                ins.entry(end).or_default().push_str(&format!(" && {}", self.src(self.operands[m])));
            } else if operator(l).is_some_and(|c| !self.ops[o].takes(Side::Left, c)) {
                self.parenthesize(nodes, l, &mut ins);
            }
            // A chain of comparisons on the right of `&&` needs none: written
            // out, its `&&` chain with this one, of the same value (S-60).
            let and_chain = self.ops[o] == BinOp::And && chained(r);
            if !and_chain && operator(r).is_some_and(|c| !self.ops[o].takes(Side::Right, c)) {
                self.parenthesize(nodes, r, &mut ins);
            }
        }
        Ok(ins)
    }

    fn parenthesize(&self, nodes: &[Node], n: usize, ins: &mut Inserts) {
        let end = |mut n: usize, left: bool| loop {
            match nodes[n] {
                Node::Op(_, l, r) => n = if left { l } else { r },
                Node::Operand(i) => break self.ast.expr(self.operands[i]).span,
            }
        };
        ins.entry(end(n, true).start).or_default().push('(');
        ins.entry(end(n, false).end).or_default().push(')');
    }

    /// The middle of a chain of comparisons that may be written twice: a
    /// name, a literal (a negated number one too, S-227), or a path of
    /// fields (`p.x`, `t.0`, `F32.PI`).
    fn evaluated_once(&self, e: ExprId) -> bool {
        match &self.ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => s.segments.iter().all(|s| matches!(s, StrSeg::Text(_))),
            ExprKind::Path(_) | ExprKind::Lit(_) => true,
            ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } => {
                matches!(self.ast.expr(*base).kind, ExprKind::Path(_)) || self.field_path(*base)
            }
            ExprKind::Unary { .. } => self.ast.negated_literal(e).is_some(),
            _ => false,
        }
    }

    fn field_path(&self, e: ExprId) -> bool {
        matches!(self.ast.expr(e).kind, ExprKind::Field { .. } | ExprKind::TupleIndex { .. }) && self.evaluated_once(e)
    }

    /// The chain as a candidate writes it.
    fn reading_text(&self, ins: &Inserts) -> String {
        inserted(&self.text[..self.span.end as usize], self.span.start, ins)
    }

    /// Whether the candidate nests over the limit (spec §2.5; §18.1: such a
    /// candidate is not made), with the levels the candidate may add.
    fn nests_too_deep(&self, ins: &Inserts, limit: Limit) -> bool {
        let added = ins.values().map(|s| s.matches(['(', '&']).count() as u32).sum::<u32>() + self.ops.len() as u32;
        let file = self.span.file;
        let edits: Vec<Edit> = ins.iter().map(|(&at, s)| Edit::insert(file, at, s.clone())).collect();
        limit.exceeded(self.span, &edits, added)
    }
}
#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    const BEFORE: &str = "fn f() {\n  let v = ";
    const AFTER: &str = "\n}";

    /// The diagnostics of `let v = <src>`, and the expression after each
    /// candidate of each.
    fn all(src: &str) -> Vec<(Code, Vec<String>)> {
        let text = format!("{BEFORE}{src}{AFTER}");
        let p = crate::parse(FileId(0), &text);
        p.diagnostics
            .iter()
            .map(|d| {
                let fixes = d
                    .fixes
                    .iter()
                    .map(|f| {
                        let edits: Vec<&onsa_diag::Edit> = f.edits().iter().collect();
                        let after = onsa_diag::apply_text(&text, &edits).unwrap();
                        after[BEFORE.len()..after.len() - AFTER.len()].to_string()
                    })
                    .collect();
                (d.code, fixes)
            })
            .collect()
    }

    /// The diagnostics of `let v = <src>`, and the expression after the
    /// first candidate of each.
    fn check(src: &str) -> Vec<(Code, Option<String>)> {
        all(src).into_iter().map(|(c, f)| (c, f.into_iter().next())).collect()
    }

    /// The candidates of the one E0010 of `src`; each leaves no diagnostic.
    fn candidates(src: &str) -> Vec<String> {
        let d = all(src);
        assert_eq!(d.len(), 1, "{src}: {d:?}");
        assert_eq!(d[0].0, Code::E0010, "{src}");
        for fixed in &d[0].1 {
            assert!(all(fixed).is_empty(), "{src} -> {fixed}: {:?}", all(fixed));
        }
        d[0].1.clone()
    }

    #[test]
    fn the_strengths_are_a_partial_order() {
        use crate::ast::OpGroup::{self, *};
        let all = [Additive, Multiplicative, Remainder, Comparison, And, Or, Bitwise];
        let s = |a: OpGroup, b: OpGroup| a.stronger(b);
        for a in all {
            assert!(!s(a, a));
            for b in all {
                assert!(!(s(a, b) && s(b, a)));
                for c in all {
                    assert!(!(s(a, b) && s(b, c)) || s(a, c), "{a:?} {b:?} {c:?}");
                }
            }
        }
        // The facts of §3.1.
        assert!(s(Multiplicative, Additive) && s(Additive, Comparison) && s(Comparison, And) && s(Comparison, Or));
        assert!(s(Remainder, Comparison));
        assert!(!s(Remainder, Additive) && !s(Additive, Remainder) && !s(Remainder, Multiplicative));
        assert!(!s(Multiplicative, Remainder) && !s(And, Or) && !s(Or, And));
        assert!(all.iter().all(|&g| !s(Bitwise, g) && !s(g, Bitwise)));
    }

    /// Every value of `BinOp`: each names the next in an exhaustive `match`,
    /// so that a new operator does not compile until it is in the list.
    fn every_binop() -> Vec<crate::ast::BinOp> {
        use crate::ast::BinOp::{self, *};
        fn next(op: Option<BinOp>) -> Option<BinOp> {
            match op {
                None => Some(Add),
                Some(Add) => Some(Sub),
                Some(Sub) => Some(Mul),
                Some(Mul) => Some(Div),
                Some(Div) => Some(Rem),
                Some(Rem) => Some(WrapAdd),
                Some(WrapAdd) => Some(WrapSub),
                Some(WrapSub) => Some(WrapMul),
                Some(WrapMul) => Some(SatAdd),
                Some(SatAdd) => Some(SatSub),
                Some(SatSub) => Some(SatMul),
                Some(SatMul) => Some(Eq),
                Some(Eq) => Some(Ne),
                Some(Ne) => Some(Lt),
                Some(Lt) => Some(Le),
                Some(Le) => Some(Gt),
                Some(Gt) => Some(Ge),
                Some(Ge) => Some(And),
                Some(And) => Some(Or),
                Some(Or) => Some(BitAnd),
                Some(BitAnd) => Some(BitOr),
                Some(BitOr) => Some(BitXor),
                Some(BitXor) => Some(Shl),
                Some(Shl) => Some(Shr),
                Some(Shr) => None,
            }
        }
        std::iter::successors(next(None), |&op| next(Some(op))).collect()
    }

    /// Every binary operator has a key of strength: an operator of the
    /// bitwise group one of its own, any other the one of its group (§18.1,
    /// S-61), and every key is some operator's.
    #[test]
    fn every_operator_has_its_key() {
        use super::{KEYS, key_of};
        use crate::ast::OpGroup;
        let ops = every_binop();
        // The list is whole: the operators of the tokens are in it, once each.
        let distinct: std::collections::HashSet<_> = ops.iter().collect();
        assert_eq!(distinct.len(), ops.len(), "{ops:?}");
        for op in crate::token::TokenKind::ALL.iter().filter_map(|k| k.binop()) {
            assert!(ops.contains(&op), "{op:?}");
        }
        let key = |op| key_of(op).unwrap_or_else(|| panic!("{op:?} has no key"));
        for &a in &ops {
            assert!(key(a) < KEYS, "{a:?}");
            for &b in &ops {
                let same = if a.group() == OpGroup::Bitwise { a == b } else { a.group() == b.group() };
                assert_eq!(key(a) == key(b), same, "{a:?} {b:?}");
            }
        }
        let used: std::collections::HashSet<usize> = ops.iter().map(|&o| key(o)).collect();
        assert_eq!(used.len(), KEYS);
    }

    /// The parts of the E0010 message are in the order of the joins of the
    /// chain (`chain_nodes`): `a & b | c ^ d << a >> b` reads left to right
    /// (no two of the operators have a strength between them).
    #[test]
    fn the_parts_of_e0010_follow_the_joins() {
        let text = format!("{BEFORE}a & b | c ^ d << a >> b{AFTER}");
        let p = crate::parse(FileId(0), &text);
        let messages: Vec<(Code, &str)> = p.diagnostics.iter().map(|d| (d.code, d.message.as_str())).collect();
        assert_eq!(
            messages,
            [(
                Code::E0010,
                "`&` and `|` have no strength between them; `|` and `^` have no strength between them; `^` and \
                 `<<` have no strength between them; `<<` and `>>` have no strength between them (§3.1)"
            )]
        );
    }

    #[test]
    fn chains_the_strengths_allow() {
        for src in [
            "x + y - z",
            "x + (y * z)",
            "(lo <= x) && (x < hi)",
            "a && b && c",
            "a +% b -| c",
            "((1.0 - r) * x) + (b1 * y1) - (b2 * y2)",
            "x + y * z",
            "a * b + c * d",
            "lo <= x && x < hi",
            "a + 1 == b",
            "i % 2 == 0",
            "a * b < c % d && ok",
            "w % n % m",
            "x | y | 1",
            "x & y & 1",
            "x ^ y ^ 1",
            "x << 1 << 2",
        ] {
            assert!(check(src).is_empty(), "{src}: {:?}", check(src));
        }
    }

    #[test]
    fn a_candidate_per_reading() {
        let c = candidates;
        assert_eq!(c("a && b || c"), ["(a && b) || c", "a && (b || c)"]);
        assert_eq!(c("a || b && c"), ["(a || b) && c", "a || (b && c)"]);
        assert_eq!(c("a && b || c && d"), ["(a && b) || (c && d)", "a && (b || c) && d"]);
        assert_eq!(c("x & 1 == 0"), ["(x & 1) == 0", "x & (1 == 0)"]);
        assert_eq!(c("x << 1 + y"), ["(x << 1) + y", "x << (1 + y)"]);
        assert_eq!(c("w + 1 % n"), ["(w + 1) % n", "w + (1 % n)"]);
        assert_eq!(c("w * 2 % n"), ["(w * 2) % n", "w * (2 % n)"]);
        assert_eq!(c("a + b % c + d"), ["(a + b) % (c + d)", "a + (b % c) + d"]);
        assert_eq!(c("i + 1 % n < m"), ["(i + 1) % n < m", "i + (1 % n) < m"]);
        assert_eq!(c("x & y | 1"), ["(x & y) | 1", "x & (y | 1)"]);
        // Three groups: the one that appears first is the stronger one first.
        assert_eq!(c("x & 1 == 0 && ok"), ["(x & 1) == 0 && ok", "(x & (1 == 0)) && ok", "x & (1 == 0 && ok)"]);
        // More than three readings: no candidate.
        assert!(c("x & 1 == 0 && a || b").is_empty());
        assert!(c("a & b | c ^ d").is_empty());
    }

    #[test]
    fn chains_of_comparisons() {
        let c = candidates;
        assert_eq!(c("a < b < c"), ["a < b && b < c"]);
        assert_eq!(c("a == b == c"), ["a == b && b == c"]);
        assert_eq!(c("a < p.x < c"), ["a < p.x && p.x < c"]);
        assert_eq!(c("a < t.0 <= F32.PI"), ["a < t.0 && t.0 <= F32.PI"]);
        assert_eq!(c("a < -1 < c"), ["a < -1 && -1 < c"]);
        assert_eq!(c("a < b < c < d"), ["a < b && b < c && c < d"]);
        // An operand of `&&` then.
        assert_eq!(c("a < b < c || d"), ["(a < b && b < c) || d"]);
        assert_eq!(c("a + 1 < b < c && d"), ["a + 1 < b && b < c && d"]);
        // On the right of `&&`, written out with no parentheses.
        assert_eq!(c("p && a < b < c"), ["p && a < b && b < c"]);
        assert_eq!(c("a < b < c && p"), ["a < b && b < c && p"]);
        // A middle evaluated twice: no candidate.
        assert!(c("a < g(b) < c").is_empty());
        assert!(c("a < (b) < c").is_empty());
        assert!(c("a < x & b < c").is_empty());
    }

    /// The examples of `onsa explain E0010` read as the table of the
    /// strengths reads them: `// OK`, or `// E0010: <candidate> or <candidate>`.
    #[test]
    fn the_explanation_of_e0010_agrees_with_the_strengths() {
        let text = include_str!("../../onsa_diag/explain/E0010.md");
        let mut seen = 0;
        for line in text.lines().filter(|l| l.starts_with("let ")) {
            let (code, comment) = line.split_once("//").expect("a comment");
            let expr = code.split_once('=').expect("a `let`").1.trim();
            let got = all(expr);
            if comment.trim().starts_with("OK") {
                assert!(got.is_empty(), "{line}: {got:?}");
            } else {
                let want = comment.trim().strip_prefix("E0010:").expect("`OK` or `E0010:`");
                let want: Vec<String> = want.split(" or ").map(|s| s.trim().to_string()).collect();
                assert_eq!(got, vec![(Code::E0010, want)], "{line}");
            }
            seen += 1;
        }
        assert!(seen >= 6, "the examples were read: {seen}");
    }

    /// The message, the titles and the candidates of the one E0010 of `src`.
    fn shown(src: &str) -> (String, Vec<String>, Vec<String>) {
        let text = format!("{BEFORE}{src}{AFTER}");
        let p = crate::parse(FileId(0), &text);
        assert_eq!(p.diagnostics.len(), 1, "{src}: {:?}", p.diagnostics);
        let d = &p.diagnostics[0];
        assert_eq!(d.code, Code::E0010, "{src}");
        let titles = d.fixes.iter().map(|f| f.title().to_string()).collect();
        (d.message.clone(), titles, candidates(src))
    }

    /// Whether the message and every title show every reading, or none does
    /// (S-345: one decision for both).
    fn shows_readings(src: &str) -> bool {
        let (message, titles, readings) = shown(src);
        assert_eq!(titles.len(), readings.len(), "{src}");
        let in_message = readings.iter().filter(|r| message.contains(&format!("`{r}`"))).count();
        let in_titles = titles.iter().zip(&readings).filter(|(t, r)| **t == format!("read it as `{r}`")).count();
        let n = readings.len();
        assert!(in_message == in_titles && (in_message == 0 || in_message == n), "{src}: {message:?} {titles:?}");
        if in_titles == 0 {
            let want: Vec<String> = (1..=n).map(|i| format!("reading {i} of {n}")).collect();
            assert_eq!(titles, want, "{src}");
        }
        in_titles == n
    }

    #[test]
    fn the_message_and_the_titles_show_the_readings_of_a_short_line() {
        // 56 characters: over the 47 the titles once had room for.
        let src = "alpha_value && beta_value || gamma_value && delta_value";
        assert!(shows_readings(src));
        let (message, titles, _) = shown(src);
        assert_eq!(
            titles,
            [
                "read it as `(alpha_value && beta_value) || (gamma_value && delta_value)`",
                "read it as `alpha_value && (beta_value || gamma_value) && delta_value`",
            ]
        );
        assert!(message.contains(&format!("`{src}` reads as")), "{message}");
        // One reading: the message writes it.
        assert!(shows_readings("a < b < c"));
        // The threshold counts characters of the chain as written, and is
        // `READINGS_MAX` itself.
        let tail = " + 1 % n";
        let at = "w".repeat(super::READINGS_MAX - tail.len()) + tail;
        assert_eq!(at.chars().count(), super::READINGS_MAX);
        assert!(shows_readings(&at));
    }

    #[test]
    fn neither_shows_the_readings_of_a_long_line() {
        let tail = " + 1 % n";
        let over = "w".repeat(super::READINGS_MAX + 1 - tail.len()) + tail;
        assert!(!shows_readings(&over));
        let (message, _, _) = shown(&over);
        assert!(!message.contains("reads as"), "{message}");
    }

    #[test]
    fn neither_shows_the_readings_of_a_chain_over_lines() {
        assert!(!shows_readings("a && b ||\n    c && d"));
        assert!(!shows_readings("a < b <\n    c"));
        assert!(!super::shows_readings("a\r+ b"));
    }

    #[test]
    fn cast_as_operand() {
        assert_eq!(check("acc + x as F64"), vec![(Code::E0011, Some("acc + (x as F64)".into()))]);
        assert!(check("acc + (x as F64)").is_empty());
        assert!(check("-x as F64").is_empty());
    }

    #[test]
    fn chained_casts() {
        assert_eq!(check("x as I64 as F64"), vec![(Code::E0011, Some("(x as I64) as F64".into()))]);
        assert_eq!(check("x as I16 as I32 as F64"), vec![(Code::E0011, Some("((x as I16) as I32) as F64".into()))]);
        assert!(check("(x as I64) as F64").is_empty());
    }

    #[test]
    fn clocks_as_operands_and_chained() {
        // §3.1, S-118: `at` has the strength of `as`.
        assert_eq!(check("acc + x at sample"), vec![(Code::E0011, Some("acc + (x at sample)".into()))]);
        assert_eq!(check("x at block at sample"), vec![(Code::E0011, Some("(x at block) at sample".into()))]);
        assert_eq!(check("n as F32 at sample"), vec![(Code::E0011, Some("(n as F32) at sample".into()))]);
        assert_eq!(check("n at sample as F32"), vec![(Code::E0011, Some("(n at sample) as F32".into()))]);
        assert!(check("-x at sample").is_empty());
        assert!(check("(x at block) at sample").is_empty());
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

    /// E0013 (§3.1, S-537): a block-like expression as an operand.
    #[test]
    fn block_like_operands() {
        let e = |src: &str, fixed: &str| assert_eq!(check(src), vec![(Code::E0013, Some(fixed.into()))], "{src}");
        // The sides of a binary operator, a prefix, the receivers, `as` and `at`.
        e("if c { 1 } else { 2 } + 10", "(if c { 1 } else { 2 }) + 10");
        e("10 + if c { 1 } else { 2 }", "10 + (if c { 1 } else { 2 })");
        e("-if c { 1 } else { 2 }", "-(if c { 1 } else { 2 })");
        e("!{ b }", "!({ b })");
        e("if c { xs } else { ys }[1]", "(if c { xs } else { ys })[1]");
        e("{ n }.abs()", "({ n }).abs()");
        e("{ t }.0", "({ t }).0");
        e("{ r }?", "({ r })?");
        e("{ v }.push!(1)", "({ v }).push!(1)");
        e("fn(x: I32) -> I32 { x }.(3)", "(fn(x: I32) -> I32 { x }).(3)");
        e("{ n } as F64", "({ n }) as F64");
        e("{ n } at sample", "({ n }) at sample");
        // The nine forms.
        e("if~ c { x } else { 0.0 } + x", "(if~ c { x } else { 0.0 }) + x");
        e("match o { _ => 1 } + 1", "(match o { _ => 1 }) + 1");
        e("match~ o { _ => x } + 1", "(match~ o { _ => x }) + 1");
        e("unsafe { n } + 10", "(unsafe { n }) + 10");
        e("handle { 1 } with h + 10", "(handle { 1 } with h) + 10");
        e("par i in 0..<2 { x } + x", "(par i in 0..<2 { x }) + x");
        // One expression is one form: all its block-like operands, in one candidate.
        e("if a { 1 } else { 2 } + match o { _ => 1 }", "(if a { 1 } else { 2 }) + (match o { _ => 1 })");
        e("-{ n } * 2 + { m }.abs()", "-({ n }) * 2 + ({ m }).abs()");
        e("10 + if c { 1 } else { 2 } + 100", "10 + (if c { 1 } else { 2 }) + 100");
        // Parentheses close an expression: inside them is another one.
        let d = check("(a + { 1 }) * { 2 }");
        assert_eq!(d.len(), 2, "{d:?}");
        assert!(d.contains(&(Code::E0013, Some("(a + ({ 1 })) * { 2 }".into()))), "{d:?}");
        assert!(d.contains(&(Code::E0013, Some("(a + { 1 }) * ({ 2 })".into()))), "{d:?}");
        // With E0011 on the same expression, each is an error of its own.
        let d = check("if c { n } else { 2 } as F64 * 2.0");
        assert_eq!(d.len(), 2, "{d:?}");
        assert!(d.contains(&(Code::E0013, Some("(if c { n } else { 2 }) as F64 * 2.0".into()))), "{d:?}");
        // E0013 is the one reported (its span ends first), so the candidate
        // of E0011 is not completed with the parentheses (`crate::operands`).
        assert!(d.contains(&(Code::E0011, Some("(if c { n } else { 2 } as F64) * 2.0".into()))), "{d:?}");
        // The whole positions, the parenthesized operands, and a struct literal.
        for src in [
            "if c { 1 } else { 2 }",
            "(if c { 1 } else { 2 }) + 10",
            "-(match o { _ => 1 })",
            "(fn(x: I32) -> I32 { x }).(3)",
            "two(if c { 1 } else { 2 }, { n })",
            "[{ 1 }, if c { 1 } else { 2 }]",
            "(if c { 1 } else { 2 }, { n })",
            "P { x: if c { 1 } else { 2 } }",
            "xs[if c { 0 } else { 1 }]",
            "match o { _ => if c { 1 } else { 2 } }",
            "{ if c { 1 } else { 2 } }",
            "P { x: 1 }.x",
            "fn(x: I32) -> I32 { x }",
        ] {
            assert!(check(src).is_empty(), "{src}: {:?}", check(src));
        }
    }
}
