//! Post-parse checks on operator chains (spec §3.1): E0010 (an operator of a
//! chain with an operand the strengths of the groups do not allow), E0011
//! (`as` as a bare operand, and `as` chained), E0012 (stacked prefix
//! operators).
//!
//! A chain is the tree of §3.1 in the AST ([`Chain`]). The candidates of
//! E0010 (S-60, §18.1) are the readings of the chain with temporary
//! strengths placed on the groups that clash, one per placement.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::ast::{Ast, BinOp, Chain, ExprId, ExprKind, Lit, OpGroup, Side, StrSeg, UnOp};

/// The checks of this module on the AST of one file. `deepest` is the
/// deepest unit of the file in levels (spec §2.5), for the candidates that
/// add parentheses.
pub(crate) fn check(ast: &Ast, text: &str, deepest: u32, diagnostics: &mut Vec<Diagnostic>) {
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
    // The operators under another one of their chain, and the casts under
    // another cast (a chain of `as` is one form, as a stack is).
    let mut inner = HashSet::new();
    for e in &ast.exprs {
        match e.kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                inner.extend([lhs, rhs].into_iter().filter(|&c| matches!(ast.expr(c).kind, ExprKind::Binary { .. })));
            }
            ExprKind::Cast { expr, .. } if matches!(ast.expr(expr).kind, ExprKind::Cast { .. }) => {
                inner.insert(expr);
            }
            _ => {}
        }
    }
    for (i, expr) in ast.exprs.iter().enumerate() {
        let id = ExprId(i as u32);
        match expr.kind {
            ExprKind::Binary { .. } => {
                if inner.contains(&id) {
                    continue;
                }
                let chain = Flat::new(ast, text, id);
                // E0011: a cast is parenthesized as an operand of a chain;
                // SPEC-GAP(S-348): the casts of one chain are one form,
                // parenthesized whole.
                let casts: Vec<Span> = chain
                    .operands
                    .iter()
                    .map(|&o| ast.expr(o))
                    .filter(|e| matches!(e.kind, ExprKind::Cast { .. }))
                    .map(|e| e.span)
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
                        "`as` is written in parentheses when it is an operand (§3.3)",
                    )
                    .with_found(src(first))
                    .with_fix(Fix::new("parenthesize the cast", edits));
                    diagnostics.push(d);
                }
                if let Some(d) = chain.check(deepest) {
                    diagnostics.push(d);
                }
            }
            ExprKind::Cast { expr: mut e, .. }
                if !inner.contains(&id) && matches!(ast.expr(e).kind, ExprKind::Cast { .. }) =>
            {
                // E0011: `x as A as B` is `(x as A) as B` written out (§3.1).
                let mut closes = Vec::new();
                while let ExprKind::Cast { expr: base, .. } = ast.expr(e).kind {
                    closes.push(Edit::insert(expr.span.file, ast.expr(e).span.end, ")"));
                    e = base;
                }
                let mut edits = vec![Edit::insert(expr.span.file, expr.span.start, "(".repeat(closes.len()))];
                edits.extend(closes.into_iter().rev());
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0011,
                    expr.span,
                    "`as` is not chained; parenthesize the inner cast (§3.1)",
                )
                .with_found(src(expr.span))
                .with_fix(Fix::new("parenthesize the inner cast", edits));
                diagnostics.push(d);
            }
            ExprKind::Unary { .. } if stacked(id) && !inner_of_a_stack.contains(&id) => {
                // The operators of the stack, outermost first: each but the
                // last takes the rest in parentheses (`- - -x` is
                // `-(-(-x))`); the blanks between two operators give way
                // to the `(`.
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
                edits.push(Edit::insert(expr.span.file, expr.span.end, ")".repeat(ops.len() - 1)));
                let d = Diagnostic::new(
                    Stage::Syntax,
                    Code::E0012,
                    expr.span,
                    "prefix operators are not stacked; parenthesize the inner operator (§3.1)",
                )
                .with_found(src(expr.span))
                .with_fix(Fix::new("parenthesize the inner operator", edits));
                diagnostics.push(d);
            }
            _ => {}
        }
    }
}

/// The keys of strength: the groups, the bitwise group one key per operator
/// (§18.1: its operators clash as groups of their own; one operator chains
/// with itself, S-61).
const KEYS: usize = 11;

fn key(op: BinOp) -> usize {
    match op.group() {
        OpGroup::Additive => 0,
        OpGroup::Multiplicative => 1,
        OpGroup::Remainder => 2,
        OpGroup::Comparison => 3,
        OpGroup::And => 4,
        OpGroup::Or => 5,
        OpGroup::Bitwise => match op {
            BinOp::BitAnd => 6,
            BinOp::BitOr => 7,
            BinOp::BitXor => 8,
            BinOp::Shl => 9,
            _ => 10,
        },
    }
}

/// The group of a key that is not a bitwise operator.
const GROUPS: [OpGroup; 6] =
    [OpGroup::Additive, OpGroup::Multiplicative, OpGroup::Remainder, OpGroup::Comparison, OpGroup::And, OpGroup::Or];

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
}

impl<'a> Flat<'a> {
    fn new(ast: &'a Ast, text: &'a str, root: ExprId) -> Flat<'a> {
        let (mut operands, mut ops) = (Vec::new(), Vec::new());
        // In order, without recursion (a chain is up to 256 levels high).
        let mut right = Vec::new();
        let mut e = root;
        loop {
            if let ExprKind::Binary { op, lhs, rhs, .. } = ast.expr(e).kind {
                right.push((op, rhs));
                e = lhs;
                continue;
            }
            operands.push(e);
            let Some((op, rhs)) = right.pop() else { break };
            ops.push(op);
            e = rhs;
        }
        Flat { ast, text, span: ast.expr(root).span, operands, ops }
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
            chain.operator(o, |o: usize, w: usize| order.tighter(key(self.ops[o]), key(self.ops[w]), undecided), join);
            chain.operand(push(Node::Operand(o + 1)));
        }
        chain.finish(join);
        Reading(nodes.into_inner())
    }

    /// The readings of the chain, one per placement of strengths on the keys
    /// that clash (S-60), in the order of §18.1: at each pair without a
    /// strength, met from the left, the key that appears first in the
    /// expression is taken as the stronger one first. Each pair decided one
    /// way or the other makes a different tree, so the readings differ;
    /// more than three are not all made.
    // SPEC-GAP(S-347): the order of the readings of three groups or more.
    fn readings(&self) -> (Vec<Reading>, bool) {
        let mut first = [usize::MAX; KEYS];
        for (i, &op) in self.ops.iter().enumerate().rev() {
            first[key(op)] = i;
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

/// The longest chain, in characters, whose readings the message shows.
const MESSAGE_READINGS_MAX: usize = 80;

/// The title of a candidate that shows its reading, around the reading.
const TITLE_BEFORE: &str = "read it as `";
const TITLE_AFTER: &str = "`";

/// The title that shows `reading`, when it fits on one line of at most
/// [`onsa_diag::TITLE_MAX`] characters.
fn reading_title(reading: &str) -> Option<String> {
    let room = onsa_diag::TITLE_MAX - TITLE_BEFORE.chars().count() - TITLE_AFTER.chars().count();
    (reading.chars().count() <= room && !reading.contains(['\n', '\r']))
        .then(|| format!("{TITLE_BEFORE}{reading}{TITLE_AFTER}"))
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
    /// E0010 for the chain, when one of its operators has an operand the
    /// strengths of §3.1 do not allow ([`BinOp::takes`]): one diagnostic
    /// for the chain (one form), with a candidate per reading (S-60).
    // SPEC-GAP(S-344): groups without a strength between them that are not
    // next to each other in the tree (`a % b == c + d`) pass: the judgment
    // is on the edges of the tree.
    fn check(&self, deepest: u32) -> Option<Diagnostic> {
        let actual = self.read(&Order::of_the_spec(), &mut None);
        let mut parts: Vec<String> = Vec::new();
        let mut said = HashSet::new();
        for &n in &actual.0 {
            let Node::Op(o, l, r) = n else { continue };
            for (side, c) in [(Side::Left, l), (Side::Right, r)] {
                let Node::Op(co, ..) = actual.0[c] else { continue };
                let (op, child) = (self.ops[o], self.ops[co]);
                if op.takes(side, child) {
                    continue;
                }
                let part = if key(op) == key(child) {
                    format!("`{}` cannot be chained", op.symbol())
                } else {
                    let (a, b) = if co < o { (child, op) } else { (op, child) };
                    format!("`{}` and `{}` have no strength between them", a.symbol(), b.symbol())
                };
                if said.insert((key(op).min(key(child)), key(op).max(key(child)))) {
                    parts.push(part);
                }
            }
        }
        if parts.is_empty() {
            return None;
        }
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
                Ok(ins) if self.nests_too_deep(&ins, deepest) => {
                    rule = Some("bind a part of it with `let`: parenthesizing it nests deeper than the limit (§2.5)");
                }
                Ok(ins) => candidates.push(ins),
            }
        }
        let texts: Vec<String> = candidates.iter().map(|ins| self.reading_text(ins)).collect();
        // SPEC-GAP(S-345): a long chain, or one over lines, has its readings
        // in the candidates only, not in the message or the titles.
        if !texts.is_empty() && found.chars().count() <= MESSAGE_READINGS_MAX && !found.contains('\n') {
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
            let title = reading_title(&text).unwrap_or_else(|| format!("reading {} of {n}", i + 1));
            let edits = ins.into_iter().map(|(at, s)| Edit::insert(self.span.file, at, s)).collect();
            d = d.with_fix(Fix::new(title, edits));
        }
        Some(d)
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
            ExprKind::Unary { op: UnOp::Neg, expr } => {
                let mut e = *expr;
                while let ExprKind::Paren(inner) = self.ast.expr(e).kind {
                    e = inner;
                }
                matches!(self.ast.expr(e).kind, ExprKind::Lit(Lit::Int { .. } | Lit::Float { .. }))
            }
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
    /// candidate is not made). The parser counts it, on the file with the
    /// candidate, when the deepest unit and the levels the candidate may
    /// add are over the limit.
    fn nests_too_deep(&self, ins: &Inserts, deepest: u32) -> bool {
        let added = ins.values().map(|s| s.matches(['(', '&']).count() as u32).sum::<u32>() + self.ops.len() as u32;
        if deepest + added <= crate::parser::NESTING_LIMIT {
            return false;
        }
        let file = self.span.file;
        let text = inserted(self.text, 0, ins);
        let longer: u32 = ins.values().map(|s| s.len() as u32).sum();
        let out = crate::parser::Parser::new(file, &text, crate::lex(file, &text)).parse_file();
        out.diagnostics
            .iter()
            .any(|d| d.code == Code::E0006 && self.span.start <= d.span.start && d.span.start < self.span.end + longer)
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

    #[test]
    fn a_title_shows_its_reading_when_it_fits() {
        let room = onsa_diag::TITLE_MAX - super::TITLE_BEFORE.len() - super::TITLE_AFTER.len();
        let fits = "x".repeat(room);
        assert_eq!(super::reading_title(&fits).map(|t| t.chars().count()), Some(onsa_diag::TITLE_MAX));
        assert_eq!(super::reading_title(&"x".repeat(room + 1)), None);
        // Characters, not bytes.
        assert!(super::reading_title(&"é".repeat(room)).is_some());
        assert_eq!(super::reading_title("a\n+ b"), None);
        // The title of each candidate of a chain one character too long for it.
        let name = "w".repeat(room - "(".len() - " + 1) % n".len() + 1);
        let text = format!("{BEFORE}{name} + 1 % n{AFTER}");
        let p = crate::parse(FileId(0), &text);
        let titles: Vec<&str> = p.diagnostics[0].fixes.iter().map(|f| f.title()).collect();
        assert_eq!(titles, ["reading 1 of 2", "reading 2 of 2"]);
        let name = "w".repeat(room - "(".len() - " + 1) % n".len());
        let text = format!("{BEFORE}{name} + 1 % n{AFTER}");
        let p = crate::parse(FileId(0), &text);
        assert_eq!(p.diagnostics[0].fixes[0].title(), format!("read it as `({name} + 1) % n`"));
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
