//! The type arguments of an expression written `name[A, B]` with no `::`
//! (§4.5, S-329): the parser reads the list whole, as the list of
//! `name::[A, B]` (a `TypeArgsExpr` with no `::`), and the row
//! `type_args_square_comma` is found on the tree after parsing, with the
//! candidates of its two readings (S-333, S-975, R-418).

use std::cell::OnceCell;
use std::collections::HashMap;

use onsa_diag::{Diagnostic, Edit, Fix, FixRule, Span, Stage};

use super::{Hit, RowId, TYPE_ARGS_WITH_COLONS, diagnostic};
use crate::ast::BinOp;
use crate::callee::{Callee, Link};
use crate::cst::{Class, Cst, NodeId, NodeKind, TokenIdx};
use crate::literal::Literals;
use crate::scan::Brackets;
use crate::token::TokenKind;

/// The title of the candidate of the multi-dimensional index (S-333).
const AS_AN_INDEX: &str = "index with each element in brackets of its own";

/// The E0020 of each `TypeArgsExpr` with no `::`, read whole or not (the
/// `[` is before any error in it, §18.1), from its `[` to its `]`, or from
/// the `[` to the `]` of the outermost index whose content reads as a type
/// (S-975). A list in another reported one is not reported: one diagnostic
/// per unit, the outer first (§18.1). The candidates are the `::` of a list
/// that reads as type arguments (before the outermost `[`, S-975) and the
/// index form (S-333); with neither, the row's E0002.
pub(crate) fn square_lists(cst: &Cst, text: &str, literals: &Literals, out: &mut Vec<Diagnostic>) {
    let tokens = cst.tokens();
    let brackets = OnceCell::new();
    // Whether the content of an index reads as a type, read once (S-975).
    let mut contents = HashMap::new();
    let mut reported_to = 0;
    for (i, t) in tokens.iter().enumerate() {
        if t.kind != TokenKind::LBracket || i < reported_to {
            continue;
        }
        let list = cst.token_parent(TokenIdx(i as u32));
        let Some(expr) = cst.parent(list).filter(|&e| cst.kind(e) == NodeKind::TypeArgsExpr) else { continue };
        if cst.kind(list) != NodeKind::TypeArgs
            || cst.child_tokens(expr).any(|c| cst.token(c).kind == TokenKind::ColonColon)
        {
            continue;
        }
        let read = Reading { cst, text, literals, brackets: Brackets::of(&brackets, tokens) };
        // The parser read the list after `type_list_ahead`: a `]` closes it.
        let close = read.brackets.contents(i).map_or_else(
            || onsa_diag::internal::bug(Some(t.span), "a list of type arguments with no `::` and no `]` with `,`"),
            |c| c.0,
        );
        // A list the parser stopped in at a form of another language (an
        // E0020 of a row, and no other error in it) reads up to it (§18.1).
        let inside = || {
            out.iter()
                .filter(|d| d.stage == Stage::Syntax && (t.span.end..=tokens[close].span.start).contains(&d.span.start))
        };
        let partial = !cst.is_complete(list)
            && inside().next().is_some()
            && inside().all(|d| d.code.fix_rule() == FixRule::Syntax);
        let types = type_arg(cst, list, partial);
        let (open, end) = types.then(|| read.outermost(expr, &mut contents)).flatten().unwrap_or((i, close));
        reported_to = end;
        let colons = Edit::insert(t.span.file, tokens[open].span.start, "::");
        let index = read.index_form(i, close).filter(|_| index_keeps_what_follows(cst, expr));
        let fixes = types.then(|| Fix::new(TYPE_ARGS_WITH_COLONS, vec![colons])).into_iter().chain(index);
        let span = Span::new(t.span.file, tokens[open].span.start, tokens[end].span.end);
        out.push(diagnostic(text, RowId::TypeArgsSquareComma, Hit::new(span, fixes.collect())));
    }
}

/// Whether the node `n` reads as a type argument or a part of one (§4.5,
/// S-333): complete, and each expression in it (a const argument, the
/// length of an array type) a constant expression ([`constant`]). A list of
/// type arguments reads as one when its elements do. With `partial`, a node
/// the parser stopped in reads when its nodes read (a form of another
/// language in it, §18.1). The forms are those of
/// the syntax; `onsa_sema`'s `constarg.rs` checks the same grammar on the AST
/// ([`crate::ast::Ast::const_form`]), with the same operators
/// ([`BinOp::in_constant`]); the two are compared by `constexpr_tests`.
fn type_arg(cst: &Cst, n: NodeId, partial: bool) -> bool {
    if !cst.is_complete(n) {
        return partial && cst.child_nodes(n).all(|c| type_arg(cst, c, partial));
    }
    match cst.kind(n).class() {
        Class::Expr => constant(cst, n, partial),
        _ => cst.child_nodes(n).all(|c| type_arg(cst, c, partial)),
    }
}

/// Whether the expression `n` has the form of a constant expression of
/// §4.5: an integer literal, a name, a path of names and a member of a type
/// with type arguments (`Rg::[F32, 4].CAP`, `Rg[F32, 4].CAP`), the operators
/// `+ - * / %`, a prefix `-`, parentheses. `as`, `!`, `?`, comparisons,
/// calls, strings and floats are not (S-333, R-418). `partial` as for
/// [`type_arg`].
pub(crate) fn constant(cst: &Cst, n: NodeId, partial: bool) -> bool {
    use TokenKind::*;
    let tokens_are =
        |ok: &dyn Fn(TokenKind) -> bool| cst.child_tokens(n).map(|t| cst.token(t).kind).all(|k| !k.is_code() || ok(k));
    let nodes = || cst.child_nodes(n);
    if !cst.is_complete(n) {
        return type_arg(cst, n, partial);
    }
    match cst.kind(n) {
        NodeKind::Literal => tokens_are(&|k| k == Int),
        NodeKind::PathExpr => true,
        NodeKind::ParenExpr => nodes().all(|c| constant(cst, c, partial)),
        NodeKind::BinaryExpr => {
            tokens_are(&|k| k.binop().is_some_and(BinOp::in_constant)) && nodes().all(|c| constant(cst, c, partial))
        }
        NodeKind::PrefixExpr => tokens_are(&|k| k == Minus) && nodes().all(|c| constant(cst, c, partial)),
        NodeKind::FieldExpr => nodes().next().is_some_and(|r| match cst.kind(r) {
            NodeKind::PathExpr | NodeKind::FieldExpr => constant(cst, r, partial),
            NodeKind::TypeArgsExpr => cst.child_nodes(r).all(|c| match cst.kind(c) {
                NodeKind::TypeArgs => type_arg(cst, c, partial),
                _ => constant(cst, c, partial),
            }),
            _ => false,
        }),
        _ => false,
    }
}

/// Whether the list `expr` written as indexes is read with what follows
/// its `]` as the list is (§18.1: the promise of a candidate, as for a
/// function type in the list): the chain with two indexes for the list,
/// and each postfix over it taken as the parser takes it
/// ([`Callee::takes`]). `mk().m[I32][F32](1)` is a call of a value (§6.1,
/// S-191), `Rg[F32][4] { d: x }` no struct literal, `delay[F32][4]~(x)` a
/// mark after a value: each an error of the syntax stage.
fn index_keeps_what_follows(cst: &Cst, expr: NodeId) -> bool {
    use NodeKind::*;
    let postfix = |n| {
        matches!(cst.kind(n), FieldExpr | IndexExpr | TypeArgsExpr | CallExpr | TryExpr | TupleIndexExpr | StructLit)
    };
    let mut links = Vec::new();
    let mut link = cst.child_nodes(expr).next();
    while let Some(n) = link {
        links.push(cst.kind(n));
        link = cst.child_nodes(n).next().filter(|_| postfix(n));
    }
    let Some(first) = links.pop() else { return true };
    let mut callee = links.into_iter().rev().fold(Callee::start(first), Callee::then).then(IndexExpr).then(IndexExpr);
    let mut n = expr;
    while let Some(p) = cst.parent(n).filter(|&p| postfix(p) && cst.child_nodes(p).next() == Some(n)) {
        let mark = cst.child_tokens(p).next().map(|t| cst.token(t).kind);
        if !callee.takes(cst.kind(p), mark) {
            return false;
        }
        (callee, n) = (callee.then(cst.kind(p)), p);
    }
    true
}

/// Whether an expression node of `kind` is shaped as a type around what is
/// in it (parentheses, a tuple, an array `[T; N]`): the walk to the
/// outermost index goes through it, and the index's content is read whole
/// as a type (§4.5, S-975).
fn shaped_as_a_type(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::ParenExpr | NodeKind::TupleExpr | NodeKind::RepeatExpr)
}

/// What the candidates of a list read besides its tree.
struct Reading<'a> {
    cst: &'a Cst,
    text: &'a str,
    literals: &'a Literals,
    brackets: &'a Brackets,
}

impl Reading<'_> {
    /// The `[` and `]` of the outermost index whose content holds the list
    /// `expr` and reads as a type (S-975): an index after a path of names or
    /// a method, from `expr` up through parentheses and such indexes as long
    /// as each content reads as a type (`id[Option[Result[I32, Str]]](x)`,
    /// `Q[Rg[F32, 4]].CAP`, S-999). None when there is none. Whether an
    /// index's content reads as a type is kept in `types`, so that the lists
    /// in one index read it once.
    fn outermost(&self, expr: NodeId, types: &mut HashMap<NodeId, bool>) -> Option<(usize, usize)> {
        let (cst, mut child, mut found) = (self.cst, expr, None);
        while let Some(n) = cst.parent(child) {
            match cst.kind(n) {
                k if shaped_as_a_type(k) => {}
                NodeKind::IndexExpr
                    if cst.is_complete(n)
                        && cst
                            .child_nodes(n)
                            .next()
                            .is_some_and(|r| r != child && Link::of(cst.kind(r)).names_a_path()) =>
                {
                    let mut marks = cst.child_tokens(n).filter(|&t| cst.token(t).kind.is_code());
                    let (Some(open), Some(close)) = (marks.next(), marks.next()) else { break };
                    let (open, close) = (open.index(), close.index());
                    let tokens = cst.tokens();
                    let file = tokens[open].span.file;
                    let reads = *types.entry(n).or_insert_with(|| {
                        crate::parser::reads_as_type(file, self.text, tokens, self.literals, (open + 1, close - 1))
                    });
                    if !reads {
                        break;
                    }
                    found = Some((open, close));
                }
                _ => break,
            }
            child = n;
        }
        found
    }

    /// The index form of the list from the `[` at `open` to the `]` at
    /// `close` (S-333): each `,` directly in it, with the blanks after it on
    /// its line, becomes `][`, and a `,` before the `]` is dropped. None
    /// when an element does not read as an expression (a function type,
    /// nothing; §18.1; `_` is a hole, an expression) or a bracket in it closes one of another kind.
    fn index_form(&self, open: usize, close: usize) -> Option<Fix> {
        let tokens = self.cst.tokens();
        let file = tokens[open].span.file;
        // An element, its blanks and comments inside it kept (gaps are read).
        let reads = |run: &[crate::token::Token]| {
            let code = |t: &&crate::token::Token| t.kind.is_code();
            let (Some(a), Some(b)) = (run.iter().position(|t| code(&t)), run.iter().rposition(|t| code(&t))) else {
                return false;
            };
            // An element is in brackets: a `{` in it is a struct literal (§4.4, S-376).
            crate::parser::reads_as_expr(file, self.text, run[a..=b].to_vec(), self.literals, false)
        };
        let (mut edits, mut from, mut k) = (Vec::new(), open + 1, open + 1);
        while k < close {
            if matches!(tokens[k].kind, TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace) {
                k = self.brackets.closing(k)?;
            } else if tokens[k].kind == TokenKind::Comma {
                if !reads(&tokens[from..k]) {
                    return None;
                }
                let blank = tokens[k + 1].kind == TokenKind::Whitespace;
                let span = Span::new(file, tokens[k].span.start, tokens[if blank { k + 1 } else { k }].span.end);
                from = k + 1;
                if tokens[from..close].iter().all(|t| !t.kind.is_code()) {
                    edits.push(Edit::delete(span));
                    return Some(Fix::new(AS_AN_INDEX, edits));
                }
                edits.push(Edit::replace(span, "]["));
            }
            k += 1;
        }
        reads(&tokens[from..close]).then(|| Fix::new(AS_AN_INDEX, edits))
    }
}
