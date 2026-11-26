//! The rows of the line breaks where a symbol touches its partner (§2.5,
//! W3-06): after a member `.` (S-353), after a prefix `-` / `!` / `^` and
//! before a postfix `?` (S-369). The candidate moves the symbol to its
//! partner's line ([`super::edits::move_token_down`],
//! [`super::edits::move_token_up`]). And the symbols at the head of a line
//! that go at the end of the line before (S-124, S-370, S-374, S-380), the
//! `|` and `||` of a pattern out of their place (S-383, S-389), and the
//! prefix `+` that Onsa has not (S-405).

use super::edits::{move_token_down, move_token_up};
use super::lists::comma_before_sign;
use super::*;
use crate::ast::{BinOp, Chain, Operand, Side};
use crate::edits::move_up;
use crate::scan::arm_ahead;

/// A line break after a member `.` (`s.` and `f` on the next line, also in
/// a list; S-353): the `.` moves to the head of the next line, before a
/// name, a tuple index or the `(` of `.(`. Before anything else the form
/// has no candidate (E0002 with the note).
pub(super) fn newline_after_dot(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Postfix || c.kind(c.at) != TokenKind::Dot || c.gap_after(c.at) != Gap::Newline {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    // A name, a tuple index or the `(` of `.(` (§2.5); a keyword starts the
    // next statement (`let c = s.` and `let d = 1`), which the `.` would join.
    let member = crate::starts::starts_member(next);
    let fixes = if member {
        move_token_down(c, "move the `.` to the next line", c.at).into_iter().collect()
    } else {
        Vec::new()
    };
    hit(c.span(c.at), fixes)
}

/// A line break after a prefix `-` / `!` / `^` (`two(-` and `a, 1)` on the
/// next line; `let y = -` and `a`; S-369): the symbol moves to its
/// operand's line. Before what no operand starts (and no name, for `^`) the
/// form has no candidate.
pub(super) fn newline_after_prefix(c: &Cursor) -> Option<Hit> {
    let kind = c.kind(c.at);
    let want = if kind == TokenKind::Caret { Want::Expr } else { Want::Prefix };
    if !matches!(kind, TokenKind::Minus | TokenKind::Bang | TokenKind::Caret)
        || c.want != want
        || c.gap_after(c.at) != Gap::Newline
    {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    let operand = if kind == TokenKind::Caret { next == TokenKind::Ident } else { crate::starts::starts_operand(next) };
    let fixes = if operand {
        move_token_down(c, "write it against its operand", c.at).into_iter().collect()
    } else {
        Vec::new()
    };
    hit(c.span(c.at), fixes)
}

/// A line break before a postfix `?` (`two(o` and `?, 1)` on the next line;
/// `let v = o` and `?`; S-369): the `?` moves up to its operand, where the
/// chain of an expression would read it ([`Cursor::question_detached`],
/// R-214).
pub(super) fn newline_before_question(c: &Cursor) -> Option<Hit> {
    if !c.question_detached() || !c.at_line_head(c.at) {
        return None;
    }
    hit(c.span(c.at), move_token_up(c, "write it against its operand", c.at).into_iter().collect())
}

/// Whether the failure is inside a pattern: where one starts, after one
/// that closed there, or in a list of patterns.
fn in_pattern(c: &Cursor) -> bool {
    use crate::cst::Class;
    // The innermost node that closed there and is an expression, a type or a
    // pattern (a name's path inside a pattern is none of them: `Red`).
    let innermost = c.closed.iter().find(|n| n.0.class() != Class::Other);
    c.want == Want::Pattern
        || innermost.is_some_and(|n| n.0.class() == Class::Pat)
        || matches!(c.want, Want::Separator(NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::StructPat))
}

/// The rows [`leading_symbol`] names ([`super::Matcher::many`]).
pub(super) const LEADING_SYMBOL_ROWS: &[RowId] = &[RowId::LeadingOperator, RowId::LeadingMinus];

/// A symbol at the head of a line that goes at the end of the line before
/// (§2.5): an operator only binary (`leading_operator`, S-124, S-370), the
/// `|` of a pattern choice (S-380), the `->` of a result and the `=` of a
/// binding or a definition (S-374), or a `-` / `^` that is a prefix too
/// (`leading_minus`). The candidate moves the symbol to the end of the code
/// of the line before, before its comment (S-216); a `- b` with a blank
/// joins the line instead (its blank is an error of its own, so the symbol
/// alone would not do). In a list whose elements are expressions, a `-`,
/// `^` or `+` touching its operand may start the next element too: the `,`
/// is the second candidate ([`comma_before_sign`], S-370, S-405). In the
/// arms of a `match`, a symbol that a `=>` follows starts the next arm
/// (S-386): the missing `,` of the list.
pub(super) fn leading_symbol(c: &Cursor) -> Option<(RowId, Hit)> {
    use TokenKind::*;
    let (s, prev) = leading(c)?;
    let sign = matches!(c.kind(s), Minus | Caret);
    let fixes = match c.gap_after(s) {
        Gap::Newline if sign => return None,
        Gap::Space if sign => joined(c, prev, s).into_iter().collect(),
        gap => moved_to_the_line_before(c, s, prev, gap),
    };
    found(if sign { RowId::LeadingMinus } else { RowId::LeadingOperator }, c.span(s), fixes)
}

/// The candidates of a symbol `s` at the head of a line that moves to the end
/// of the line before (after `prev`), and in a list whose elements are
/// expressions, of a `-`, `^` or `+` touching its operand, the `,` before it
/// (S-370, S-405).
fn moved_to_the_line_before(c: &Cursor, s: usize, prev: usize, gap: Gap) -> Vec<Fix> {
    use TokenKind::*;
    let symbol = &c.text[c.span(s).start as usize..c.span(s).end as usize];
    let title = "move it to the end of the line before";
    let moved = super::edits::move_token_up_as(c, title, s, &format!(" {symbol}"));
    let mut fixes: Vec<Fix> = moved.filter(|_| joins_cleanly(c, prev, s)).into_iter().collect();
    let list = super::lists::expression_list(c);
    let operand = gap == Gap::None && crate::starts::starts_operand(c.kind(s + 1));
    if list && operand && matches!(c.kind(s), Minus | Caret | Plus) {
        fixes.push(comma_before_sign(c, prev, s));
    }
    fixes
}

/// The candidate that joins the line of the symbol `s` at its head to the
/// line before, after its last token `prev`, when the chain reads
/// ([`joins_cleanly`]): of a `- b` or `^ b` with a blank (S-123, S-124). The
/// one place of it, for [`leading_symbol`] and the blank after a prefix
/// (`super::spaces`).
pub(super) fn joined(c: &Cursor, prev: usize, s: usize) -> Option<Fix> {
    let title = "join it to the line before";
    move_up(c.file, c.text, c.all, title, c.span(prev).end, c.tokens[s], " ").filter(|_| joins_cleanly(c, prev, s))
}

/// Whether the binary operator `s` at the head of a line, joined to the line
/// before after its last token `prev`, leaves a chain that reads (§3.1,
/// §18.1, R-443): the operands and operators from the start of the chain
/// before it ([`chain_start`]) to the end of its own line's operand
/// ([`read_chain`]) read as the tree of §3.1 ([`Chain`]), each edge judged
/// by [`BinOp::bare`] (E0010, and E0011 for an operand with `as` or `at`).
/// Where a scan stops at a token it does not know, the chain does not read
/// (R-445: no candidate, as the comparisons of [`super::operators`]).
/// Another symbol joins as it is.
fn joins_cleanly(c: &Cursor, prev: usize, s: usize) -> bool {
    let Some(op) = c.kind(s).binop() else { return true };
    chain_start(c, prev).is_some_and(|from| chain_reads(c, from, s, op, true, false))
}

/// Whether the chain from token `from` with `op` in place of the token `s`
/// ([`read_chain`]) reads as the tree of §3.1 ([`Chain`]), each edge judged
/// by [`BinOp::bare`] (E0010, and E0011 for an operand with `as` or `at`):
/// the one reading of a chain around a symbol, for the symbols joined to
/// the line before ([`joins_cleanly`]) and the comparisons of other
/// languages (`super::operators`). `braces`: whether a `{` may open at its
/// depth (a block-like operand, a struct literal); the comparisons take
/// none (their candidate writes no parentheses, E0013, S-450). `closer`: whether
/// a closer at its depth must close the bracket it is in (the comparisons, R-469).
pub(super) fn chain_reads(c: &Cursor, from: usize, s: usize, op: BinOp, braces: bool, closer: bool) -> bool {
    let Some((operands, ops, braced)) = read_chain(c, from, s, op, closer) else { return false };
    let mut fits = braces || !braced;
    let mut join = |l, o: BinOp, r| {
        fits &= o.bare(Side::Left, l) && o.bare(Side::Right, r);
        Operand::Binary(o)
    };
    let tighter = |o: BinOp, w: BinOp| o.group().stronger(w.group());
    let mut operands = operands.into_iter();
    let mut chain = Chain::new(operands.next().unwrap_or(Operand::Plain));
    for (o, operand) in ops.into_iter().zip(operands) {
        chain.operator(o, tighter, &mut join);
        chain.operand(operand);
    }
    chain.finish(&mut join);
    fits
}

/// The first token of the chain whose last operand ends at `prev`: going
/// back at its depth over the tokens of a chain ([`in_chain`]) and the
/// brackets an operand holds, to the bracket it is in or a token that ends
/// a chain ([`ends_chain`]). A block-like operand (§3.1, S-537) is passed
/// whole: after a block (`{ … }`) the keyword of an `if` with its `else`
/// arms, a `match`, an anonymous function (its `->` too), an `unsafe`, a
/// `handle` or a `par~` (the `in` and the range of its head too) is in it,
/// and the operand ends there (an `if` after an `else` goes on with it);
/// with no block passed since, or after an operand on its line (a guard),
/// an `if` or a `match` is the head the chain is the condition of. None at
/// another token, which the scan does not know (R-445: the `->` of `a as
/// fn(I32) -> I32`; an `in` or a range after a block with no `par~`
/// before), and at the start of the file.
fn chain_start(c: &Cursor, prev: usize) -> Option<usize> {
    use TokenKind::*;
    let (mut i, mut depth, mut braced, mut ranged) = (prev, 0u32, false, false);
    let start = loop {
        let k = c.kind(i);
        match k {
            RParen | RBracket | RBrace => depth += 1,
            LParen | LBracket | LBrace if depth == 0 => break i + 1,
            LParen | LBracket | LBrace => {
                depth -= 1;
                braced |= depth == 0 && k == LBrace;
            }
            _ if depth > 0 || in_chain(c, i) => {}
            KwIf | KwMatch if !braced || after_operand(c, i) => break i + 1 + usize::from(c.kind(i + 1) == Tilde),
            KwElse | Arrow if braced => {}
            DotDotLt | DotDotEq | KwIn if braced => ranged = true,
            KwIf | KwMatch | KwFn | KwUnsafe | KwHandle | KwPar if braced => {
                braced = c.sig_before(i).is_some_and(|p| c.kind(p) == KwElse);
                ranged &= k != KwPar;
            }
            _ if ends_chain(k, true) => break i + 1,
            _ => return None,
        }
        i = i.checked_sub(1)?;
    };
    (!ranged).then_some(start)
}

/// The operands (with `as` or `at` or plain) and the binary operators of the
/// chain from token `from` ([`chain_start`]) with `op` in place of the symbol
/// `s`, to the end of the operand after it: at the depth of `from`, the
/// brackets an operand holds passed, and the head of a block-like operand
/// (from its keyword or `else` to its `{` on its lines) too. It ends at a bracket that
/// closes none (with `closer`, only at the one that closes the bracket `from` is in,
/// R-469), the end of the file, a token that ends a chain
/// ([`ends_chain`]; the line break that ends the line of `s`), and the `{`
/// of the body of the head the failure is in ([`super::operators::in_head`]);
/// a range only in a `for` or `par~` head (§7). None at another token (R-445),
/// a bracket its kind does not close ([`closing`]), another closer with `closer`,
/// and operands and operators that do not alternate ([`alternation`], to an
/// operand at the end). With them, whether a `{` opened at the depth of `from`.
fn read_chain(c: &Cursor, from: usize, s: usize, op: BinOp, closer: bool) -> Option<(Vec<Operand>, Vec<BinOp>, bool)> {
    use TokenKind::*;
    let (mut operands, mut ops, mut depth, mut head) = (vec![Operand::Plain], Vec::new(), 0u32, false);
    let (mut braced, mut expect) = (false, true);
    let ranges = matches!(c.context(), Some((_, NodeKind::ForStmt | NodeKind::ParExpr)));
    let mut i = from;
    loop {
        if i == s {
            if depth > 0 || head || expect {
                return None;
            }
            ops.push(op);
            operands.push(Operand::Plain);
            (i, expect) = (c.sig_after(s), true);
            continue;
        }
        let k = c.kind(i);
        match k {
            Eof => break,
            LBrace if depth == 0 && !head && i > s && super::operators::in_head(c) => break,
            LParen | LBracket | LBrace if depth == 0 && closing(c, i).is_none() => return None,
            LParen | LBracket | LBrace => {
                head &= depth > 0 || k != LBrace;
                braced |= depth == 0 && k == LBrace;
                depth += 1;
            }
            RParen | RBracket | RBrace if depth == 0 => {
                let around = c.brackets().around(from);
                (!closer || around.and_then(|o| closing(c, o)) == Some(i)).then_some(())?;
                break;
            }
            RParen | RBracket | RBrace => (depth, expect) = (depth - 1, expect && depth > 1),
            _ if depth > 0 || (k == Newline && i < s) || (head && (k != Newline || c.lines.goes_on(i))) => {}
            Newline if head => return None,
            KwIf if !expect && in_pattern(c) => break,
            KwIf | KwMatch | KwFn | KwUnsafe | KwHandle | KwPar => head = expect.then_some(true)?,
            KwElse if !expect => head = true,
            KwAs | KwAt if !expect => {
                operands.iter_mut().last().into_iter().for_each(|o| *o = Operand::AsAt);
                expect = true;
            }
            _ if k.binop().is_some() && !expect => {
                ops.extend(k.binop());
                operands.push(Operand::Plain);
                expect = true;
            }
            _ if in_chain(c, i) => expect = alternation(c, i, expect)?,
            DotDotLt | DotDotEq if !ranges => return None,
            _ if ends_chain(k, false) => break,
            _ => return None,
        }
        i += 1;
    }
    Some((operands, ops, braced)).filter(|_| i > s && !expect && !head)
}

/// Whether an operand is wanted after the token `i` of a chain ([`in_chain`]),
/// `expect` whether one was before it (§3.1): a prefix `-`, `!` or `^` against
/// one wants it, an operand or `?` none, another operator, `as`, `at`, `.`,
/// `::`, `~`, `!` or `with` the next. None where they do not alternate.
fn alternation(c: &Cursor, i: usize, expect: bool) -> Option<bool> {
    use TokenKind::*;
    let prefix = |k| matches!(k, Minus | Bang | Caret);
    match c.kind(i) {
        _ if c.comment(i) || c.kind(i) == Newline => Some(expect),
        k if prefix(k) && expect => (c.gap_after(i) == Gap::None && !prefix(c.kind(i + 1))).then_some(true),
        Question => (!expect).then_some(false),
        k if ends_operand(k) || k == Underscore => expect.then_some(false),
        _ => (!expect).then_some(true),
    }
}

/// Whether the token `i` goes on a chain at its depth (§3.1): a comment, a
/// line break that goes on with its line, an operator, `as` and `at`, and
/// what ends an operand or goes on with one (`_`, `.`, `::`, `~`, `!`, the
/// `with` of a `handle`).
fn in_chain(c: &Cursor, i: usize) -> bool {
    use TokenKind::*;
    let k = c.kind(i);
    c.comment(i)
        || (k == Newline && c.lines.goes_on(i))
        || k.binop().is_some()
        || ends_operand(k)
        || matches!(k, KwAs | KwAt | KwWith | Underscore | Dot | ColonColon | Tilde | Bang)
}

/// Whether a token of `kind` ends a chain at its depth, going back (`back`)
/// or on (§3.1): a line break, a `,`, the `;` of the repetition of an array,
/// a `=>`, the `if` of a guard and the marks of a range (they are weaker than
/// every binary operator, §7); going back, what an expression follows too: a
/// `=`, the `:` of a field, and the keywords `return`, `assert`, `break`,
/// `while` and `in`.
fn ends_chain(kind: TokenKind, back: bool) -> bool {
    use TokenKind::*;
    matches!(kind, Newline | Comma | Semi | FatArrow | KwIf | DotDotLt | DotDotEq)
        || (back && matches!(kind, Eq | Colon | KwReturn | KwAssert | KwBreak | KwWhile | KwIn))
}

/// Whether the token at `i` follows an operand on its line: an operator there
/// is binary, else a prefix one (a `-`, `!` or `^` at the head of a line, or
/// after another operator).
pub(super) fn after_operand(c: &Cursor, i: usize) -> bool {
    c.before(i).is_some_and(|p| ends_operand(c.kind(p)))
}

/// Whether the failure is at a symbol at the head of a line that goes on with
/// the line before ([`leading_symbol`]): the symbol and the code before it,
/// by the kind of the symbol ([`leading_arrow`], [`leading_eq`],
/// [`leading_binary`]). Not in a pattern (the rows of the patterns judge it),
/// nor a symbol that starts the next arm of a `match` (S-386, the missing
/// `,`), nor one that another touches (`+=`, `===`, `&*x`): what is left
/// would be wrong (S-236). A `&` or a `+` at the head of a line that this
/// finds is read as the binary one (W3-06, S-405): the reference's and the
/// prefix `+`'s rows ask it ([`super::modes::reference`], [`prefix_plus`]).
pub(super) fn leading(c: &Cursor) -> Option<(usize, usize)> {
    use TokenKind::*;
    let kind = c.kind(c.symbol_ahead());
    if !(matches!(kind, Arrow | Eq) || kind.binop().is_some()) {
        return None;
    }
    let (s, prev) = c.head_symbol_after_operand()?;
    let touching = c.gap_after(s) == Gap::None && !crate::starts::starts_operand(c.kind(s + 1));
    if c.want == Want::Pattern || starts_an_arm(c, s) || touching {
        return None;
    }
    let fits = match kind {
        Arrow => leading_arrow(c),
        Eq => leading_eq(c, prev),
        _ => leading_binary(c, s),
    };
    fits.then_some((s, prev))
}

/// A `->` at the head of a line: the result of a head, with a body or
/// without (a member of a trait, an effect or an `extern`, a `target fn`;
/// S-374).
fn leading_arrow(c: &Cursor) -> bool {
    c.closed.iter().any(|n| matches!(n.0, NodeKind::ParamList | NodeKind::FnTypeParams))
}

/// A `=` at the head of a line (S-374): of a binding or a definition waiting
/// for it, after a statement after which it goes on to an assignment (not
/// one that has its `=` already: `x = 2` and `= 3` on the next line), the
/// value of a constant of a trait, or the default of a field that has none.
fn leading_eq(c: &Cursor, prev: usize) -> bool {
    if c.kind(c.at) == TokenKind::Newline {
        return matches!(
            c.context(),
            Some((_, NodeKind::LetStmt | NodeKind::VarStmt | NodeKind::Const | NodeKind::TypeAlias))
        );
    }
    (c.want == Want::Expr && c.closed.is_empty() && c.end_at(prev).is_none())
        || (c.closed.iter().any(|n| n.0 == NodeKind::Const) && closed_expr(c).is_none())
        || (c.want == Want::Separator(NodeKind::FieldList) && closed_expr(c).is_none())
}

/// A binary operator at the head of a line (S-124, S-370), or the `|` of a
/// pattern choice (S-380): after an operand that closed there, or at the
/// start of a statement after one (the line break read, nothing closed
/// since). A `- b` and a `^ b` where an expression goes are the prefix rows',
/// a `||` in a pattern is `pattern_double_vert`'s (S-389), and `&mut` is the
/// reference's ([`Cursor::ref_mut`]).
fn leading_binary(c: &Cursor, s: usize) -> bool {
    use TokenKind::*;
    let kind = c.kind(s);
    if matches!(kind, Minus | Caret) && matches!(c.want, Want::Prefix | Want::Expr) {
        return false;
    }
    if (kind == OrOr && in_pattern(c)) || (kind == Amp && c.ref_mut(s)) {
        return false;
    }
    if kind == Pipe && in_pattern(c) {
        return true;
    }
    goes_on_after_operand(c)
}

/// Whether the symbol `s` at the head of a line starts the next arm of a
/// `match` (S-386): it goes on with no line before.
pub(super) fn starts_an_arm(c: &Cursor, s: usize) -> bool {
    c.want == Want::Separator(NodeKind::MatchArms) && arm_ahead(c.tokens, c.brackets(), s)
}

/// Whether the head of the line of the failure, after an operand, goes on
/// with the expression of the line before (§2.5): one closed there, or a
/// statement that starts after one (the line break read, nothing closed
/// since). Not after a type or a name of a declaration (a field, a variant).
pub(super) fn goes_on_after_operand(c: &Cursor) -> bool {
    closed_expr(c).is_some() || (c.kind(c.at) != TokenKind::Newline && c.closed.is_empty())
}

/// A `|` where a pattern starts (`| 0 | 1 =>`, `Some(| 0)`, `let | (a, b) = p`;
/// §7, S-383): the `|` goes between the alternatives only, and the
/// candidate takes it out with the blanks after it. When no pattern follows
/// (`| =>`), or what follows reads as more than a pattern (`| x > 0 =>`, an
/// operator in it), there is none (E0002).
pub(super) fn leading_vert(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Pattern || c.kind(c.at) != TokenKind::Pipe {
        return None;
    }
    let next = c.sig_after(c.at);
    let starts = c.kind(next) == TokenKind::Pipe || crate::starts::starts_element(NodeKind::TuplePat, c.kind(next));
    // To an opener no closer closes: no operator after it is at the depth
    // of the pattern (R-410, [`crate::scan::Brackets::scan_end`]).
    let end = c.brackets().scan_end(next);
    let kinds = c.tokens[next..end].iter().map(|t| t.kind).filter(|k| !k.is_trivia());
    let (n, _) = crate::scan::pattern_alternative(kinds.clone());
    let mut depth = 0u32;
    let operator = kinds.take(n).enumerate().any(|(k, kind)| {
        match kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth = depth.saturating_sub(1),
            _ => {}
        }
        depth == 0 && kind.binop().is_some() && !(k == 0 && kind == TokenKind::Minus)
    });
    if !starts || operator {
        return None;
    }
    let s = c.span(c.at);
    let end = c.space_after(c.at).map_or(s.end, |w| w.end);
    hit(s, vec![Fix::delete("take the `|` out", Span::new(c.file, s.start, end))])
}

/// A `||` in a pattern (`0 || 1 =>`, `|| 0 =>`, `Some(0 || 1)`; §7, S-389):
/// a pattern choice is one `|`, and the candidate writes it. Only when a
/// pattern follows that is no `|` (`0 ||| 1` would read `||` again).
pub(super) fn pattern_double_vert(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::OrOr || !in_pattern(c) {
        return None;
    }
    let next = c.kind(c.sig_after(c.at));
    if next == TokenKind::Pipe || !crate::starts::starts_element(NodeKind::TuplePat, next) {
        return None;
    }
    hit(c.span(c.at), vec![Fix::replace("write one `|`", c.span(c.at), "|")])
}

/// A prefix `+` (`let a = +1`, `[1, +1]`, `two(+x, 1)`, `+1 =>`, an argument of
/// an attribute; §3.1, S-405): Onsa has no prefix `+`, and the candidate
/// takes it out with the blanks after it. After a line break (`let y = +`
/// and `a` on the next line, S-425) the operand's line comes up to its place,
/// before the comment of the `+`'s line (S-216). A `+` at the head of a line
/// after an operand is read as the binary one, `leading_operator`'s
/// ([`leading`], S-405): no form of its own. The order of the diagnostics
/// would choose the same (S-281), by the order of the two messages (`a
/// line …` before `there …`: to be checked again when either changes), but
/// the reading is decided, and a second diagnostic that is never reported
/// costs its candidates at every such line (W3-06's long inputs). In a
/// pattern only before an integer.
pub(super) fn prefix_plus(c: &Cursor) -> Option<Hit> {
    if !prefix_plus_at(c) {
        return None;
    }
    let next = c.sig_after(c.at);
    let fits = if c.want == Want::Pattern {
        c.kind(next) == TokenKind::Int
    } else {
        crate::starts::starts_operand(c.kind(next))
    };
    if !fits {
        return None;
    }
    let s = c.span(c.at);
    let title = "take the `+` out";
    let fix = match c.gap_after(c.at) {
        Gap::Newline => {
            let up = move_up(c.file, c.text, c.all, title, s.end, c.tokens[next], "")?;
            let mut edits = vec![Edit::delete(s)];
            edits.extend(up.edits().iter().cloned());
            Fix::new(title, edits)
        }
        _ => Fix::delete(title, Span::new(c.file, s.start, c.space_after(c.at).map_or(s.end, |w| w.end))),
    };
    hit(s, vec![fix])
}

/// Whether the cursor is at a prefix `+` ([`prefix_plus`]): where an operand
/// or a pattern starts, and no binary one at the head of a line ([`leading`]).
pub(super) fn prefix_plus_at(c: &Cursor) -> bool {
    c.kind(c.at) == TokenKind::Plus && matches!(c.want, Want::Expr | Want::Pattern) && leading(c).is_none()
}
