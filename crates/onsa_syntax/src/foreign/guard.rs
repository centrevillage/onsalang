//! The guard forms of the patterns (spec §7, §18.1): the forms a guard
//! writes (a float literal, a range, an interpolated string, a `-` before a
//! constant, an `@` binding), read from the tokens of an arm, and the one
//! candidate that writes them in a guard (S-317, S-319).
//!
//! The pattern of an arm is read from its tokens ([`PatReader`]) into a
//! tree whose holes are the forms; [`shape`] replaces each hole with a new
//! binding, an `@` binding with its name, and merges the alternatives of
//! one skeleton; the condition ([`Cond`]) is written with the parentheses
//! the groups of §3.1 need ([`BinOp::bare`]). The type stage (W5-09) is to
//! read its constants of other types through the same reader and shape.

use super::*;
use crate::ast::{BinOp, Operand, RangeEnd, Side};

/// The forms a guard writes, in the order of the rows that report them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Form {
    Float,
    Range,
    Str,
    Negated,
    At,
}

impl Form {
    /// The row of the form when a candidate is made (or when the form is
    /// not in an arm, or cannot be read: E0002 by S-48).
    fn row(self) -> RowId {
        match self {
            Form::Float => RowId::FloatPattern,
            Form::Range => RowId::RangePattern,
            Form::Str => RowId::InterpolatedStringPattern,
            Form::Negated => RowId::NegatedConstantPattern,
            Form::At => RowId::AtBinding,
        }
    }

    /// The row when the alternatives differ once the forms are replaced
    /// (S-317): those of the floats, the ranges and `@` have their own.
    fn choice_row(self) -> RowId {
        match self {
            Form::Float => RowId::FloatPatternChoice,
            Form::Range => RowId::RangePatternChoice,
            Form::At => RowId::AtBindingComplex,
            Form::Str | Form::Negated => self.row(),
        }
    }
}

/// What a hole of a pattern tests, once it is a name of the guard (S-317).
#[derive(Clone)]
enum Test {
    /// `name == <text>`: a float literal, an interpolated string, a `-`
    /// before a constant, and on the right of `@` a literal or a constant.
    Equal(String),
    /// `lo <= name && name < hi` (S-249, S-278): the ends as written, in
    /// parentheses when a comparison needs them (S-341); `end` is `None`
    /// for `..` and `...`, read both ways.
    Range { lo: Option<String>, hi: Option<String>, end: Option<RangeEnd> },
}

/// A pattern read from its tokens (`lo..=hi`, positions of the reader's
/// tokens), for the guard form: its holes, the forms the guard tests.
struct Pat {
    lo: usize,
    hi: usize,
    kind: PatKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Leaf {
    /// A literal (`1`, `-1`, `'a'`, `"a"`, `true`).
    Lit,
    /// A path whose last name is a constant's (`LIMIT`, `cfg.LIMIT`, §2.3).
    Const,
    /// A name, `_`, another path, the rest `..` of a struct pattern.
    Other,
}

enum PatKind {
    /// A form the guard tests.
    Hole(Form, Test),
    /// A form that makes no candidate (a range whose end is not an
    /// expression, a comment in it).
    Bad(Form),
    /// Tokens with nothing inside.
    Leaf(Leaf),
    /// Brackets around patterns (a tuple, `Some(..)`, `S { x: .. }`).
    Node(Vec<Pat>),
    /// `(p)`, a group (R-43): the same skeleton as `p`.
    Paren(Box<Pat>),
    /// Alternatives `p | q`.
    Or(Vec<Pat>),
    /// `name @ rhs` (`@` at `at`).
    At { at: usize, rhs: Box<Pat> },
}

/// A reader of the tokens `toks` (indexes of `tokens`, without newlines and
/// comments) of a pattern. It reads what `Parser::parse_pattern` reads, and
/// the guard forms; anything else makes no candidate. It reads patterns
/// nested `limit` deep at most (the parser counts the levels only up to its
/// failure, §2.5; the tree and the walks over it are as deep).
struct PatReader<'c, 'a> {
    c: &'c Cursor<'a>,
    toks: Vec<usize>,
    pos: usize,
    depth: u32,
    limit: u32,
}

impl<'c, 'a> PatReader<'c, 'a> {
    /// A reader of `toks`, significant tokens of `c` (indexes of `tokens`).
    fn new(c: &'c Cursor<'a>, toks: Vec<usize>, limit: u32) -> PatReader<'c, 'a> {
        PatReader { c, toks, pos: 0, depth: 0, limit }
    }

    fn peek(&self) -> Option<TokenKind> {
        self.toks.get(self.pos).map(|&i| self.c.kind(i))
    }

    fn bump(&mut self) -> usize {
        self.pos += 1;
        self.pos - 1
    }

    fn pat(&self, lo: usize, kind: PatKind) -> Pat {
        Pat { lo, hi: self.pos - 1, kind }
    }

    fn or(&mut self) -> Option<Pat> {
        let lo = self.pos;
        let one = self.one()?;
        if self.peek() != Some(TokenKind::Pipe) {
            return Some(one);
        }
        let mut alts = vec![one];
        while self.peek() == Some(TokenKind::Pipe) {
            self.bump();
            alts.push(self.one()?);
        }
        Some(self.pat(lo, PatKind::Or(alts)))
    }

    /// The patterns up to `close`, and whether a `,` follows the last one.
    fn list(&mut self, close: TokenKind, fields: bool) -> Option<(Vec<Pat>, bool)> {
        let mut out = Vec::new();
        let mut comma = false;
        while self.peek() != Some(close) {
            comma = false;
            if fields {
                // The rest `..` is another error (S-109): it stays.
                if self.peek().is_some_and(TokenKind::is_foreign_range) {
                    let lo = self.bump();
                    out.push(self.pat(lo, PatKind::Leaf(Leaf::Other)));
                } else {
                    if self.peek() != Some(TokenKind::Ident) {
                        return None;
                    }
                    self.bump();
                    if self.peek() != Some(TokenKind::Colon) {
                        return None;
                    }
                    self.bump();
                    out.push(self.or()?);
                }
            } else {
                out.push(self.or()?);
            }
            if self.peek() != Some(TokenKind::Comma) {
                break;
            }
            self.bump();
            comma = true;
        }
        (self.peek() == Some(close)).then(|| {
            self.bump();
            (out, comma)
        })
    }

    /// The text of the reader's tokens `a..=b`.
    fn text(&self, a: usize, b: usize) -> String {
        let c = self.c;
        c.text[c.span(self.toks[a]).start as usize..c.span(self.toks[b]).end as usize].to_string()
    }

    /// A comment between the reader's tokens `a` and `b` (S-251: an edit
    /// over them would remove it).
    fn comment_in(&self, a: usize, b: usize) -> bool {
        (self.toks[a]..=self.toks[b]).any(|i| self.c.comment(i))
    }

    /// A path at the reader (`a`, `a.B`, `Self.X`): whether its last name is
    /// a constant's.
    fn path(&mut self) -> Option<bool> {
        self.bump();
        while self.peek() == Some(TokenKind::Dot) {
            self.bump();
            if !self.peek().is_some_and(is_segment) {
                return None;
            }
            self.bump();
        }
        Some(crate::naming::is_constant_name(self.c.src(self.toks[self.pos - 1])))
    }

    /// The literal or the constant after a `-`, `(`s and as many `)`s.
    fn negative(&mut self, lo: usize) -> Option<Pat> {
        let minus = self.peek() == Some(TokenKind::Minus);
        if minus {
            self.bump();
        }
        let mut opens = 0;
        while minus && self.peek() == Some(TokenKind::LParen) {
            self.bump();
            opens += 1;
        }
        // The number: a float (`1.5`), one written as in other languages
        // (`1.`, `0.5f32`, `.5`: the guard writes it in the Onsa spelling).
        let at = self.pos;
        let mut constant = false;
        let float = match self.peek()? {
            TokenKind::Int => None,
            TokenKind::Float => Some(self.c.src(self.toks[at]).to_string()),
            TokenKind::ForeignLit => Some(float_spelling(self.c.src(self.toks[at]))?),
            // `.5`: the point and the digits together, as the lexer reads `0.5`.
            TokenKind::Dot
                if self.toks.get(at + 1).is_some_and(|&n| {
                    n == self.toks[at] + 1 && self.c.kind(n) == TokenKind::Int && !self.c.gap(n).is_some()
                }) =>
            {
                self.bump();
                Some(format!("0.{}", self.c.src(self.toks[at + 1])))
            }
            // `-LIMIT`, `-(LIMIT)`, `-I64.MAX` (S-319): the name is a constant's.
            TokenKind::Ident | TokenKind::KwSelfType if minus => {
                if !self.path()? {
                    return None;
                }
                self.pos -= 1;
                constant = true;
                None
            }
            _ => return None,
        };
        self.bump();
        for _ in 0..opens {
            if self.peek() != Some(TokenKind::RParen) {
                return None;
            }
            self.bump();
        }
        let kind = match float {
            Some(value) => {
                let close = ")".repeat(opens);
                let open = "(".repeat(opens);
                let sign = if minus { "-" } else { "" };
                PatKind::Hole(Form::Float, Test::Equal(format!("{sign}{open}{value}{close}")))
            }
            None if constant => PatKind::Hole(Form::Negated, Test::Equal(self.text(lo, self.pos - 1))),
            None => PatKind::Leaf(Leaf::Lit),
        };
        Some(self.pat(lo, kind))
    }

    /// The end `a..=b` of a range (reader's tokens), as the guard writes it:
    /// in parentheses when it is no bare operand of a comparison (S-341).
    /// `None` when it is not one expression, or holds a comment.
    fn end_text(&self, a: usize, b: usize, side: Side) -> Option<String> {
        if self.comment_in(a, b) {
            return None;
        }
        let c = self.c;
        let (first, last) = (c.full[self.toks[a]] as usize, c.full[self.toks[b]] as usize);
        if !crate::parser::reads_as_expr(c.file, c.text, c.all, c.holes, first, last) {
            return None;
        }
        let text = self.text(a, b);
        let top = operand(&(self.toks[a]..=self.toks[b]).map(|i| c.kind(i)).collect::<Vec<_>>());
        Some(if BinOp::Le.bare(side, top) { text } else { format!("({text})") })
    }

    /// A range from `lo`, with its symbol at `sym` and its end before `end`.
    fn range(&mut self, lo: usize, sym: usize, end: usize) -> Option<Pat> {
        if lo == sym && sym + 1 == end {
            // `..` alone (the rest of a tuple of Rust): no form.
            return None;
        }
        let symbol = self.c.kind(self.toks[sym]);
        self.pos = end;
        let start = if lo < sym { self.end_text(lo, sym - 1, Side::Left).map(Some) } else { Some(None) };
        let stop = if sym + 1 < end { self.end_text(sym + 1, end - 1, Side::Right).map(Some) } else { Some(None) };
        let end_of = symbol.range_end();
        let kind = match (start, stop) {
            // `5..<` has no end to compare with.
            (Some(_), Some(None)) if end_of.is_some() => PatKind::Bad(Form::Range),
            (Some(lo), Some(hi)) => PatKind::Hole(Form::Range, Test::Range { lo, hi, end: end_of }),
            _ => PatKind::Bad(Form::Range),
        };
        Some(self.pat(lo, kind))
    }

    fn one(&mut self) -> Option<Pat> {
        if self.depth >= self.limit {
            return None;
        }
        self.depth += 1;
        let p = self.one_at_depth();
        self.depth -= 1;
        p
    }

    fn one_at_depth(&mut self) -> Option<Pat> {
        let lo = self.pos;
        // The alternative as the parser reads it: newlines are seen, comments not.
        let first = *self.toks.get(self.pos)?;
        let rest = self.c.tokens[first..].iter().map(|t| t.kind).filter(|k| !k.is_trivia() || *k == TokenKind::Newline);
        if let (end, Some(sym)) = crate::parser::pattern_alternative(rest) {
            return self.range(lo, lo + sym, lo + end);
        }
        match self.peek()? {
            TokenKind::Minus | TokenKind::Int | TokenKind::Float | TokenKind::ForeignLit | TokenKind::Dot => {
                self.negative(lo)
            }
            TokenKind::Str => {
                let at = self.bump();
                let t = self.c.tokens[self.toks[at]];
                let kind = match interpolated(self.c.file, self.c.text, self.c.holes, t) {
                    true => PatKind::Hole(Form::Str, Test::Equal(self.text(lo, lo))),
                    false => PatKind::Leaf(Leaf::Lit),
                };
                Some(self.pat(lo, kind))
            }
            TokenKind::Char | TokenKind::KwTrue | TokenKind::KwFalse => {
                self.bump();
                Some(self.pat(lo, PatKind::Leaf(Leaf::Lit)))
            }
            TokenKind::Underscore => {
                self.bump();
                Some(self.pat(lo, PatKind::Leaf(Leaf::Other)))
            }
            TokenKind::LParen => {
                self.bump();
                let (mut inner, comma) = self.list(TokenKind::RParen, false)?;
                let kind = match inner.len() {
                    1 if !comma => PatKind::Paren(Box::new(inner.remove(0))),
                    _ => PatKind::Node(inner),
                };
                Some(self.pat(lo, kind))
            }
            TokenKind::Ident | TokenKind::KwSelfType => {
                let constant = self.path()?;
                let last = self.c.src(self.toks[self.pos - 1]);
                match self.peek() {
                    // As the parser: `(` touching the path, `{` after an UpperCamel name.
                    Some(TokenKind::LParen) if !self.c.gap(self.toks[self.pos]).is_some() => {
                        self.bump();
                        let (inner, _) = self.list(TokenKind::RParen, false)?;
                        Some(self.pat(lo, PatKind::Node(inner)))
                    }
                    Some(TokenKind::LBrace) if crate::naming::is_type_name(last) => {
                        self.bump();
                        let (inner, _) = self.list(TokenKind::RBrace, true)?;
                        Some(self.pat(lo, PatKind::Node(inner)))
                    }
                    // `n @ p`: the left side is a binding (§7).
                    Some(TokenKind::At) => {
                        let binding = self.pos == lo + 1 && crate::naming::is_binding_name(last);
                        if !binding {
                            return None;
                        }
                        let at = self.bump();
                        // A right side that is no pattern (`a @ ..`) is still the form of `@`.
                        let rhs = self.one().unwrap_or(Pat { lo: at, hi: at, kind: PatKind::Bad(Form::At) });
                        Some(self.pat(lo, PatKind::At { at, rhs: Box::new(rhs) }))
                    }
                    _ => Some(self.pat(lo, PatKind::Leaf(if constant { Leaf::Const } else { Leaf::Other }))),
                }
            }
            _ => None,
        }
    }
}

/// Whether the string literal `t` interpolates (§2.4, §7, S-225): it has a
/// hole, and the lexer finds no error in it (a hole of another form,
/// `{}`, `{a + b}`, is the lexer's E0001, which a guard that copies the
/// literal would keep).
pub(crate) fn interpolated(file: FileId, text: &str, holes: &[Span], t: Token) -> bool {
    let first = holes.partition_point(|h| h.start < t.span.start);
    let has = holes.get(first).is_some_and(|h| h.end <= t.span.end);
    has && crate::lex(file, &text[t.span.start as usize..t.span.end as usize]).diagnostics.is_empty()
}

/// The top of the expression of `kinds` (its tokens, comments and all) as
/// an operand ([`Operand`]): read by the brackets and the operators outside
/// them (a `-` or a `!` where an operand starts is a prefix). A chain whose
/// operators have no weakest group (an error E0010 of its own) is taken as
/// needing parentheses.
fn operand(kinds: &[TokenKind]) -> Operand {
    let mut depth = 0u32;
    let mut expect = true;
    let mut ops: Vec<BinOp> = Vec::new();
    let mut cast = false;
    for &k in kinds.iter().filter(|k| !k.is_trivia()) {
        match k {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1);
                expect = false;
            }
            _ if depth > 0 => {}
            TokenKind::Minus | TokenKind::Bang if expect => {}
            TokenKind::KwAs => {
                cast = true;
                expect = true;
            }
            _ => match crate::lower::binop(k) {
                Some(op) => {
                    ops.push(op);
                    expect = true;
                }
                None => expect = false,
            },
        }
    }
    let weakest = |r: &&BinOp| ops.iter().all(|o| o.group() == r.group() || o.group().stronger(r.group()));
    match ops.iter().rev().find(weakest) {
        Some(&root) => Operand::Binary(root),
        None if !ops.is_empty() || cast => Operand::AsAt,
        None => Operand::Plain,
    }
}

/// What a condition compares: a new binding (a hole, by its index) or the
/// name of an `@` binding.
#[derive(Clone)]
enum Subject {
    Hole(usize),
    Name(String),
}

/// The condition of a guard over the holes of a shape.
#[derive(Clone)]
enum Cond {
    True,
    Test(Subject, Test),
    And(Vec<Cond>),
    Or(Vec<Cond>),
}

impl Cond {
    fn shifted(self, by: usize) -> Cond {
        match self {
            Cond::True => Cond::True,
            Cond::Test(Subject::Hole(i), t) => Cond::Test(Subject::Hole(i + by), t),
            Cond::Test(s, t) => Cond::Test(s, t),
            Cond::And(v) => Cond::And(v.into_iter().map(|c| c.shifted(by)).collect()),
            Cond::Or(v) => Cond::Or(v.into_iter().map(|c| c.shifted(by)).collect()),
        }
    }

    /// Whether a range of the condition is read both ways (`..`, `...`).
    fn two_readings(&self) -> bool {
        match self {
            Cond::Test(_, Test::Range { hi: Some(_), end: None, .. }) => true,
            Cond::And(v) | Cond::Or(v) => v.iter().any(Cond::two_readings),
            _ => false,
        }
    }

    /// The text and its top as an operand: the comparisons bare, the `&&`
    /// and `||` chains flat (S-339), a chain in the other one in
    /// parentheses (§3.1, [`BinOp::bare`]). `reading` is the end of the
    /// ranges written `..` and `...`.
    fn render(&self, names: &[String], reading: RangeEnd) -> (String, Operand) {
        let subject = |s: &Subject| match s {
            Subject::Hole(i) => names[*i].clone(),
            Subject::Name(n) => n.clone(),
        };
        match self {
            Cond::True => ("true".into(), Operand::Plain),
            Cond::Test(s, Test::Equal(text)) => (format!("{} == {text}", subject(s)), Operand::Binary(BinOp::Eq)),
            Cond::Test(s, Test::Range { lo, hi, end }) => {
                let s = subject(s);
                let mut parts = Vec::new();
                if let Some(lo) = lo {
                    parts.push(format!("{lo} <= {s}"));
                }
                if let Some(hi) = hi {
                    parts.push(format!("{s} {} {hi}", end.unwrap_or(reading).cmp()));
                }
                let top = if parts.len() == 1 { BinOp::Le } else { BinOp::And };
                (parts.join(" && "), Operand::Binary(top))
            }
            Cond::And(v) => chain(v, names, reading, BinOp::And),
            Cond::Or(v) => chain(v, names, reading, BinOp::Or),
        }
    }
}

/// The items of an `&&` or `||` chain, flat: `&&` and `||` are associative,
/// so every item is read as the left operand of the next one.
fn chain(items: &[Cond], names: &[String], reading: RangeEnd, op: BinOp) -> (String, Operand) {
    let parts: Vec<(String, Operand)> =
        items.iter().filter(|c| !matches!(c, Cond::True)).map(|c| c.render(names, reading)).collect();
    if parts.len() == 1 {
        return parts.into_iter().next().unwrap_or(("true".into(), Operand::Plain));
    }
    let text = parts
        .into_iter()
        .map(|(t, top)| if op.bare(Side::Left, top) { t } else { format!("({t})") })
        .collect::<Vec<_>>()
        .join(if op == BinOp::And { " && " } else { " || " });
    (text, Operand::Binary(op))
}

/// One token of a skeleton: a token, or a hole.
#[derive(PartialEq)]
enum Skel<'a> {
    Tok(TokenKind, &'a str),
    Hole,
}

/// A pattern as the guard form keeps it: its skeleton, its holes (the first
/// and last token of each, in the order of the text), the condition on them,
/// and the edits that merge alternatives and remove the right of `@`.
struct Shape<'a> {
    skel: Vec<Skel<'a>>,
    holes: Vec<(usize, usize)>,
    cond: Cond,
    edits: Vec<Edit>,
}

/// Why a pattern has no candidate.
enum Why {
    /// The alternatives differ once the forms are replaced, or a comment
    /// lies in what the candidate removes (S-317, S-251).
    Differ,
    /// A form makes none (a range whose end is no expression, the right of
    /// `@` that is no literal, constant or range).
    Bad(Form),
}

/// The shape of `p` (S-317): the alternatives of a pattern with holes are
/// one when they have the same skeleton (the tokens but the holes, a group
/// `(p)` as `p`); the first stays, the others are removed, and the condition
/// is the `||` of theirs.
fn shape<'a>(c: &'a Cursor<'_>, toks: &[usize], p: &Pat) -> Result<Shape<'a>, Why> {
    let tok = |pos: usize| Skel::Tok(c.kind(toks[pos]), c.src(toks[pos]));
    let comment = |a: usize, b: usize| (toks[a]..=toks[b]).any(|i| c.comment(i));
    let empty = || Shape { skel: Vec::new(), holes: Vec::new(), cond: Cond::True, edits: Vec::new() };
    match &p.kind {
        PatKind::Hole(_, t) => {
            if comment(p.lo, p.hi) {
                return Err(Why::Differ);
            }
            Ok(Shape {
                skel: vec![Skel::Hole],
                holes: vec![(toks[p.lo], toks[p.hi])],
                cond: Cond::Test(Subject::Hole(0), t.clone()),
                edits: Vec::new(),
            })
        }
        PatKind::Bad(f) => Err(Why::Bad(*f)),
        PatKind::Leaf(_) => Ok(Shape { skel: (p.lo..=p.hi).map(tok).collect(), ..empty() }),
        PatKind::Paren(inner) => shape(c, toks, inner),
        PatKind::At { rhs, .. } => {
            let name = c.src(toks[p.lo]);
            let cond = at_cond(c, toks, name, rhs).ok_or(Why::Bad(Form::At))?;
            if comment(p.lo, p.hi) {
                return Err(Why::Differ);
            }
            // ` @ rhs` goes: the name stays the binding.
            let removed = c.file_span(c.span(toks[p.lo]).end, c.span(toks[p.hi]).end);
            Ok(Shape { skel: vec![tok(p.lo)], cond, edits: vec![Edit::delete(removed)], ..empty() })
        }
        PatKind::Node(inner) => {
            let mut out = empty();
            let mut conds = Vec::new();
            let mut pos = p.lo;
            for q in inner {
                out.skel.extend((pos..q.lo).map(tok));
                let s = shape(c, toks, q)?;
                out.skel.extend(s.skel);
                if !matches!(s.cond, Cond::True) {
                    conds.push(s.cond.shifted(out.holes.len()));
                }
                out.holes.extend(s.holes);
                out.edits.extend(s.edits);
                pos = q.hi + 1;
            }
            out.skel.extend((pos..=p.hi).map(tok));
            out.cond = match conds.len() {
                0 => Cond::True,
                1 => conds.remove(0),
                _ => Cond::And(conds),
            };
            Ok(out)
        }
        PatKind::Or(alts) => {
            let shapes = alts.iter().map(|a| shape(c, toks, a)).collect::<Result<Vec<_>, _>>()?;
            if shapes.iter().all(|s| s.holes.is_empty() && matches!(s.cond, Cond::True)) {
                // No form: the alternatives stay as written.
                return Ok(Shape { skel: (p.lo..=p.hi).map(tok).collect(), ..empty() });
            }
            if shapes.iter().any(|s| s.skel != shapes[0].skel) {
                return Err(Why::Differ);
            }
            // Remove ` | A_2 | ...`, which must hold no comment.
            let (from, to) = (toks[alts[0].hi], toks[p.hi]);
            if (from..=to).any(|i| c.comment(i)) {
                return Err(Why::Differ);
            }
            let mut shapes = shapes.into_iter();
            let Some(mut out) = shapes.next() else { return Err(Why::Differ) };
            let conds = std::iter::once(out.cond).chain(shapes.map(|s| s.cond)).collect();
            out.cond = Cond::Or(conds);
            out.edits.push(Edit::delete(c.file_span(c.span(from).end, c.span(to).end)));
            Ok(out)
        }
    }
}

/// The condition of `name @ rhs` (S-186, S-319, S-352): the whole right
/// side on the name. `None` when it is not literals, constants, ranges and
/// the choices of them.
fn at_cond(c: &Cursor, toks: &[usize], name: &str, rhs: &Pat) -> Option<Cond> {
    let subject = || Subject::Name(name.to_string());
    match &rhs.kind {
        PatKind::Hole(_, t) => Some(Cond::Test(subject(), t.clone())),
        PatKind::Leaf(Leaf::Lit | Leaf::Const) => {
            let text = c.text[c.span(toks[rhs.lo]).start as usize..c.span(toks[rhs.hi]).end as usize].to_string();
            Some(Cond::Test(subject(), Test::Equal(text)))
        }
        PatKind::Paren(inner) => at_cond(c, toks, name, inner),
        PatKind::Or(alts) => alts.iter().map(|a| at_cond(c, toks, name, a)).collect::<Option<_>>().map(Cond::Or),
        _ => None,
    }
}

/// The forms of `p` in the order of the text: the form and its first and
/// last reader's token (an `@` binding from its `@`, S-316).
fn forms(p: &Pat, out: &mut Vec<(Form, usize, usize)>) {
    match &p.kind {
        PatKind::Hole(f, _) | PatKind::Bad(f) => out.push((*f, p.lo, p.hi)),
        PatKind::Leaf(_) => {}
        PatKind::Paren(inner) => forms(inner, out),
        PatKind::Node(v) | PatKind::Or(v) => v.iter().for_each(|q| forms(q, out)),
        PatKind::At { at, .. } => out.push((Form::At, *at, p.hi)),
    }
}

/// The form of a pattern that starts at the failing token, and its first
/// and last token (indexes of `tokens`): read by the reader of the arms
/// (one reading of the forms, D-15), from the name before an `@`.
fn form_at(c: &Cursor) -> Option<(Form, usize, usize)> {
    let start = if c.kind(c.at) == TokenKind::At { c.sig_before(c.at)? } else { c.at };
    let toks = (start..c.tokens.len()).filter(|&i| !c.kind(i).is_trivia()).collect();
    let mut reader = PatReader::new(c, toks, crate::parser::NESTING_LIMIT);
    let p = reader.one()?;
    let mut found = Vec::new();
    forms(&p, &mut found);
    let &(form, a, b) = found.first()?;
    (reader.toks[a] == c.at).then(|| (form, reader.toks[a], reader.toks[b]))
}

/// A guard form in a pattern (§7, §18.1; S-109, S-186, S-225, S-249, S-278,
/// S-317, S-319, S-341, S-352): E0020 in the syntax stage. In an arm of
/// `match`, the candidate is the guard form, for all the forms of the arm's
/// pattern at once (one form, S-248): each becomes a name no other name of
/// the file has (S-253) and an `@` binding its name, and the guard compares
/// them; alternatives are merged when they have the same skeleton
/// ([`shape`]). Elsewhere (`let`, `for`), when the alternatives differ or a
/// form makes no candidate, E0002 with the note (S-48). The row is the one
/// of the first form of the pattern, and the main span runs from the first
/// form to the last (S-316).
pub(super) fn guard_pattern(c: &Cursor) -> Option<Hit> {
    if c.want != Want::Pattern {
        return None;
    }
    let (form, first, last) = form_at(c)?;
    let alone = c.file_span(c.span(first).start, c.span(last).end);
    // The pattern's owner: the innermost `match` arm, `let` or `for`.
    let owner = c.open.iter().rev().find(|o| matches!(o.0, NodeKind::MatchArm | NodeKind::LetStmt | NodeKind::ForStmt));
    let Some(&(NodeKind::MatchArm, arm_start)) = owner else {
        c.say(form.row());
        return hit(alone, Vec::new());
    };
    let Some(arm) = Arm::read(c, arm_start, crate::parser::NESTING_LIMIT) else {
        c.say(form.row());
        return hit(alone, Vec::new());
    };
    let mut found = Vec::new();
    forms(&arm.pat, &mut found);
    let (Some(&(head, a, _)), Some(&(_, _, b))) = (found.first(), found.last()) else {
        c.say(form.row());
        return hit(alone, Vec::new());
    };
    let span = c.file_span(c.span(arm.toks[a]).start, c.span(arm.toks[b]).end);
    match arm.candidates(c) {
        Ok(fixes) => {
            c.say(head.row());
            hit(span, fixes)
        }
        Err(Why::Differ) => {
            c.say(head.choice_row());
            hit(span, Vec::new())
        }
        Err(Why::Bad(bad)) => {
            c.say(if bad == Form::At { Form::At.choice_row() } else { head.row() });
            hit(span, Vec::new())
        }
    }
}

/// The `n`-th name (from 1) the guard-form candidates may bind: `v`, `v2`,
/// `v3`, ... (S-253). A candidate takes the first ones no identifier of the
/// file spells: a name visible at the arm is declared or imported in the
/// file, or is a name of the prelude, which has none of these
/// (`onsa_sema`'s test `the_prelude_has_no_name_of_the_guard_candidates`);
/// the names the merged pattern keeps, those in the ends of the ranges
/// (S-341) and those in the holes of the strings (S-319) are identifiers of
/// the file too.
pub fn guard_name(n: usize) -> String {
    if n <= 1 { "v".to_string() } else { format!("v{n}") }
}

/// The pattern of an arm, read: its tokens (indexes of `tokens`), its tree,
/// its own guard (`if` and `=>`) and its last token.
struct Arm {
    toks: Vec<usize>,
    pat: Pat,
    if_tok: Option<usize>,
    arrow: usize,
    last_pat: usize,
}

impl Arm {
    /// The arm that starts at `arm_start`: the pattern runs to `if` or `=>`
    /// outside brackets, the guard to `=>`; its patterns nest `limit` deep
    /// at most ([`PatReader`]).
    fn read(c: &Cursor, arm_start: u32, limit: u32) -> Option<Arm> {
        let first = c.index_at(arm_start);
        let mut depth = 0i32;
        let mut toks = Vec::new();
        let mut i = first;
        let (if_tok, arrow) = loop {
            match c.kind(i) {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::KwIf if depth == 0 => {
                    let mut j = i + 1;
                    while c.kind(j) != TokenKind::FatArrow {
                        if matches!(c.kind(j), TokenKind::Eof | TokenKind::RBrace) {
                            return None;
                        }
                        j += 1;
                    }
                    break (Some(i), j);
                }
                TokenKind::FatArrow if depth == 0 => break (None, i),
                TokenKind::Eof => return None,
                _ => {}
            }
            if depth < 0 {
                return None;
            }
            if !c.kind(i).is_trivia() {
                toks.push(i);
            }
            i += 1;
        };
        let last_pat = *toks.last()?;
        let mut reader = PatReader::new(c, toks, limit);
        let pat = reader.or()?;
        if reader.pos != reader.toks.len() {
            return None;
        }
        Some(Arm { toks: reader.toks, pat, if_tok, arrow, last_pat })
    }

    /// The candidates: one, or two when a range is written `..` or `...`
    /// (the end excluded, then included).
    fn candidates(&self, c: &Cursor) -> Result<Vec<Fix>, Why> {
        let shape = shape(c, &self.toks, &self.pat)?;
        if shape.holes.is_empty() && matches!(shape.cond, Cond::True) {
            return Err(Why::Differ);
        }
        // New names: none that the file has (S-253), the names in the holes
        // of the string literals too (S-319): a new name that a misspelt
        // `{v}` names would hide its E0302.
        let in_holes = c.holes.iter().flat_map(|h| {
            let inner = &c.text[h.start as usize..h.end as usize];
            inner.trim_start_matches('{').trim_end_matches('}').split('.')
        });
        let used: std::collections::HashSet<&str> = c
            .all
            .iter()
            .filter(|t| t.kind == TokenKind::Ident)
            .map(|t| &c.text[t.span.start as usize..t.span.end as usize])
            .chain(in_holes)
            .collect();
        let mut n = 0;
        let mut names = Vec::new();
        while names.len() < shape.holes.len() {
            n += 1;
            let name = guard_name(n);
            if !used.contains(name.as_str()) {
                names.push(name);
            }
        }
        let mut edits = shape.edits;
        for (&(a, b), name) in shape.holes.iter().zip(&names) {
            edits.push(Edit::replace(c.file_span(c.span(a).start, c.span(b).end), name.clone()));
        }
        // A pattern with several ranges written `..` or `...` reads them all
        // one way: two candidates (S-365).
        let readings: &[(RangeEnd, &str)] = if shape.cond.two_readings() {
            &[
                (RangeEnd::Excluded, "compare in a guard, without the end (`..<`)"),
                (RangeEnd::Included, "compare in a guard, with the end (`..=`)"),
            ]
        } else {
            &[(RangeEnd::Excluded, "compare in a guard")]
        };
        let mut fixes = Vec::new();
        for &(reading, title) in readings {
            let (cond, top) = shape.cond.render(&names, reading);
            let mut edits = edits.clone();
            match self.if_tok {
                None => edits.push(Edit::insert(c.file, c.span(self.last_pat).end, format!(" if {cond}"))),
                Some(t) => {
                    // The arm's own guard follows with `&&` (§7).
                    let g_first = c.sig_after(t);
                    let g_last = c.sig_before(self.arrow).ok_or(Why::Differ)?;
                    let g = operand(&(g_first..=g_last).map(|i| c.kind(i)).collect::<Vec<_>>());
                    let cond = if BinOp::And.bare(Side::Left, top) { cond } else { format!("({cond})") };
                    if BinOp::And.bare(Side::Left, g) {
                        edits.push(Edit::insert(c.file, c.span(g_first).start, format!("{cond} && ")));
                    } else {
                        edits.push(Edit::insert(c.file, c.span(g_first).start, format!("{cond} && (")));
                        edits.push(Edit::insert(c.file, c.span(g_last).end, ")"));
                    }
                }
            }
            fixes.push(Fix::new(title, edits));
        }
        Ok(fixes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whether the arm whose pattern starts at the first `(` of `src` is read
    /// with patterns nested `limit` deep at most.
    fn arm_reads(src: &str, limit: u32) -> bool {
        let lexed = crate::lex(FileId(0), src);
        let all = lexed.tokens;
        let full: Vec<u32> = (0..all.len() as u32).filter(|&i| all[i as usize].kind != TokenKind::Whitespace).collect();
        let tokens: Vec<Token> = full.iter().map(|&i| all[i as usize]).collect();
        let c = Cursor {
            file: FileId(0),
            text: src,
            tokens: &tokens,
            all: &all,
            full: &full,
            holes: &lexed.holes,
            at: 0,
            open: Vec::new(),
            closed: &[],
            want: Want::Pattern,
            found: std::cell::Cell::new(None),
        };
        let start = src.find("((").unwrap_or_default() as u32;
        Arm::read(&c, start, limit).is_some()
    }

    #[test]
    fn the_reader_stops_at_its_limit_of_nesting() {
        // Five levels: the four groups and the literal.
        let src = "fn f(x: F32) -> I32 {\n  match x {\n    ((((0.5)))) => 1,\n    _ => 0,\n  }\n}\n";
        assert!(arm_reads(src, 5));
        assert!(!arm_reads(src, 4));
    }
}
