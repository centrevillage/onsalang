//! The guard forms of the patterns (spec §7, §18.1): the forms a guard
//! writes (a float literal, a range, an interpolated string, a `-` before a
//! constant, an `@` binding), read from the tokens of an arm, and the one
//! candidate that writes them in a guard (S-317, S-319).
//!
//! The pattern of an arm is read from its tokens by the parser's grammar
//! ([`crate::parser::reads_as_pattern`], the forms as `Error` nodes), then
//! moved into a tree whose holes are the forms ([`Toks`]); [`shape`]
//! replaces each hole with a new
//! binding, an `@` binding with its name, and merges the alternatives of
//! one skeleton; the condition ([`Cond`]) is written with the parentheses
//! the groups of §3.1 need ([`BinOp::bare`]). The types stage reads its
//! constants of other types through the same reader and shape
//! ([`constants_in_guard`]).

use super::*;
use crate::ast::{BinOp, Operand, RangeEnd, Side};
use crate::cst::{Cst, NodeId};

/// The forms a guard writes, in the order of the rows that report them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Form {
    Float,
    Range,
    Str,
    Negated,
    At,
    /// A constant of a type no pattern compares (§7): only the types stage
    /// knows one ([`mark`]).
    Constant,
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
            Form::Constant => RowId::FloatConstantPattern,
        }
    }

    /// The row when the alternatives differ once the forms are replaced
    /// (S-317): those of the floats, the ranges and `@` have their own.
    fn choice_row(self) -> RowId {
        match self {
            Form::Float => RowId::FloatPatternChoice,
            Form::Range => RowId::RangePatternChoice,
            Form::At => RowId::AtBindingComplex,
            Form::Str | Form::Negated | Form::Constant => self.row(),
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

/// The tokens `toks` (indexes of `tokens`, without newlines and line
/// comments) of a pattern read by the parser
/// ([`crate::parser::reads_as_pattern`]), and the tree of that reading.
struct Toks<'c, 'a> {
    c: &'c Cursor<'a>,
    toks: Vec<usize>,
}

type Forms = [(u32, crate::parser::Guarded)];

impl<'c, 'a> Toks<'c, 'a> {
    /// The pattern of `toks` read from their first token: the whole of them
    /// when `whole`, else one alternative. The block comments of `c` are
    /// left out of the reading when `skip_blocks` (and out of `toks`).
    fn read(c: &'c Cursor<'a>, toks: Vec<usize>, whole: bool, skip_blocks: bool) -> Option<(Toks<'c, 'a>, Pat)> {
        let (first, last) = (c.full[*toks.first()?] as usize, c.full[*toks.last()?] as usize);
        let run = c.all[first..=last].iter().filter(|t| !(skip_blocks && t.kind == TokenKind::BlockComment));
        let (cst, forms) = crate::parser::reads_as_pattern(c.file, c.text, run.copied().collect(), c.literals, whole)?;
        let t = Toks { c, toks };
        let pat = cst.child_nodes(cst.root()).next()?;
        let p = t.pat(&cst, &forms, pat)?;
        Some((t, p))
    }

    /// The position in `toks` of the token that starts at `start`.
    fn pos(&self, start: u32) -> Option<usize> {
        self.toks.binary_search_by_key(&start, |&k| self.c.span(k).start).ok()
    }

    /// The patterns inside the node `n`: its child nodes but its path, a
    /// field of a struct pattern by its pattern.
    fn inner(&self, cst: &Cst, forms: &Forms, n: NodeId) -> Option<Vec<Pat>> {
        let mut out = Vec::new();
        for k in cst.child_nodes(n) {
            match cst.kind(k) {
                NodeKind::Path => {}
                NodeKind::StructPatField => out.push(self.pat(cst, forms, cst.child_nodes(k).last()?)?),
                _ => out.push(self.pat(cst, forms, k)?),
            }
        }
        Some(out)
    }

    /// The pattern of the node `n` of the reading.
    fn pat(&self, cst: &Cst, forms: &Forms, n: NodeId) -> Option<Pat> {
        use crate::parser::Guarded;
        let (a, b) = cst.significant_tokens(n)?;
        let (lo, hi) = (self.pos(cst.token(a).span.start)?, self.pos(cst.token(b).span.start)?);
        let kind = match cst.kind(n) {
            NodeKind::WildPat | NodeKind::BindPat | NodeKind::StructPatRest => PatKind::Leaf(Leaf::Other),
            NodeKind::LitPat | NodeKind::NegLitPat => PatKind::Leaf(Leaf::Lit),
            NodeKind::PathPat => {
                let constant = crate::naming::reads_constant(self.c.src(self.toks[hi]));
                PatKind::Leaf(if constant { Leaf::Const } else { Leaf::Other })
            }
            NodeKind::ParenPat => PatKind::Paren(Box::new(self.inner(cst, forms, n)?.pop()?)),
            NodeKind::TuplePat | NodeKind::TupleStructPat | NodeKind::StructPat => {
                PatKind::Node(self.inner(cst, forms, n)?)
            }
            NodeKind::OrPat => PatKind::Or(self.inner(cst, forms, n)?),
            NodeKind::Error => match forms.iter().find(|f| f.0 == cst.token(a).span.start)?.1 {
                Guarded::Str => PatKind::Hole(Form::Str, Test::Equal(self.text(lo, lo))),
                Guarded::Number => self.number(lo, hi)?,
                Guarded::Range { sym } => self.range(lo, self.pos(sym)?, hi + 1),
                Guarded::At => {
                    let at = lo + 1;
                    // A right side that is no pattern (`a @ ..`) is still the form of `@`.
                    let rhs = match cst.child_nodes(n).nth(1) {
                        Some(r) => self.pat(cst, forms, r)?,
                        None => Pat { lo: at, hi: at, kind: PatKind::Bad(Form::At) },
                    };
                    PatKind::At { at, rhs: Box::new(rhs) }
                }
            },
            _ => return None,
        };
        Some(Pat { lo, hi, kind })
    }

    /// The text of the tokens `a..=b` of `toks`.
    fn text(&self, a: usize, b: usize) -> String {
        written(self.c, &self.toks, a, b)
    }

    /// A comment between the tokens `a` and `b` of `toks` (S-251: an edit
    /// over them would remove it).
    fn comment_in(&self, a: usize, b: usize) -> bool {
        (self.toks[a]..=self.toks[b]).any(|i| self.c.comment(i))
    }

    /// A float or a `-` before a constant at `lo..=hi`: `-`, `(`s, the
    /// number or the path and as many `)`s ([`crate::parser::Guarded::Number`]).
    fn number(&self, lo: usize, hi: usize) -> Option<PatKind> {
        let c = self.c;
        let kind = |p: usize| c.kind(self.toks[p]);
        let minus = kind(lo) == TokenKind::Minus;
        let mut at = lo + usize::from(minus);
        while minus && kind(at) == TokenKind::LParen {
            at += 1;
        }
        let opens = at - lo - usize::from(minus);
        // The number: a float (`1.5`), one written as in other languages
        // (`1.`, `0.5f32`, `.5`: the guard writes it in the Onsa spelling).
        let value = match kind(at) {
            TokenKind::Float => c.src(self.toks[at]).to_string(),
            TokenKind::ForeignLit => float_spelling_at(c, self.toks[at])?,
            TokenKind::Dot => format!("0.{}", c.src(self.toks[at + 1])),
            // `-LIMIT`, `-(LIMIT)`, `-I64.MAX` (S-319): the `-` is written
            // against the constant (§2.5, S-123), the blanks after it in the
            // pattern do not go into the guard.
            _ => return Some(PatKind::Hole(Form::Negated, Test::Equal(format!("-{}", self.text(lo + 1, hi))))),
        };
        let (open, close, sign) = ("(".repeat(opens), ")".repeat(opens), if minus { "-" } else { "" });
        Some(PatKind::Hole(Form::Float, Test::Equal(format!("{sign}{open}{value}{close}"))))
    }

    /// The end `a..=b` of a range (tokens of `toks`), as the guard writes it:
    /// in parentheses when it is no bare operand of a comparison (S-341).
    /// `None` when it is not one expression, or holds a comment.
    fn end_text(&self, a: usize, b: usize, side: Side) -> Option<String> {
        if self.comment_in(a, b) {
            return None;
        }
        let c = self.c;
        // A leading prefix `-` is written against its operand in the guard
        // (§2.5, S-123): the blanks after it in the pattern do not go into it.
        let minus = a < b
            && c.kind(self.toks[a]) == TokenKind::Minus
            && !matches!(c.kind(self.toks[a + 1]), TokenKind::Minus | TokenKind::Bang);
        let from = if minus { a + 1 } else { a };
        let (first, last) = (c.full[self.toks[from]] as usize, c.full[self.toks[b]] as usize);
        if !crate::parser::reads_as_expr(c.file, c.text, c.all, c.literals, first, last) {
            return None;
        }
        let text = if minus { format!("-{}", self.text(a + 1, b)) } else { self.text(a, b) };
        let top = operand(&(self.toks[a]..=self.toks[b]).map(|i| c.kind(i)).collect::<Vec<_>>());
        Some(if BinOp::Le.bare(side, top) { text } else { format!("({text})") })
    }

    /// A range from `lo`, with its symbol at `sym` and its end before `end`.
    fn range(&self, lo: usize, sym: usize, end: usize) -> PatKind {
        let symbol = self.c.kind(self.toks[sym]);
        let start = if lo < sym { self.end_text(lo, sym - 1, Side::Left).map(Some) } else { Some(None) };
        let stop = if sym + 1 < end { self.end_text(sym + 1, end - 1, Side::Right).map(Some) } else { Some(None) };
        let end_of = symbol.range_end();
        match (start, stop) {
            // `5..<` has no end to compare with.
            (Some(_), Some(None)) if end_of.is_some() => PatKind::Bad(Form::Range),
            (Some(lo), Some(hi)) => PatKind::Hole(Form::Range, Test::Range { lo, hi, end: end_of }),
            _ => PatKind::Bad(Form::Range),
        }
    }
}

/// The text of the tokens `a..=b` of `toks`.
fn written(c: &Cursor, toks: &[usize], a: usize, b: usize) -> String {
    c.text[c.span(toks[a]).start as usize..c.span(toks[b]).end as usize].to_string()
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

/// Why a pattern has no candidate ([`guard_pattern`]): its row
/// ([`Why::row`]) and the note that says why ([`Why::note`]).
#[derive(Clone, Copy)]
enum Why {
    /// The alternatives differ once the forms are replaced (S-317).
    Skeletons,
    /// A comment lies in a form or in what the candidate removes (S-251):
    /// the alternatives after the first, the right of `@`.
    Comment,
    /// The pattern has no form to write in a guard.
    NoForm,
    /// The arm's own guard has no last token before its `=>`.
    GuardEnd,
    /// The arm's pattern does not read ([`Arm::read`]).
    Unread,
    /// A form makes none (a range whose end is no expression, the right of
    /// `@` that is no literal, constant or range).
    Bad(Form),
    /// A range with a comment in it, which the copy of its ends into the
    /// guard would lose (S-251): the row of the form, as [`Why::Bad`].
    EndComment,
}

impl Why {
    /// The row of a pattern with no candidate whose first form is `head`:
    /// that of the alternatives but where a form makes none (S-48, S-317).
    fn row(&self, head: Form) -> RowId {
        match self {
            Why::Bad(Form::At) => Form::At.choice_row(),
            Why::Bad(_) | Why::EndComment | Why::Unread => head.row(),
            Why::Skeletons | Why::Comment | Why::NoForm | Why::GuardEnd => head.choice_row(),
        }
    }

    /// The note after the row's rule that says why no candidate is made
    /// (A26): a comment the candidate would lose, an end of a range that
    /// does not read, alternatives of other shapes. None for the others,
    /// whose message says it (`@` that is no comparison) or that no input
    /// the reader takes makes.
    fn note(&self) -> Option<&'static str> {
        match self {
            Why::Comment | Why::EndComment => Some(
                "no candidate: a comment in the part the guard form would rewrite would be lost (§18.1); \
                 move it out of the pattern, or write the guard by hand",
            ),
            Why::Bad(Form::Range) => Some(
                "no candidate: an end of the range does not read as an expression a guard could copy; \
                 write the end as an expression, or write the guard by hand",
            ),
            Why::Skeletons => Some(
                "no candidate: once the forms are replaced the alternatives are not of one shape, and one \
                 guard cannot tell which matched; split them into arms, or write the guard by hand",
            ),
            Why::Bad(_) | Why::NoForm | Why::GuardEnd | Why::Unread => None,
        }
    }
}

/// The shape of `p` (S-317): the alternatives of a pattern with holes are
/// one when they have the same skeleton (the tokens but the holes, a group
/// `(p)` as `p`); the first stays, the others are removed, and the condition
/// is the `||` of theirs.
fn shape<'a>(c: &'a Cursor<'_>, toks: &[usize], p: &Pat) -> Result<Shape<'a>, Why> {
    let tok = |pos: usize| Skel::Tok(c.kind(toks[pos]), c.src(toks[pos]));
    let comment = |a: usize, b: usize| (toks[a]..=toks[b]).any(|i| c.comment(i));
    // A literal with the lexer's error (`1x`) is not copied into the guard,
    // where the error would stay (S-236, R-215).
    let unread = |a: usize, b: usize| (toks[a]..=toks[b]).any(|i| !c.literal_ok(i));
    let empty = || Shape { skel: Vec::new(), holes: Vec::new(), cond: Cond::True, edits: Vec::new() };
    match &p.kind {
        PatKind::Hole(form, t) => {
            if unread(p.lo, p.hi) {
                return Err(Why::Bad(*form));
            }
            if comment(p.lo, p.hi) {
                return Err(Why::Comment);
            }
            Ok(Shape {
                skel: vec![Skel::Hole],
                holes: vec![(toks[p.lo], toks[p.hi])],
                cond: Cond::Test(Subject::Hole(0), t.clone()),
                edits: Vec::new(),
            })
        }
        PatKind::Bad(Form::Range) if comment(p.lo, p.hi) => Err(Why::EndComment),
        PatKind::Bad(f) => Err(Why::Bad(*f)),
        PatKind::Leaf(_) => Ok(Shape { skel: (p.lo..=p.hi).map(tok).collect(), ..empty() }),
        PatKind::Paren(inner) => shape(c, toks, inner),
        PatKind::At { rhs, .. } => {
            let name = c.src(toks[p.lo]);
            let cond = at_cond(c, toks, name, rhs).filter(|_| !unread(rhs.lo, rhs.hi)).ok_or(Why::Bad(Form::At))?;
            if comment(p.lo, p.hi) {
                return Err(Why::Comment);
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
                return Err(Why::Skeletons);
            }
            // Remove ` | A_2 | ...`, which must hold no comment.
            let (from, to) = (toks[alts[0].hi], toks[p.hi]);
            if (from..=to).any(|i| c.comment(i)) {
                return Err(Why::Comment);
            }
            let mut shapes = shapes.into_iter();
            // No alternative has no shape: an empty list returned above.
            let Some(mut out) = shapes.next() else {
                onsa_diag::internal::bug(Some(c.span(toks[p.lo])), "alternatives with no shape")
            };
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
            Some(Cond::Test(subject(), Test::Equal(written(c, toks, rhs.lo, rhs.hi))))
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
    // The tokens of one alternative from `start`, and of the right of each
    // `@` it ends at ([`crate::scan::pattern_alternative`]): the reading
    // reads one alternative, no further.
    let mut toks: Vec<usize> = Vec::new();
    let mut from = start;
    loop {
        let rest = (from..c.tokens.len()).filter(|&i| !c.kind(i).is_trivia() || c.kind(i) == TokenKind::Newline);
        let (n, _) = crate::scan::pattern_alternative(rest.clone().map(|i| c.kind(i)));
        let code: Vec<usize> = rest.filter(|&i| !c.kind(i).is_trivia()).take(n + 1).collect();
        toks.extend(&code[..n.min(code.len())]);
        match code.get(n) {
            Some(&at) if n > 0 && c.kind(at) == TokenKind::At => {
                toks.push(at);
                from = at + 1;
            }
            _ => break,
        }
    }
    let (t, p) = Toks::read(c, toks, false, false)?;
    let mut found = Vec::new();
    forms(&p, &mut found);
    let &(form, a, b) = found.first()?;
    (t.toks[a] == c.at).then(|| (form, t.toks[a], t.toks[b]))
}

/// The rows [`guard_pattern`] names ([`super::Matcher::many`]).
pub(super) const GUARD_PATTERN_ROWS: &[RowId] = &[
    RowId::FloatPattern,
    RowId::FloatPatternChoice,
    RowId::InterpolatedStringPattern,
    RowId::NegatedConstantPattern,
    RowId::AtBinding,
    RowId::AtBindingComplex,
    RowId::RangePattern,
    RowId::RangePatternChoice,
];

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
pub(super) fn guard_pattern(c: &Cursor) -> Option<(RowId, Hit)> {
    if c.want != Want::Pattern {
        return None;
    }
    let (form, first, last) = form_at(c)?;
    let alone = c.file_span(c.span(first).start, c.span(last).end);
    // The pattern's owner: the innermost `match` arm, `let` or `for`.
    let owner = c.open.iter().rev().find(|o| matches!(o.0, NodeKind::MatchArm | NodeKind::LetStmt | NodeKind::ForStmt));
    let Some(&(NodeKind::MatchArm, arm_start)) = owner else {
        return found(form.row(), alone, Vec::new());
    };
    // The one choice of the row (RF-23): the first form of the arm read, and
    // why it makes no candidate ([`Why::row`]).
    let read = Arm::read(c, arm_start);
    let mut in_arm = Vec::new();
    if let Some((arm, _)) = &read {
        forms(&arm.pat, &mut in_arm);
    }
    let (head, span) = match (&read, in_arm.first(), in_arm.last()) {
        (Some((arm, _)), Some(&(head, a, _)), Some(&(_, _, b))) => {
            (head, c.file_span(c.span(arm.toks[a]).start, c.span(arm.toks[b]).end))
        }
        _ => (form, alone),
    };
    let outcome = match read {
        Some((arm, None)) if !in_arm.is_empty() => {
            arm.candidates(c, c.names.get_or_init(|| file_names(c.all, c.text, c.literals)))
        }
        Some((_, Some(why))) => Err(why),
        Some((_, None)) | None => Err(Why::Unread),
    };
    match outcome {
        Ok(fixes) => found(head.row(), span, fixes),
        Err(why) => Some((why.row(head), Hit::new(span, Vec::new()).with_note(why.note()))),
    }
}

/// Why [`constants_in_guard`] makes no candidate at the limit of §2.5.
const TOO_DEEP: &str = "no candidate: the guard form would nest over the limit (§2.5); simplify the arm";

/// The names of `p` that start at `constants` (sorted) made holes of the
/// constant they name; how many.
fn mark(c: &Cursor, toks: &[usize], p: &mut Pat, constants: &[u32]) -> usize {
    match &mut p.kind {
        PatKind::Leaf(_) if constants.binary_search(&c.span(toks[p.lo]).start).is_ok() => {
            p.kind = PatKind::Hole(Form::Constant, Test::Equal(written(c, toks, p.lo, p.hi)));
            1
        }
        PatKind::Leaf(_) | PatKind::Hole(..) | PatKind::Bad(_) => 0,
        PatKind::Paren(q) | PatKind::At { rhs: q, .. } => mark(c, toks, q, constants),
        PatKind::Node(v) | PatKind::Or(v) => v.iter_mut().map(|q| mark(c, toks, q, constants)).sum(),
    }
}

/// The candidate of the E0020 of the types stage (§7, S-319): the constants
/// at `constants` (sorted) of the pattern of the arm `arm` in the guard, by
/// the rules of the forms of the syntax stage. Without one, the note that
/// says why, if a reason does. The tokens of the arm's unit are read again
/// from the CST of the file (`tree`, with its `units`): this is the path of
/// an error, and no later stage keeps the parser.
pub fn constants_in_guard(
    tree: &crate::Tree,
    units: &crate::units::Units,
    text: &str,
    arm: Span,
    constants: &[u32],
) -> Result<Fix, Option<&'static str>> {
    let Some(within) = units.reading(&[arm]) else {
        onsa_diag::internal::bug(Some(arm), "an arm of the types stage in no unit")
    };
    let run = tree.cst.tokens()[tree.cst.tokens_in(within.span)].to_vec();
    let Some(made) = crate::parser::with_cursor(arm.file, text, run, &tree.literals, |c| {
        let (mut read, why) = Arm::read(c, arm.start).ok_or(None)?;
        if let Some(why) = why {
            return Err(why.note());
        }
        if mark(c, &read.toks, &mut read.pat, constants) != constants.len() {
            return Err(None);
        }
        let names = tree.names.get_or_init(|| file_names(tree.cst.tokens(), text, &tree.literals));
        // One: a constant is no range, read two ways.
        let fix = read.candidates(c, names).map_err(|why| why.note())?.pop().ok_or(None)?;
        Ok((fix, Span::new(arm.file, arm.start, c.span(read.arrow).end)))
    }) else {
        onsa_diag::internal::bug(Some(arm), "the unit of an arm of the types stage has no token")
    };
    let (fix, window) = made?;
    // The parentheses of a block-like guard after the `&&` (§3.1), as for
    // the candidates of the syntax stage: the unit has no error of that
    // stage, so the completion drops one only over the limit.
    let fix = crate::operands::completed_later(text, units, window, fix).ok_or(Some(TOO_DEEP))?;
    // Each level it adds is of a token it writes (an operator of the guard
    // too, §2.5): a byte at least.
    let written = fix.edits().iter().map(|e| e.replace.len() as u32).sum();
    let limit = crate::nesting::Limit { text, units };
    if limit.exceeded(window, fix.edits(), written) { Err(Some(TOO_DEEP)) } else { Ok(fix) }
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

/// The names of a file that no new name of the guard candidates is (S-253):
/// its identifiers, and the names in the holes of its string literals
/// (S-319: a new name that a misspelt `{v}` names would hide its E0302).
pub(crate) type Names = std::collections::HashSet<Box<str>>;

/// The [`Names`] of the file of the tokens `all` (all of its tokens) and
/// `literals`: the one place that makes them, once for a file (the parser's
/// [`Cursor::names`], the types stage's `crate::Tree`).
pub(crate) fn file_names(all: &[Token], text: &str, literals: &crate::literal::Literals) -> Names {
    #[cfg(test)]
    NAMED.set(NAMED.get() + all.len());
    let idents = all.iter().filter(|t| t.kind == TokenKind::Ident).map(|t| t.span);
    let in_holes = literals.holes().iter().flat_map(|h| h.path.iter().flatten().copied());
    idents.chain(in_holes).map(|s| text[s.start as usize..s.end as usize].into()).collect()
}

#[cfg(test)]
thread_local! {
    /// The tokens [`file_names`] went through on this thread: the tests see
    /// that a file of many guard forms makes its names once.
    pub(crate) static NAMED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    /// outside brackets, the guard to `=>`, read as the parser reads a
    /// pattern ([`Toks::read`]); `None` when it does not read. When it reads
    /// only without the block comments, that arm and why, if a reason the
    /// note says ([`Why::note`]): the reading takes no block comment, and one
    /// in what the candidate rewrites would be lost, as the shape tests a
    /// comment ([`shape`]: [`Why::Comment`], [`Why::EndComment`]).
    fn read(c: &Cursor, arm_start: u32) -> Option<(Arm, Option<Why>)> {
        let commented = match Arm::read_tokens(c, arm_start, false) {
            Ok(arm) => return Some((arm, None)),
            Err(commented) => commented,
        };
        let arm = commented.then(|| Arm::read_tokens(c, arm_start, true).ok()).flatten()?;
        match shape(c, &arm.toks, &arm.pat) {
            Err(why @ (Why::Comment | Why::EndComment)) => Some((arm, Some(why))),
            _ => None,
        }
    }

    /// [`Arm::read`], without the block comments when `skip_blocks`; when it
    /// does not read, whether a block comment is among the pattern's tokens.
    fn read_tokens(c: &Cursor, arm_start: u32, skip_blocks: bool) -> Result<Arm, bool> {
        let first = c.index_at(arm_start);
        let mut depth = 0i32;
        let mut toks = Vec::new();
        let mut i = first;
        let (if_tok, arrow) = loop {
            match c.kind(i) {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth -= 1,
                TokenKind::KwIf if depth == 0 => {
                    // Its `=>` is outside the brackets of the guard (`if { c } =>`).
                    let mut j = i + 1;
                    while depth > 0 || c.kind(j) != TokenKind::FatArrow {
                        match c.kind(j) {
                            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth > 0 => depth -= 1,
                            TokenKind::Eof | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                                return Err(false);
                            }
                            _ => {}
                        }
                        j += 1;
                    }
                    break (Some(i), j);
                }
                TokenKind::FatArrow if depth == 0 => break (None, i),
                TokenKind::Eof => return Err(false),
                _ => {}
            }
            if depth < 0 {
                return Err(false);
            }
            let skipped = c.kind(i).is_trivia() || (skip_blocks && c.kind(i) == TokenKind::BlockComment);
            if !skipped {
                toks.push(i);
            }
            i += 1;
        };
        let last_pat = *toks.last().ok_or(false)?;
        let commented = toks.iter().any(|&t| c.kind(t) == TokenKind::BlockComment);
        let (t, pat) = Toks::read(c, toks, true, skip_blocks).ok_or(commented)?;
        Ok(Arm { toks: t.toks, pat, if_tok, arrow, last_pat })
    }

    /// The candidates: one, or two when a range is written `..` or `...`
    /// (the end excluded, then included). The new names are none of `used`,
    /// the names of the file ([`file_names`]).
    fn candidates(&self, c: &Cursor, used: &Names) -> Result<Vec<Fix>, Why> {
        let shape = shape(c, &self.toks, &self.pat)?;
        if shape.holes.is_empty() && matches!(shape.cond, Cond::True) {
            return Err(Why::NoForm);
        }
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
                    let g_last = c.sig_before(self.arrow).ok_or(Why::GuardEnd)?;
                    let g = operand(&(g_first..=g_last).map(|i| c.kind(i)).collect::<Vec<_>>());
                    let cond = if BinOp::And.bare(Side::Left, top) { cond } else { format!("({cond})") };
                    // A guard against its `if` (`if(c)`) stays apart from the word (§18.1, R-235).
                    let lead = if c.gap_after(t) == Gap::None { " " } else { "" };
                    if BinOp::And.bare(Side::Left, g) {
                        edits.push(Edit::insert(c.file, c.span(g_first).start, format!("{lead}{cond} && ")));
                    } else {
                        edits.push(Edit::insert(c.file, c.span(g_first).start, format!("{lead}{cond} && (")));
                        edits.push(Edit::insert(c.file, c.span(g_last).end, ")"));
                    }
                }
            }
            fixes.push(Fix::new(title, edits));
        }
        Ok(fixes)
    }
}
