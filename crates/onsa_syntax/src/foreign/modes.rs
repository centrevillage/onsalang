//! The rows of the references and the modes of other languages (`&mut x`,
//! `&self`, `mut self`; §5.2, S-250, R-173).

use super::*;

/// `&` and `&mut` of Rust (§5.2, S-250, R-173): before a parameter's name
/// (`&mut self`, `&self`), in a parameter's type (`v: &mut T` is `inout v:
/// T`, `v: &T` is `v: T`), in another type (`&T` is `T`; `&mut T` has no
/// form: E0002), before an argument (`&mut x` is `inout x`; `&x` is `x`, or
/// `inout x`) and in another expression (`&x` is `x`; `&mut x`: E0002).
pub(super) fn reference(c: &Cursor) -> Option<(RowId, Hit)> {
    // A `&` at the head of a line that goes on with the line before is read
    // as the binary operator (`leading_operator`, S-124, W3-06): no
    // reference (the order of the diagnostics would choose the same, S-281,
    // by the order of the two messages: to be checked again when either
    // changes).
    if c.kind(c.at) != TokenKind::Amp || super::lines::leading(c).is_some() {
        return None;
    }
    let amp = c.at;
    let is_mut = c.ref_mut(amp);
    let mark_end = if is_mut { c.sig_after(amp) } else { amp };
    let operand = mark_end + 1;
    // The form, from the `&` to its `mut` (S-316), and what its candidates
    // edit: the mark and the blanks after it.
    let mark = c.file_span(c.span(amp).start, c.span(mark_end).end);
    let edited = Mark::of(c, amp, mark_end, operand);
    let mode = c.sig_before(amp).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
    match c.want {
        // `&self` where the parameter starts (after its mode, if any; not `x&self`).
        Want::Other
            if c.top() == Some(NodeKind::Param)
                && c.kind(operand) == TokenKind::KwSelf
                && (mode.is_some() || c.open_at(0).is_some_and(|o| o.1 == c.span(amp).start)) =>
        {
            if is_mut {
                // A mode before it is not written twice (`inout &mut self`).
                found(RowId::RefMutSelf, mark, mode_and_mark(c, mode, &edited, Some("inout ")))
            } else {
                found(RowId::RefSelf, mark, vec![edited.delete("remove the `&`")])
            }
        }
        Want::Type => {
            let in_param = c.top() == Some(NodeKind::Param);
            let in_fn_type = c.top() == Some(NodeKind::FnTypeParams);
            if !is_mut {
                return found(RowId::RefType, mark, vec![edited.delete("remove the `&`")]);
            }
            if in_fn_type {
                return found(RowId::RefMutParam, mark, mode_and_mark(c, mode, &edited, Some("inout ")));
            }
            if !in_param {
                return found(RowId::RefMutOther, mark, Vec::new());
            }
            // `name: &mut T`: the name before the `:`, and a mode before it.
            let colon = c.sig_before(amp).filter(|&k| c.kind(k) == TokenKind::Colon)?;
            let name = c.sig_before(colon)?;
            let mode = c.sig_before(name).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
            let fixes = match mode {
                None => vec![Fix::new(
                    "write `inout` before the name",
                    [vec![Edit::insert(c.file, c.span(name).start, "inout ")], edited.deleted()].concat(),
                )],
                _ => mode_and_mark(c, mode, &edited, None),
            };
            found(RowId::RefMutParam, mark, fixes)
        }
        Want::Expr => {
            let in_arg = c.top() == Some(NodeKind::Arg);
            // `f(inout &mut x)`, `f(inout &x)`: the mode is there; the mark goes.
            if in_arg && mode.is_some_and(|m| c.kind(m) == TokenKind::KwInout) {
                return found(
                    if is_mut { RowId::RefMutArg } else { RowId::RefExpr },
                    mark,
                    vec![edited.delete("remove the reference mark")],
                );
            }
            let in_arg = in_arg && mode.is_none();
            match (is_mut, in_arg) {
                (true, true) => found(RowId::RefMutArg, mark, vec![edited.replace("write `inout`", "inout ")]),
                (true, false) => found(RowId::RefMutOther, mark, Vec::new()),
                (false, true) => found(
                    RowId::RefExpr,
                    mark,
                    vec![edited.delete("remove the `&`"), edited.replace("write `inout`", "inout ")],
                ),
                (false, false) => found(RowId::RefExpr, mark, vec![edited.delete("remove the `&`")]),
            }
        }
        _ => None,
    }
}

/// The candidates for a reference mark (`&mut `, `mut `, with its blanks:
/// `mark`) after the mode `mode` of a parameter: with `inout`, the mark goes;
/// with `move`, the reading is not one, the caller's value changing
/// (`inout`) or taken (`move`): both. Without a mode, `with` (the mode to
/// write in place of the mark), if any. A mode is never written twice.
fn mode_and_mark(c: &Cursor, mode: Option<usize>, mark: &Mark, with: Option<&str>) -> Vec<Fix> {
    match mode {
        Some(m) if c.kind(m) == TokenKind::KwInout => vec![mark.delete("remove the mark")],
        Some(m) => vec![
            Fix::new("write `inout` for `move`", [vec![Edit::replace(c.span(m), "inout")], mark.deleted()].concat()),
            mark.delete("remove the mark"),
        ],
        None => with.map(|w| mark.replace(&format!("write `{}`", w.trim()), w)).into_iter().collect(),
    }
}

/// What the candidates of a reference mark edit (`&` or `&mut`, and the
/// blanks after it): one range when only blanks are in it (`&mut `,
/// `& mut `), else the `&` and the `mut` with its blanks apart, so that a
/// comment or a line break between them stays where it is (S-251: an edit
/// takes no token it does not change and no comment).
struct Mark {
    parts: Vec<Span>,
}

impl Mark {
    /// The mark of the `&` at `amp` whose last token is `last` (the `&` or
    /// its `mut`), before the token `operand`.
    fn of(c: &Cursor, amp: usize, last: usize, operand: usize) -> Mark {
        let to_operand = |from: usize| c.file_span(c.span(from).start, c.span(operand).start);
        let parts =
            if last == amp || last == amp + 1 { vec![to_operand(amp)] } else { vec![c.span(amp), to_operand(last)] };
        Mark { parts }
    }

    /// The edits that take the mark out.
    fn deleted(&self) -> Vec<Edit> {
        self.parts.iter().map(|&s| Edit::delete(s)).collect()
    }

    /// The candidate `title` that takes the mark out.
    fn delete(&self, title: &str) -> Fix {
        Fix::new(title, self.deleted())
    }

    /// The candidate `title` that writes `with` in place of the mark (where
    /// the `&` is).
    fn replace(&self, title: &str, with: &str) -> Fix {
        let mut edits = self.deleted();
        edits[0] = Edit::replace(self.parts[0], with);
        Fix::new(title, edits)
    }
}

/// `mut self` of Rust: a receiver the method takes is `move self` (S-250).
/// After a mode (`inout mut self`), the `mut` goes.
pub(super) fn mut_self(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::KwSelf || c.top() != Some(NodeKind::Param) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.mut_word(m))?;
    let span = c.file_span(c.span(m).start, c.span(c.at).end);
    let mode = c.sig_before(m).filter(|&k| matches!(c.kind(k), TokenKind::KwInout | TokenKind::KwMove));
    if mode.is_some() {
        return hit(span, vec![Fix::delete("remove the `mut`", c.file_span(c.span(m).start, c.span(c.at).start))]);
    }
    hit(span, vec![Fix::replace("write `move self`", c.span(m), "move")])
}
