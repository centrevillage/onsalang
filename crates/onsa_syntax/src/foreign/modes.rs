//! The rows of the references and the modes of other languages (`&mut x`,
//! `&self`, `mut self`; §5.2, S-250, R-173).

use super::*;

/// `&` and `&mut` of Rust (§5.2, S-250, R-173): before a parameter's name
/// (`&mut self`, `&self`), in a parameter's type (`v: &mut T` is `inout v:
/// T`, `v: &T` is `v: T`), in another type (`&T` is `T`; `&mut T` has no
/// form: E0002), before an argument (`&mut x` is `inout x`; `&x` is `x`, or
/// `inout x`) and in another expression (`&x` is `x`; `&mut x`: E0002).
pub(super) fn reference(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::Amp {
        return None;
    }
    let amp = c.at;
    let is_mut = c.is_ident(amp + 1, "mut");
    let mark_end = if is_mut { amp + 1 } else { amp };
    let operand = mark_end + 1;
    let mark = c.file_span(c.span(amp).start, c.span(mark_end).end);
    // The mark and the blanks after it.
    let mark_and_space = c.file_span(mark.start, c.span(operand).start);
    let mode = c.sig_before(amp).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
    match c.want {
        // `&self` where the parameter starts (after its mode, if any; not `x&self`).
        Want::Other
            if c.top() == Some(NodeKind::Param)
                && c.kind(operand) == TokenKind::KwSelf
                && (mode.is_some() || c.open_at(0).is_some_and(|o| o.1 == c.span(amp).start)) =>
        {
            if is_mut {
                c.say(RowId::RefMutSelf);
                // A mode before it is not written twice (`inout &mut self`).
                hit(mark, mode_and_mark(c, mode, mark_and_space, Some("inout ")))
            } else {
                c.say(RowId::RefSelf);
                hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)])
            }
        }
        Want::Type => {
            let in_param = c.top() == Some(NodeKind::Param);
            let in_fn_type = c.top() == Some(NodeKind::FnTypeParams);
            if !is_mut {
                c.say(RowId::RefType);
                return hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)]);
            }
            if in_fn_type {
                c.say(RowId::RefMutParam);
                return hit(mark, mode_and_mark(c, mode, mark_and_space, Some("inout ")));
            }
            if !in_param {
                c.say(RowId::RefMutOther);
                return hit(mark, Vec::new());
            }
            c.say(RowId::RefMutParam);
            // `name: &mut T`: the name before the `:`, and a mode before it.
            let colon = c.sig_before(amp).filter(|&k| c.kind(k) == TokenKind::Colon)?;
            let name = c.sig_before(colon)?;
            let mode = c.sig_before(name).filter(|&m| matches!(c.kind(m), TokenKind::KwInout | TokenKind::KwMove));
            let fixes = match mode {
                None => vec![Fix::new(
                    "write `inout` before the name",
                    vec![Edit::insert(c.file, c.span(name).start, "inout "), Edit::delete(mark_and_space)],
                )],
                _ => mode_and_mark(c, mode, mark_and_space, None),
            };
            hit(mark, fixes)
        }
        Want::Expr => {
            let in_arg = c.top() == Some(NodeKind::Arg);
            // `f(inout &mut x)`, `f(inout &x)`: the mode is there; the mark goes.
            if in_arg && mode.is_some_and(|m| c.kind(m) == TokenKind::KwInout) {
                c.say(if is_mut { RowId::RefMutArg } else { RowId::RefExpr });
                return hit(mark, vec![Fix::delete("remove the reference mark", mark_and_space)]);
            }
            let in_arg = in_arg && mode.is_none();
            match (is_mut, in_arg) {
                (true, true) => {
                    c.say(RowId::RefMutArg);
                    hit(mark, vec![Fix::replace("write `inout`", mark_and_space, "inout ")])
                }
                (true, false) => {
                    c.say(RowId::RefMutOther);
                    hit(mark, Vec::new())
                }
                (false, true) => {
                    c.say(RowId::RefExpr);
                    hit(
                        mark,
                        vec![
                            Fix::delete("remove the `&`", mark_and_space),
                            Fix::replace("write `inout`", mark_and_space, "inout "),
                        ],
                    )
                }
                (false, false) => {
                    c.say(RowId::RefExpr);
                    hit(mark, vec![Fix::delete("remove the `&`", mark_and_space)])
                }
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
fn mode_and_mark(c: &Cursor, mode: Option<usize>, mark: Span, with: Option<&str>) -> Vec<Fix> {
    match mode {
        Some(m) if c.kind(m) == TokenKind::KwInout => vec![Fix::delete("remove the mark", mark)],
        Some(m) => vec![
            Fix::new("write `inout` for `move`", vec![Edit::replace(c.span(m), "inout"), Edit::delete(mark)]),
            Fix::delete("remove the mark", mark),
        ],
        None => with.map(|w| Fix::replace(format!("write `{}`", w.trim()), mark, w)).into_iter().collect(),
    }
}

/// `mut self` of Rust: a receiver the method takes is `move self` (S-250).
/// After a mode (`inout mut self`), the `mut` goes.
pub(super) fn mut_self(c: &Cursor) -> Option<Hit> {
    if c.kind(c.at) != TokenKind::KwSelf || c.top() != Some(NodeKind::Param) {
        return None;
    }
    let m = c.before(c.at).filter(|&m| c.is_ident(m, "mut"))?;
    let span = c.file_span(c.span(m).start, c.span(c.at).end);
    let mode = c.sig_before(m).filter(|&k| matches!(c.kind(k), TokenKind::KwInout | TokenKind::KwMove));
    if mode.is_some() {
        return hit(span, vec![Fix::delete("remove the `mut`", c.file_span(c.span(m).start, c.span(c.at).start))]);
    }
    hit(span, vec![Fix::replace("write `move self`", c.span(m), "move")])
}
