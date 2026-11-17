//! The storage of a binding that an arm or a block declares, read after
//! the arm or the block ends (§5.2, S-1115, S-1118): E0716.

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Stage};
use onsa_syntax::ast::{ExprId, ExprKind};

use super::check::Walker;
use super::place::place_of;
use crate::Kind;
use crate::binding::Bind;
use crate::body::{LocalId, LocalKind};
use crate::sources::{Leaf, Open, What, leaves};

/// What reads the value at a position that does not consume it (§12.2),
/// after the arm or the block of its tail ends.
#[derive(Clone, Copy)]
pub(super) struct Reader {
    words: &'static str,
    /// A head at a borrow row (§5.4).
    head: bool,
}

const fn reader(words: &'static str, head: bool) -> Reader {
    Reader { words, head }
}

impl Reader {
    pub(super) const CALL: Reader = reader("the call", false);
    pub(super) const OPERATION: Reader = reader("the operation", false);
    pub(super) const INDEX: Reader = reader("the index", false);
    pub(super) const FIELD: Reader = reader("the field", false);
    pub(super) const LET: Reader = reader("the `let`", true);
    pub(super) const FOR: Reader = reader("the `for`", true);
    pub(super) const MATCH: Reader = reader("the `match`", true);
}

/// The E0716 of a tail ([`Walker::scoped_diag`]): the binding `local` it is
/// rooted at; `viewed`, through a partial view or a binding derived from
/// it; `whole`, with no path; `made`, every other tail of the value is a
/// value made, no place (so a `move` of it makes the row owned, §5.4).
struct Ends {
    local: LocalId,
    viewed: bool,
    whole: bool,
    made: bool,
}

impl Walker<'_> {
    /// E0716 of the value `within`, an `if`, a `match` or a block that
    /// `reader` reads ([`Walker::ends_inside`]); of another value, none: the
    /// tails of its bases are of the positions that read them.
    pub(super) fn scoped(&mut self, within: ExprId, reader: Reader) {
        let x = self.ast.without_parens(within);
        if let ExprKind::If { .. } | ExprKind::Match { .. } | ExprKind::Block(_) = self.ast.expr(x).kind {
            let leaves = leaves(self.cx(), within, Open::No);
            self.ends_inside(&leaves, within, reader);
        }
    }

    /// E0716 (§5.2, S-1115): of the leaves of `within` ([`leaves`]) that are
    /// its own tails (the tails of a base are of the position that reads the
    /// base), the first place whose expression written at the tail is not
    /// Copy and whose root, the binding it derives from (S-796), `within`
    /// declares; not a binding that needs no drop (S-1118), nor a tail of the
    /// error type (§18.1). At the tail, noted at the binding; no candidate.
    pub(super) fn ends_inside(&mut self, leaves: &[Leaf], within: ExprId, reader: Reader) {
        let inside = self.ast.expr(within).span;
        for leaf in leaves.iter().filter(|l| !l.through()) {
            let What::Place(b) = leaf.what else { continue };
            let Some(place) = place_of(self.ast, self.names, b) else {
                bug(Some(self.ast.expr(b).span), "a place leaf with no place")
            };
            let local = |l: LocalId| &self.info.locals[l.0 as usize];
            let declared = |l: &LocalId| inside.start <= local(*l).span.start && local(*l).span.end <= inside.end;
            let Some(l) = self.deps.origins(place.root).find(declared) else { continue };
            let at = self.ast.without_parens(leaf.at);
            let Some(&ty) = self.info.expr_types.get(&at) else {
                bug(Some(self.ast.expr(at).span), "a tail with no type")
            };
            // Not `Walker::owned` (whether it needs a drop): a view needs none
            // and is no Copy value either, a second-class one has no kind (§4.6).
            let copied = match self.kind_of(ty) {
                Some(k) => k == Kind::Copy,
                None => self.class_of(ty).is_none(),
            };
            if local(l).state == (Bind::Borrow { no_drop: true }) || copied {
                continue;
            }
            let made = leaves.iter().all(|o| std::ptr::eq(o, leaf) || matches!(o.what, What::Value(_)));
            let (viewed, whole) = (place.root != l || leaf.viewed, place.proj.is_empty());
            let d = self.scoped_diag(leaf, Ends { local: l, viewed, whole, made }, reader);
            return self.report(d);
        }
    }

    /// The E0716 of `leaf` (`ends`): the note says how the binding is put
    /// before the reader; of a head whose other tails are made, how it is
    /// taken with `move` (an owned row, §5.4); of a binding of an arm, how the
    /// value of the `match` is.
    fn scoped_diag(&self, leaf: &Leaf, ends: Ends, reader: Reader) -> Diagnostic {
        let local = &self.info.locals[ends.local.0 as usize];
        let (n, by) = (&local.name, reader.words);
        let what = match (ends.viewed, ends.whole) {
            (true, _) => "a view of it",
            (_, true) => "it",
            _ => "a part of it",
        };
        let message = format!("`{n}` ends with the arm or block that declares it, before {by} reads {what} (§5.2)");
        let note = match local.kind {
            _ if reader.head && !ends.viewed && ends.whole && ends.made => {
                format!("`{n}` is declared here; write `move {n}` at the tail to take its value (§5.4)")
            }
            LocalKind::MatchBind => {
                format!(
                    "`{n}` is bound by the pattern of this arm; bind the value of the `match` with a `let` before {by}"
                )
            }
            _ => format!("`{n}` is declared here; declare it before {by}"),
        };
        Diagnostic::new(Stage::Modes, Code::E0716, self.ast.expr(leaf.at).span, message).with_note(local.span, note)
    }
}
