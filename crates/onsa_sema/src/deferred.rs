//! Checks that wait for a type a later statement decides (spec §4.5, §4.7;
//! S-174, S-184, S-226, S-235).
//!
//! The body inference (§4.7) goes statement by statement, and a type variable
//! may be decided by a later statement. Every check that needs a decided type
//! and may have to wait is one [`Deferred`] item, kept in the order the checker
//! made them (the order of checking: an operand before its operator). The
//! items are checked at two points only:
//!
//! - after each statement that was checked without an error ([`Checker::check_deferred_now`]):
//!   the items whose type has no variable left;
//! - at the end of the body, after the integer literals got their default
//!   ([`Checker::check_deferred_end`]): every item.
//!
//! The first item that fails is the one diagnostic of the body (P-01). The
//! order is in the mark of [`Checker::check_deferred_now`].

use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::ExprId;

use crate::body::{Checker, LocalId, R, bound_name};
use crate::def::Bound;
use crate::infer::Cause;
use crate::ty::{IntKind, Ty, TyId};

/// What a deferred item checks.
#[derive(Debug, Clone)]
pub(crate) enum DeferredKind {
    /// An integer literal of an expression or a pattern: its range once the type
    /// is known (E0408). `neg`: a prefix `-` belongs to the value (§4.7, S-227),
    /// and an unsigned type is then E0401 (§3.4). `lit`: the literal expression
    /// (`None` in a pattern).
    IntLit { value: u64, neg: bool, lit: Option<ExprId> },
    /// A negation of a value whose type is still a literal variable: E0401 when it
    /// is decided to be unsigned (§3.4).
    UnsignedNeg,
    /// A float literal: E0405 when its type is still open at the end (§2.4).
    FloatLit,
    /// A type variable that an expression made (a type parameter of a call,
    /// `None`, `Buf.zeroed(4)`, `[]`): E0406 when it is still open at the end
    /// (§4.5, §4.7). `what` names it in the message.
    Origin { what: String },
    /// A requirement on a type (a bound, the implicit `Dup`, a kind constraint):
    /// E0416 when the decided type does not meet it (§4.5, §4.6).
    Require { bound: Bound, what: Required },
    /// A typed hole (E0421), reported at the end with the decided type.
    Hole { visible: Vec<LocalId> },
}

/// The type a requirement is on.
#[derive(Debug, Clone)]
pub(crate) enum Required {
    /// A type parameter `param` of `owner` (`` `need_f` ``, ``the `impl` of `Wrap` ``):
    /// its bounds and the implicit `Dup`.
    Param { param: String, owner: String },
    /// The element of `[e; N]` (`Dup`, §2.4).
    RepeatElement,
    /// The element of `Buf` / `Span` (`Copy`, §4.5).
    BufElement,
}

#[derive(Debug, Clone)]
pub(crate) struct Deferred {
    /// The order the checker made the items in.
    pub(crate) seq: u32,
    /// Where the diagnostic goes.
    pub(crate) span: Span,
    pub(crate) ty: TyId,
    pub(crate) kind: DeferredKind,
}

/// The outcome of looking at one item.
enum Look {
    /// Not decided yet: keep it.
    Wait,
    /// Decided and met (or nothing to check any more): drop it.
    Done,
    Fail(Diagnostic),
}

impl<'a> Checker<'a> {
    pub(crate) fn defer(&mut self, span: Span, ty: TyId, kind: DeferredKind) {
        let seq = self.deferred_count;
        self.deferred_count += 1;
        let item = Deferred { seq, span, ty, kind };
        // The items only the end decides (E0405, E0406, E0421) wait in their own list, so
        // that the statements do not walk them.
        match item.kind {
            DeferredKind::FloatLit | DeferredKind::Origin { .. } | DeferredKind::Hole { .. } => {
                self.deferred_end.push(item)
            }
            _ => self.deferred.push(item),
        }
    }

    /// After a statement: check the items whose type has no variable left.
    // SPEC-GAP(S-255): §4.5 / §4.7 check these "in the statement in which the type has no
    // variable left" and do not order them against the other errors of that statement, nor
    // against each other. Here an error found while the statement is checked comes first
    // (the checking stops there, §18.1), and the items of one point (a statement, the end of
    // the body) are reported in the order they were made; the same order puts the inner
    // literal of `-(-1)` before the outer negation also when a later statement decides the type.
    pub(crate) fn check_deferred_now(&mut self) -> R<()> {
        // Only a binding decides a waiting item: when no variable was bound since the last
        // look, the items seen then still wait and only the new ones are looked at (a body
        // of many open literals stays linear, W2-06/b).
        let generation = self.infer.generation();
        let start =
            if generation == self.deferred_generation { self.deferred_seen.min(self.deferred.len()) } else { 0 };
        let mut keep = std::mem::take(&mut self.deferred);
        let items = keep.split_off(start);
        let mut fail = None;
        for item in items {
            if fail.is_some() {
                keep.push(item);
                continue;
            }
            match self.look(&item, false) {
                Look::Wait => keep.push(item),
                Look::Done => {}
                Look::Fail(d) => fail = Some(d),
            }
        }
        self.deferred = keep;
        self.deferred_seen = self.deferred.len();
        self.deferred_generation = self.infer.generation();
        match fail {
            Some(d) => Err(self.diag(d)),
            None => Ok(()),
        }
    }

    /// At the end of the body: apply the integer default, then check every item.
    pub(crate) fn check_deferred_end(&mut self) {
        let i32_ = self.a.types.int(IntKind::I32);
        self.infer.default_int_literals(i32_);
        let mut items = std::mem::take(&mut self.deferred);
        items.append(&mut self.deferred_end);
        items.sort_by_key(|d| d.seq);
        // A requirement whose type is still open is not checked; the open variable
        // is reported (E0406 / E0405). When nothing reports it, the requirement is
        // E0406 at the expression that made it, rather than passing silently.
        let mut open_requirement: Option<Deferred> = None;
        for item in &items {
            match self.look(item, true) {
                Look::Fail(d) => {
                    self.diag(d);
                    return;
                }
                Look::Wait => {
                    if open_requirement.is_none() && matches!(item.kind, DeferredKind::Require { .. }) {
                        open_requirement = Some(item.clone());
                    }
                }
                Look::Done => {}
            }
        }
        if let Some(item) = open_requirement {
            let what = match &item.kind {
                DeferredKind::Require { what: Required::Param { param, owner }, .. } => {
                    format!("the type parameter `{param}` of {owner}")
                }
                _ => "the type of this expression".to_string(),
            };
            let d = Diagnostic::new(
                Stage::Types,
                Code::E0406,
                item.span,
                format!("{what} cannot be determined by the end of the function; annotate it (§4.5)"),
            )
            .with_found(self.src(item.span));
            self.diag(d);
        }
    }

    /// One item. `end`: the body is finished (the open items fail or are dropped).
    fn look(&mut self, item: &Deferred, end: bool) -> Look {
        // Still waiting: answered without building the resolved type.
        let waits = match item.kind {
            DeferredKind::IntLit { .. } | DeferredKind::UnsignedNeg => self.infer.is_unresolved(&self.a.types, item.ty),
            DeferredKind::Require { .. } => self.infer.has_vars(&self.a.types, item.ty),
            _ => false,
        };
        if waits && !end {
            return Look::Wait;
        }
        let r = self.infer.resolve(&mut self.a.types, item.ty);
        match &item.kind {
            DeferredKind::IntLit { value, neg, .. } => match self.ty(r) {
                Ty::Var(_) => Look::Wait,
                Ty::Int(k) => self.int_lit(item, r, k, *value, *neg),
                _ => Look::Done,
            },
            DeferredKind::UnsignedNeg => match self.ty(r) {
                Ty::Var(_) => Look::Wait,
                Ty::Int(k) if !k.signed() => Look::Fail(
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0401,
                        item.span,
                        format!("`-` on the unsigned type `{}`; it has no unary `-` (§3.4)", k.name()),
                    )
                    .with_found(self.src(item.span)),
                ),
                _ => Look::Done,
            },
            DeferredKind::FloatLit => match self.ty(r) {
                Ty::Var(_) if end => Look::Fail(
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0405,
                        item.span,
                        "the type of this float literal cannot be determined; annotate it (§2.4)",
                    )
                    .with_found(self.src(item.span)),
                ),
                Ty::Var(_) => Look::Wait,
                _ => Look::Done,
            },
            DeferredKind::Origin { what } => {
                if !self.infer.has_vars(&self.a.types, r) {
                    return Look::Done;
                }
                if !end {
                    return Look::Wait;
                }
                // Only literal variables are left: E0405 / the default covers them.
                if !self.infer.has_open_vars(&self.a.types, r) {
                    return Look::Done;
                }
                Look::Fail(
                    Diagnostic::new(
                        Stage::Types,
                        Code::E0406,
                        item.span,
                        format!("{what} cannot be determined by the end of the function; annotate it (§4.5, §4.7)"),
                    )
                    .with_found(self.src(item.span)),
                )
            }
            DeferredKind::Require { bound, what } => {
                if self.infer.has_vars(&self.a.types, r) {
                    return Look::Wait;
                }
                if self.meets(r, *bound) {
                    return Look::Done;
                }
                let shown = self.display(r);
                let msg = match what {
                    Required::RepeatElement => format!(
                        "`[e; N]` repeats the value of `e`, so its type must be Copy or Shared (`Dup`); `{shown}` is not; make an Affine array with `array.from_fn` (§2.4)"
                    ),
                    Required::BufElement => format!("the element type of `Buf` must be Copy; `{shown}` is not (§4.5)"),
                    Required::Param { param, owner } if *bound == Bound::Dup => format!(
                        "`{shown}` is not Copy or Shared, so it does not satisfy `{param}: Dup` of {owner}; a type parameter takes only Copy or Shared types unless it is declared `{param}: ?Dup` (§4.5)"
                    ),
                    Required::Param { param, owner } => format!(
                        "`{shown}` does not satisfy the bound `{param}: {}` of {owner} (§4.5)",
                        bound_name(*bound)
                    ),
                };
                let mut d = Diagnostic::new(Stage::Types, Code::E0416, item.span, msg).with_found(self.src(item.span));
                d = self.decided_note(d, item.ty, &shown);
                Look::Fail(d)
            }
            DeferredKind::Hole { visible } => {
                if !end {
                    return Look::Wait;
                }
                let mut candidates = Vec::new();
                for &id in visible {
                    let lt = self.local_ty(id);
                    if self.infer.resolve(&mut self.a.types, lt) == r {
                        candidates.push(self.info.locals[id.0 as usize].name.clone());
                    }
                }
                let msg = match self.ty(r) {
                    Ty::Var(_) => "hole; the expected type is not known here".to_string(),
                    _ => {
                        let shown = self.display(r);
                        if candidates.is_empty() {
                            format!("hole of type `{shown}`")
                        } else {
                            format!("hole of type `{shown}`; candidates: {}", candidates.join(", "))
                        }
                    }
                };
                Look::Fail(Diagnostic::new(Stage::Types, Code::E0421, item.span, msg).with_found("_"))
            }
        }
    }

    /// The range of an integer literal whose type is decided (§4.7: the prefix `-`
    /// written on the literal is a part of the value, S-184, S-227).
    fn int_lit(&mut self, item: &Deferred, r: TyId, k: IntKind, value: u64, neg: bool) -> Look {
        if neg && !k.signed() {
            return Look::Fail(
                Diagnostic::new(
                    Stage::Types,
                    Code::E0401,
                    item.span,
                    format!("`-` on the unsigned type `{}`; it has no unary `-`, also for `-0` (§3.4, §4.7)", k.name()),
                )
                .with_found(self.src(item.span)),
            );
        }
        let v = if neg { -(value as i128) } else { value as i128 };
        let (lo, hi) = k.range();
        if lo <= v && v <= hi {
            return Look::Done;
        }
        let hint = if self.infer.decided_by(&self.a.types, item.ty) == Some(Cause::Default) {
            " (the default for an unconstrained integer literal); add an annotation such as `: U32` or `: I64`"
        } else {
            ""
        };
        let _ = r;
        Look::Fail(
            Diagnostic::new(
                Stage::Types,
                Code::E0408,
                item.span,
                format!("literal `{}{value}` is out of range for `{}`{hint}", if neg { "-" } else { "" }, k.name()),
            )
            .with_found(self.src(item.span)),
        )
    }

    /// The note of E0416: the expression whose check decided the type (§4.5),
    /// or, for the integer default, a note without a position.
    fn decided_note(&mut self, d: Diagnostic, ty: TyId, shown: &str) -> Diagnostic {
        match self.infer.decided_by(&self.a.types, ty) {
            Some(Cause::At { span, why }) => {
                let why = why.map(|w| format!(" as {w}")).unwrap_or_default();
                d.with_note(span, format!("the type became `{shown}` here{why}"))
            }
            Some(Cause::Default) => d.with_rule(format!(
                "the type became `{shown}` by the default of an integer literal (§4.7); a bound does not change the default: write a float literal such as `3.0` or annotate the type"
            )),
            None => d,
        }
    }

    /// Whether a decided type meets a requirement (the bounds of §6.3 and the
    /// kind constraints `Copy` / `Dup` of §4.6).
    fn meets(&self, t: TyId, b: Bound) -> bool {
        if self.satisfies(t, b) {
            return true;
        }
        // The kind of a user type that holds a type parameter of the body is not
        // computed (`kind_of` is `None`): such a constraint is not decided here and passes.
        // R-176 (W5-08): a `?Dup` parameter inside makes the type not `Dup`
        // (`tests/spec/negative/dup_maybe_dup_param.onsa`, in the pending list).
        if matches!(b, Bound::Dup | Bound::Copy) && !matches!(self.ty(t), Ty::Param(_)) && self.a.kind_of(t).is_none() {
            return true;
        }
        false
    }
}
