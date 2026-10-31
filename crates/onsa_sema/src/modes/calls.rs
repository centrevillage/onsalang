//! The calls (W4-07 memo 2.5; §5.2, §3.5): what the callee's parameters
//! take, the marks of the arguments checked against it (E0703), and the `!`
//! of an `inout self` method (E0713, E0714). The receiver and then the
//! arguments are walked from the left, each at the position its parameter
//! gives, whatever its mark.

use std::mem::replace;

use onsa_diag::internal::bug;
use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};
use onsa_syntax::ast::{Arg, CallKind, ExprId, ExprKind, Mode};

use super::check::Walker;
use super::flow::Run;
use super::place::place_of;
use super::walk::Pos;
use super::write::How;
use crate::Kind;
use crate::body::{BANG_ON_NO_INOUT_SELF, Target};
use crate::def::DefKind;
use crate::ty::{Ty, TyId};

/// What a parameter takes (memo 2.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Takes {
    /// A parameter of the mode, and its type when the walk reads it (a
    /// literal of a second-class type, [`Walker::argument`]).
    Param(Mode, Option<TyId>),
    /// An element of a variant or of `Some`, `Ok`, `Err`: consumed as an
    /// element of a literal is (§5.2).
    Element,
}

/// What a call takes: the mode of `self` of a method, and what each of the
/// arguments takes.
type Takings = (Option<Mode>, Vec<Takes>);

impl Walker<'_> {
    /// The call `e` of `callee` with `args`, of the form `kind`. Of a callee
    /// the walk does not know (§18.1: a value of the error type), the marks
    /// and the moves are not checked.
    pub(super) fn call(&mut self, r: &mut Run, e: ExprId, callee: ExprId, args: &[Arg], kind: CallKind) {
        let Some((recv, takes)) = self.takes(e, callee, args.len()) else {
            self.expr(r, callee, Pos::Read);
            return args.iter().for_each(|a| self.expr(r, a.expr, Pos::Unknown));
        };
        if takes.len() != args.len() {
            bug(Some(self.ast.expr(e).span), "a call whose arguments are not those of its callee")
        }
        self.bang(e, callee, kind, recv);
        let receiver = match (recv, &self.ast.expr(callee).kind) {
            (Some(m), &ExprKind::Field { base, .. }) => Some((base, m)),
            (Some(_), _) => bug(Some(self.ast.expr(callee).span), "a method call with no receiver"),
            (None, _) => None,
        };
        let (later, passed) = self.exclusive(receiver, args, &takes);
        let outer = std::mem::take(&mut self.inside.after_call);
        // The callee is evaluated before the arguments, out of the window of the call (§3.5, S-799).
        if receiver.is_none() {
            self.expr(r, callee, Pos::Read);
        }
        let start = self.inside.changes.len();
        self.inside.calls += 1;
        match receiver {
            Some((base, Mode::Move)) => {
                self.inside.direct = place_of(self.ast, self.names, base).is_some();
                self.expr(r, base, Pos::Extract)
            }
            Some((base, Mode::Inout)) => self.write_place(r, base, How::Bang),
            Some((base, m)) => self.expr(r, base, Pos::Arg(m)),
            None => {}
        }
        let span = self.ast.expr(e).span;
        self.lazily(r, e, |w, r| {
            for (a, t) in args.iter().zip(takes) {
                // The root of a place in it that is E0702's (a view, an element of a planar literal too).
                let at = w.ast.expr(a.expr).span;
                let excuse = later.iter().find(|(s, _)| at.start <= s.start && s.end <= at.end);
                let outer = replace(&mut w.inside.excuse, excuse.map(|&(_, l)| (l, span)));
                w.arg(r, a, t);
                w.inside.excuse = outer;
            }
        });
        self.inside.calls -= 1;
        self.changed_in_args(start, &passed);
        for (place, at) in replace(&mut self.inside.after_call, outer) {
            self.changed(r, &place, at);
        }
    }

    /// What the call `e` of `callee` takes (memo 2.5): of a function or a
    /// method, its declaration; of a function value, its type; of a builtin
    /// method, the mode of `self` the types stage chose, and borrows; of a
    /// constructor, elements (`n` the number of the arguments). `None` of
    /// any other callee.
    fn takes(&self, e: ExprId, callee: ExprId, n: usize) -> Option<Takings> {
        Some(match self.info.targets.get(&e)? {
            Target::Fn { def, .. } | Target::Method { def, .. } => {
                let DefKind::Fn(f) = &self.a.def(*def).kind else {
                    bug(Some(self.ast.expr(e).span), "a call of a function that is no function")
                };
                (f.self_mode, f.params.iter().map(|p| Takes::Param(p.mode, Some(p.ty))).collect())
            }
            Target::Value => match self.a.types.get(*self.info.expr_types.get(&callee)?) {
                Ty::Fn(f) => (None, f.params.iter().map(|&(m, t)| Takes::Param(m, Some(t))).collect()),
                _ => return None,
            },
            Target::BuiltinMethod { self_mode, .. } => (*self_mode, vec![Takes::Param(Mode::Borrow, None); n]),
            Target::Variant { .. } | Target::Prelude(_) => (None, vec![Takes::Element; n]),
            _ => return None,
        })
    }

    /// The `!` of the call `e` (§5.2): an `inout self` method is called with
    /// it (E0713), no other call (E0714); the candidate is the one fix.
    fn bang(&mut self, e: ExprId, callee: ExprId, kind: CallKind, recv: Option<Mode>) {
        let (span, at) = (self.ast.expr(e).span, self.ast.expr(callee).span.end);
        let d = match (kind == CallKind::Bang, recv == Some(Mode::Inout)) {
            (false, true) => {
                let message = "this method takes `inout self`: write `!` after its name (§5.2)";
                Diagnostic::new(Stage::Modes, Code::E0713, span, message)
                    .with_fix(Fix::insert("add `!`", span.file, at, "!"))
            }
            // `!` on a constructor (`Some!(1)`) is E0714 too: no `inout self` receiver (§5.2, S-791).
            (true, false) => {
                let fix = Fix::delete("remove `!`", Span::new(span.file, at, at + 1));
                Diagnostic::new(Stage::Modes, Code::E0714, span, BANG_ON_NO_INOUT_SELF).with_fix(fix)
            }
            _ => return,
        };
        self.report(d);
    }

    /// The argument `a` of a parameter that takes `t` (memo 2.5): its mark
    /// checked, and its walk at the position the parameter gives.
    fn arg(&mut self, r: &mut Run, a: &Arg, t: Takes) {
        let (e, mark) = (a.expr, (a.mode != Mode::Borrow).then_some(a.span.start));
        match (t, a.mode) {
            // `inout` on an element of a constructor (`Some(inout x)`): taken by value, E0703 (§5.2, S-792).
            (Takes::Param(Mode::Move, _) | Takes::Element, Mode::Inout) => {
                self.by_value(a, t);
                self.expr(r, e, Pos::Read)
            }
            (Takes::Param(Mode::Move, _), _) => self.consume(r, e, Pos::MoveArg, mark),
            (Takes::Element, Mode::Borrow) => self.expr(r, e, Pos::Value),
            // An element, as of a literal (§5.2, S-793): a Dup value's `move` is E0703 (S-795).
            (Takes::Element, _) => self.consume(r, e, Pos::Value, mark),
            (Takes::Param(m, ty), _) => {
                if a.mode != m {
                    self.mismatch(a, m);
                }
                match m {
                    // A binding derived from its place, passed in the call, is `exclusive`'s E0702 (S-796).
                    Mode::Inout => match self.planar_literal(e, ty) {
                        Some(parts) => parts.iter().for_each(|&x| self.write_place(r, x, How::Inout)),
                        None => self.write_place(r, e, How::Inout),
                    },
                    _ => self.argument(r, e, ty),
                }
            }
        }
    }

    /// The E0703 of the mark of `a` on a parameter of the mode `m` that is
    /// not it, `move` or `inout` written on a borrowed one or a mark `inout`
    /// wants (memo 2.5): the candidate removes, adds or replaces the mark.
    /// After it, the argument stands where it stood before (the position is
    /// the parameter's), so it leaves no error the call had not. A `move` on
    /// a value that is no place is R-198's.
    fn mismatch(&mut self, a: &Arg, m: Mode) {
        let (at, file, start) = (self.ast.expr(a.expr).span, a.span.file, a.span.start);
        if a.mode == Mode::Move && place_of(self.ast, self.names, a.expr).is_none() {
            return self.needs_a_place(a.expr, start, Pos::Arg(m));
        }
        let (message, fix) = match (m, a.mode) {
            (Mode::Borrow, Mode::Inout) => ("borrowed, not `inout`", self.unmark(file, start, "inout")),
            (Mode::Borrow, _) => ("borrowed, not `move`", self.unmark(file, start, "move")),
            (_, Mode::Borrow) => {
                ("`inout`; write `inout` before the argument", Fix::insert("add `inout`", file, at.start, "inout "))
            }
            _ => (
                "`inout`, not `move`",
                Fix::replace("replace `move` with `inout`", Span::new(file, start, start + 4), "inout"),
            ),
        };
        let d = Diagnostic::new(Stage::Modes, Code::E0703, at, format!("this parameter is {message} (§5.2)"));
        self.report(d.with_fix(fix));
    }

    /// The E0703 of `inout` on the argument `a` of a parameter that takes
    /// its value `t` (a `move` one, an element): with the candidate that
    /// removes it when the value is then copied or new (§5.2), not when it
    /// is an Affine place (moved with `move` or passed by another mode: no
    /// one fix).
    fn by_value(&mut self, a: &Arg, t: Takes) {
        let at = self.ast.expr(a.expr).span;
        let x = self.ast.without_parens(a.expr);
        let ty = self.info.expr_types.get(&x).copied();
        let dup = place_of(self.ast, self.names, x).is_none()
            || ty.is_some_and(|t| matches!(self.kind_of(t), Some(Kind::Copy | Kind::Shared)));
        let message = match t {
            Takes::Element => "a constructor takes its elements by value, not `inout` (§5.2)",
            _ => "this parameter is `move`: it takes the value, not `inout` (§5.2)",
        };
        let d = Diagnostic::new(Stage::Modes, Code::E0703, at, message);
        let fix = dup.then(|| self.unmark(a.span.file, a.span.start, "inout"));
        self.report(fix.into_iter().fold(d, Diagnostic::with_fix));
    }
}
