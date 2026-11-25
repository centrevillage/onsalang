//! The order of the names of a flow body (§11.2, S-116, S-117, S-267): a
//! value reads the names defined above it, and a later `let` only as
//! `^name` in the first argument of a delay, which an argument of a flow
//! or the condition of a modifier there does not hold (S-1130), nor a binding
//! a `^name` chooses (S-1245). The walk
//! reports E0801 and the E0020 of a `^` on a visible name at the name, in
//! the order of the text (R-286), and keeps where it is ([`Reach`]); the
//! types stage reads the records only. The
//! clock of `e at k` is looked up here too (§11.3, R-472).

use onsa_diag::hash::{HashMap, HashSet};
use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{CallKind, Clock, ExprId, ExprKind, Ident, MatchArm, StmtId};
use onsa_syntax::foreign::{self, RowId};

use super::exprs::binds;
use super::flow::{Outside, instance_form};
use super::paths::{Head, Place};
use super::{BindingId, BindingKind, Fail, Origin, PathRes, Stop, W, Walker};

/// Where a name of a flow body is read from, by the past values it may read.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum Reach {
    #[default]
    Now,
    /// In the first argument of a delay (`prev~`, `delay~`, `vdelay~`).
    Delay,
    /// There, in what chooses the arm of a `match~` with a binding an argument
    /// of a flow or a condition reads (S-1245): a candidate writes no `^`.
    Choose,
    /// In an argument of the flow called by the callee, in the first argument of a delay.
    FlowArg(ExprId),
    /// In the condition of the `.when~` or `.reset_if~` call, in the first argument of a delay.
    Cond(ExprId),
}

/// The note of a `match~` whose bindings a past value chooses (S-1245).
const CHOOSE_RULE: &str = "a flow takes no past value in its arguments, nor a modifier in its condition; take the `match~` into a `let` below what it reads past, and read that: `let t = match~ v { … }`, then `prev~(^t)`";

/// The state of the order of a flow body.
#[derive(Default)]
pub(super) struct Order {
    /// The first binding of the `let`s not defined yet: the `let`s are
    /// declared ahead in the order of the text (`walk_flow`).
    defined: u32,
    /// The end of the bindings of each `let`.
    ends: HashMap<StmtId, u32>,
    pub(super) reach: Reach,
    /// The bindings that hide a name (E0304, §5.1), which is read above
    /// them, to the local they hide (none: a name of the module).
    pub(super) clashes: HashMap<BindingId, Option<BindingId>>,
    /// The callee the walk is in (the head of an indexed one, `b` of
    /// `b[0](x)`), and whether its whole chain is the callee (called with a
    /// mark `~`, `!`, `.(`, or indexed), for [`Walker::candidate_reach`].
    pub(super) callee: Option<(ExprId, bool)>,
}

impl Walker<'_> {
    /// The bindings declared so far are of the `let`s up to `s` (`None`:
    /// before the first).
    pub(super) fn declared_let(&mut self, s: Option<StmtId>) {
        let end = self.out.bindings.len() as u32;
        match s {
            Some(s) => _ = self.order.ends.insert(s, end),
            None => self.order.defined = end,
        }
    }

    /// The `let` `s` is defined: the names after it read it.
    pub(super) fn defined_let(&mut self, s: StmtId) {
        let Some(&end) = self.order.ends.get(&s) else {
            onsa_diag::internal::bug(Some(self.ast.stmt(s).span), "a `let` of a flow body not declared ahead")
        };
        self.order.defined = end;
    }

    /// The `let` of the flow body defined below that `b` reads: `b`, or the
    /// one it hides (E0304), which a use above it reads (§5.1).
    fn below(&self, b: BindingId) -> Option<BindingId> {
        if let Some(&hidden) = self.order.clashes.get(&b) {
            return hidden.and_then(|h| self.below(h));
        }
        let kind = self.out.bindings[b.0 as usize].kind;
        (self.flow && b.0 >= self.order.defined && kind == BindingKind::FlowLet).then_some(b)
    }

    /// [`Self::below`] of the local of the record `r`.
    fn local_below(&self, r: &PathRes) -> Option<BindingId> {
        match *r {
            PathRes::Local(b) => self.below(b),
            _ => None,
        }
    }

    /// The reach where a candidate of the order may write `^` or `prev~(…)`
    /// at a name of the chain `nodes` (none: a hole of a string): none at a
    /// callee, where it would leave the error of the call (S-1108). The one
    /// place of that judgment.
    fn candidate_reach(&self, nodes: &[ExprId]) -> Option<Reach> {
        let callee = self
            .order
            .callee
            .is_some_and(|(c, marked)| nodes.first() == Some(&c) || (marked && nodes.last() == Some(&c)));
        (!nodes.is_empty() && !callee).then_some(self.order.reach)
    }

    /// Whether `e`, read in the first argument of a delay, reads a `^name` of a
    /// later `let` or a binding one chooses ([`super::BodyNames::past`], §11.2,
    /// S-1245). By the text, before the walk of `e`: a name of a flow body hides
    /// none (§5.1). Every `match` of a delay scans its parts once: of the text
    /// times the nesting (§2.5).
    pub(super) fn reads_past(&self, e: ExprId) -> bool {
        let visible = |name: &Ident| self.scopes.visible(&name.name);
        self.in_delay()
            && self.reads(e, |k| match k {
                ExprKind::Feedback(name) => visible(name).is_some_and(|b| self.below(b).is_some()),
                ExprKind::Path(p) => visible(&p.segments[0]).is_some_and(|b| self.out.past.contains(&b)),
                _ => false,
            })
    }

    fn in_delay(&self) -> bool {
        matches!(self.order.reach, Reach::Delay | Reach::Choose)
    }

    /// Whether `hit` of a part of `e`, not in the first argument of a delay in
    /// it, whose output that is.
    fn reads(&self, e: ExprId, hit: impl Fn(&ExprKind) -> bool) -> bool {
        let mut todo = vec![e];
        while let Some(x) = todo.pop() {
            if hit(&self.ast.expr(x).kind) {
                return true;
            }
            todo.extend(self.parts(x).into_iter().filter(|p| p.1 != Some(false)).map(|p| p.0));
        }
        false
    }

    /// The parts of `e`, each with whether it is an argument of a flow or a
    /// condition (`true`) or the first argument of a delay (`false`).
    fn parts(&self, e: ExprId) -> Vec<(ExprId, Option<bool>)> {
        let ExprKind::Call { callee, kind: CallKind::Flow, args } = &self.ast.expr(e).kind else {
            return self.ast.sub_exprs(e).into_iter().map(|x| (x, None)).collect();
        };
        let delay = matches!(instance_form(self.ast, *callee), Outside::Past);
        let args = args.iter().enumerate().map(|(k, a)| match delay {
            true => (a.expr, (k == 0).then_some(false)),
            false => (a.expr, Some(true)),
        });
        [(*callee, None)].into_iter().chain(args).collect()
    }

    /// Whether an argument of a flow or a condition in the bodies of `arms`, of
    /// a `match` or a `match~` in the first argument of a delay, reads a binding
    /// of theirs, or of a `match~` there whose choice reads one.
    pub(super) fn feeds_args(&self, arms: &[MatchArm]) -> bool {
        let bound = |arms: &'_ [MatchArm]| -> Vec<String> {
            arms.iter().flat_map(|a| binds(self.ast, a.pat)).map(|n| n.name.clone()).collect()
        };
        let mut names: HashSet<String> =
            if self.in_delay() { bound(arms).into_iter().collect() } else { return false };
        let mut todo: Vec<(ExprId, bool)> = arms.iter().map(|a| (a.body, false)).collect();
        while let Some((x, arg)) = todo.pop() {
            let of = |k: &ExprKind| matches!(k, ExprKind::Path(p) if names.contains(&p.segments[0].name));
            match &self.ast.expr(x).kind {
                k if arg && of(k) => return true,
                ExprKind::Match { scrutinee, arms, tilde: Some(_) } => {
                    if arms.iter().filter_map(|a| a.guard).chain([*scrutinee]).any(|x| self.reads(x, of)) {
                        names.extend(bound(arms));
                    }
                }
                _ => {}
            }
            todo.extend(self.parts(x).into_iter().map(|(y, p)| (y, p.unwrap_or(arg))));
        }
        false
    }

    /// The walk of `x`, what chooses the arm of a `match`, of one `fed`
    /// ([`Self::feeds_args`]) at [`Reach::Choose`].
    pub(super) fn chooser(&mut self, x: ExprId, fed: bool) -> W {
        let reach = self.order.reach;
        self.order.reach = if fed { Reach::Choose } else { reach };
        let walked = self.expr(x);
        self.order.reach = reach;
        walked
    }

    /// The E0801 of the binding `b` a `^name` chooses, read at `name` in an
    /// argument of a flow or the condition of a modifier (§11.2, S-1245), with
    /// no candidate: the note takes its `match~` into a `let`.
    fn chosen_by_past(&self, b: BindingId, name: &Ident) -> Option<Diagnostic> {
        let what = match self.order.reach {
            Reach::FlowArg(_) => "an argument of a flow",
            Reach::Cond(_) => "the condition of a modifier",
            Reach::Now | Reach::Delay | Reach::Choose => return None,
        };
        let binding = self.out.past.contains(&b).then(|| &self.out.bindings[b.0 as usize])?;
        let msg = format!(
            "`{}` is bound by a `match~` that reads a past value (`^`) to choose its arm, which {what} may not read (§11.2)",
            name.name
        );
        let d = Diagnostic::new(Stage::Names, Code::E0801, name.span, msg).with_found(name.name.clone());
        Some(d.with_note(binding.span, "bound here").with_rule(CHOOSE_RULE))
    }

    /// The note of a `^name` (`found`) read in an argument of the flow
    /// `callee` in a delay (§11.2).
    fn flow_arg_rule(&self, callee: ExprId, found: &str) -> String {
        let callee = self.src(self.ast.expr(callee).span);
        format!("a flow takes no `^` in its arguments; the delay is written inside them: `{callee}~(prev~({found}))`")
    }

    /// The note of a name read past in the condition of the modifier call
    /// `call` in a delay (§11.2, S-1130): the call taken into a `let`.
    fn cond_rule(&self, call: ExprId) -> String {
        let Some(m) = self.out.modifiers.get(&call) else {
            onsa_diag::internal::bug(Some(self.ast.expr(call).span), "a condition of no modifier call")
        };
        let (recv, name) = (self.src(self.ast.expr(m.receiver).span), self.src(m.name));
        format!(
            "a modifier takes no past value in its condition; take the call into a `let` and read that: `let l = {recv}.{name}~(…)`, then `prev~(^l)`"
        )
    }

    /// The span of the `let` that binds `b`, for the note.
    fn let_of(&self, b: BindingId) -> Span {
        match self.out.bindings[b.0 as usize].origin {
            Origin::Let(s) => self.ast.stmt(s).span,
            _ => self.out.bindings[b.0 as usize].span,
        }
    }

    /// The head of a chain resolved (`resolved`, of `segs` at `nodes`) in the
    /// order of §11.2: a later `let` read with no `^` is E0801 at its name,
    /// with the candidate that inserts `^` only in the first argument of a
    /// delay (S-117, [`Self::candidate_reach`]); out of it a note. A constant
    /// expression reads no local (§4.5, E0417).
    pub(super) fn in_order(
        &self,
        resolved: (Vec<PathRes>, Option<Fail>),
        segs: &[&Ident],
        nodes: &[ExprId],
    ) -> (Vec<PathRes>, Option<Fail>) {
        let head = segs[0];
        let later = match &resolved {
            (r, None) if !self.in_const => {
                if let Some(&PathRes::Local(b)) = r.first()
                    && let Some(d) = self.chosen_by_past(b, head)
                {
                    return (Vec::new(), Some(Fail::Report(d)));
                }
                r.first().and_then(|r| self.local_below(r))
            }
            _ => None,
        };
        let Some(b) = later else { return resolved };
        let name = &head.name;
        let msg = format!(
            "`{name}` is defined below; names are defined from the top, and a later `let` is read as `^{name}` in the first argument of `prev~` / `delay~` / `vdelay~` (§11.2)"
        );
        let d = Diagnostic::new(Stage::Names, Code::E0801, head.span, msg)
            .with_found(name.clone())
            .with_note(self.let_of(b), "defined here");
        let d = match (self.candidate_reach(nodes), self.order.reach) {
            (Some(Reach::Delay), _) => {
                d.with_fix(Fix::insert("read the past value with `^`", head.span.file, head.span.start, "^"))
            }
            (_, Reach::Now) => d.with_rule(format!(
                "names are defined from the top: move the `let` of `{name}` above this use; a feedback reads its past value with `prev~(^{name})`"
            )),
            (_, Reach::Choose) => d.with_rule(CHOOSE_RULE),
            (_, Reach::FlowArg(callee)) => d.with_rule(self.flow_arg_rule(callee, &format!("^{name}"))),
            (_, Reach::Cond(call)) => d.with_rule(self.cond_rule(call)),
            _ => d,
        };
        (Vec::new(), Some(Fail::Report(d)))
    }

    /// `^name` at `e` of a flow body (§11.2): a later `let` in the first
    /// argument of a delay is recorded; elsewhere E0801. A visible name is
    /// E0020 (S-116), a name not found E0302.
    pub(super) fn feedback(&mut self, e: ExprId, name: &Ident) -> W {
        let span = self.ast.expr(e).span;
        if let Some(b) = self.flow_name(&name.name) {
            let d = b.misplaced([name.span].into_iter(), self.text).with_found(self.src(span));
            return Err(self.fail(Fail::Report(d)));
        }
        let value = match self.head(&[name], &[e], Place::Value) {
            Head::Done((_, Some(f))) => return Err(self.fail(f)),
            Head::Done((r, None)) => match (r.first(), r.first().and_then(|r| self.local_below(r))) {
                (_, Some(b)) => return self.past(e, name, b),
                (Some(r), None) => self.called(r).is_value(),
                (None, None) => false,
            },
            Head::Item(entity, owner) => self.called(&PathRes::Item { entity, owner }).is_value(),
            Head::NotFound => return Err(self.fail(self.not_found(name))),
        };
        Err(self.caret_visible(span, name, value))
    }

    /// `^name` of the later `let` `b` at `e`: the value of the step before in
    /// the first argument of a delay, in a `par~` too, else E0801 (§11.2):
    /// out of a delay with the candidate `prev~(^name)`
    /// ([`Self::candidate_reach`]), in an argument of a flow with a note.
    fn past(&mut self, e: ExprId, name: &Ident, b: BindingId) -> W {
        let span = self.ast.expr(e).span;
        let found = self.src(span);
        if self.in_delay() {
            self.out.paths.insert(e, PathRes::Local(b));
            return Ok(());
        }
        let msg = format!(
            "`^{0}` reads the later `{0}`, which only the first argument of `prev~` / `delay~` / `vdelay~` may do (§11.2)",
            name.name
        );
        let d = Diagnostic::new(Stage::Names, Code::E0801, span, msg).with_note(self.let_of(b), "defined here");
        let not_a_delay = "`^` is not a delay: it reads a later `let` in the first argument of a delay";
        let d = match (self.order.reach, self.candidate_reach(&[e])) {
            (Reach::FlowArg(callee), _) => d.with_rule(self.flow_arg_rule(callee, &found)),
            (Reach::Cond(call), _) => d.with_rule(self.cond_rule(call)),
            (_, None) => d.with_rule(not_a_delay),
            _ => d.with_rule(not_a_delay).with_fix(Fix::new(
                "read the past value with `prev~`",
                vec![Edit::insert(span.file, span.start, "prev~("), Edit::insert(span.file, span.end, ")")],
            )),
        };
        Err(self.fail(Fail::Report(d.with_found(found))))
    }

    /// E0020 at `^name` (`span`) of a visible name (§11.2, S-116): of a value,
    /// the candidate takes the `^` off in the first argument of a delay, and
    /// out of it both `name` and `prev~(name)`, the intent not being one.
    // SPEC-GAP(S-1107): `^` on what is no value (a function `^g`) is this
    // E0020 with no candidate.
    fn caret_visible(&mut self, span: Span, name: &Ident, value: bool) -> Stop {
        let caret = Span { end: name.span.start, ..span };
        let fixes = match (value, self.order.reach) {
            (false, _) => Vec::new(),
            (true, Reach::Now) => vec![
                Fix::delete("read the value now", caret),
                Fix::new(
                    "read the past value",
                    vec![Edit::replace(caret, "prev~("), Edit::insert(span.file, span.end, ")")],
                ),
            ],
            (true, _) => vec![Fix::delete("remove `^`", caret)],
        };
        self.fail(Fail::Report(foreign::report(RowId::CaretVisible, self.text, span, fixes)))
    }

    /// Where the argument `k` of the call `e` of `callee`, read from `outer`,
    /// is read from: the first of a delay in a delay, the condition of a
    /// `.when~` / `.reset_if~` (not the N of `.down~` / `.up~`, a constant)
    /// and an argument of an instance of a flow out of it.
    pub(super) fn arg_reach(&self, (e, callee, k): (ExprId, ExprId, usize), outer: Reach) -> Reach {
        let cond = self.out.modifiers.get(&e).is_some_and(|m| m.modifier.ratio_op().is_none());
        match self.out.paths.get(&super::named(self.ast, callee)) {
            Some(PathRes::FlowBuiltin(crate::flow_names::FlowBuiltin::Delay(_))) if k == 0 => Reach::Delay,
            _ if outer != Reach::Now && cond => Reach::Cond(e),
            _ if outer != Reach::Now && self.out.instance_of.contains_key(&e) => Reach::FlowArg(callee),
            _ => outer,
        }
    }

    /// Whether the value `value` of the assignment `s` to `name` walks clean
    /// with `name` a `let` defined below (as the candidate `let` makes it).
    /// The walk is taken back, the state of the order included, whether it
    /// stopped or not.
    pub(super) fn walks_clean_as_let(&mut self, name: &Ident, s: StmtId, value: ExprId) -> bool {
        let (bindings, scopes) = (self.out.bindings.len(), self.out.scopes.len());
        let (callee, clocks, modifiers) = (self.order.callee, self.out.clocks.clone(), self.out.modifiers.clone());
        self.open_scope();
        let clean = self.declare(name, BindingKind::FlowLet, Origin::Let(s), None).is_ok() && self.walks_clean(value);
        self.close_scope();
        self.out.bindings.truncate(bindings);
        self.out.scopes.truncate(scopes);
        self.out.paths.retain(|_, r| !matches!(r, PathRes::Local(b) if b.0 as usize >= bindings));
        self.order.clashes.retain(|b, _| (b.0 as usize) < bindings);
        self.out.past.retain(|b| (b.0 as usize) < bindings);
        (self.order.callee, self.out.clocks, self.out.modifiers) = (callee, clocks, modifiers);
        clean
    }

    /// The clock of `e at k` of a flow body (§11.3): its name, of the
    /// namespace of the clocks (E0302 at it), recorded for the types stage;
    /// the N of a derived clock walked as a constant expression (§4.5,
    /// S-1077).
    pub(super) fn clock(&mut self, e: ExprId, clock: &Clock) -> W {
        match crate::clock::resolve_at(clock) {
            Ok(r) => _ = self.out.clocks.insert(e, r),
            Err(d) => return Err(self.fail(Fail::Report(d))),
        }
        clock.ratio.as_ref().map_or(Ok(()), |r| self.const_expr(r.n))
    }
}
