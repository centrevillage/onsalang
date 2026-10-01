//! Argument modes, exclusivity, second-class values, borrow bindings and
//! Affine moves (T2-8; spec §5.2, §5.3, §5.4, §7, §12.2). Runs over the typed
//! tables of [`BodyInfo`] after type checking, for complete bodies only, and
//! stops at the first diagnostic of each body (P-01).

use std::collections::{HashMap, HashSet};

use onsa_diag::{Code, Diagnostic, Fix, Span};
use onsa_syntax::ast::{Arg, Ast, Block, CallKind, ExprId, ExprKind, Lit, Mode, StmtId, StmtKind, StrSeg};

use crate::body::{BodyInfo, LocalId, LocalKind, Target};
use crate::def::DefKind;
use crate::ty::{BuiltinTy, Ty, TyId};
use crate::{Analysis, DefId, Kind, Package, module_of_def};

/// Locals moved somewhere in each body (the `rt` pass uses it for drops).
pub(crate) type MovedLocals = HashMap<DefId, HashSet<LocalId>>;

pub(crate) fn check_all(pkg: &Package, a: &mut Analysis) -> MovedLocals {
    let mut moved_all = MovedLocals::new();
    let mut diags = Vec::new();
    let keys: Vec<DefId> = {
        let mut k: Vec<DefId> = a.bodies.keys().copied().collect();
        k.sort();
        k
    };
    for id in keys {
        let body = &a.bodies[&id];
        if !body.complete {
            continue;
        }
        let Some(module) = module_of_def(pkg, a, id) else { continue };
        let root = match &a.def(id).kind {
            DefKind::Fn(f) => f.body,
            DefKind::Test { body, .. } => Some(*body),
            DefKind::Const(c) => c.value,
            _ => None,
        };
        let Some(root) = root else { continue };
        let mut w = Walker {
            a,
            ast: &module.parsed.ast,
            text: &module.text,
            body,
            diag: None,
            state: State::default(),
            diverged: false,
            loops: Vec::new(),
            closure_depth: 0,
            moved_any: HashSet::new(),
        };
        w.closures();
        w.repeats();
        w.expr(root, Pos::Consume);
        if let Some(d) = w.diag.take() {
            diags.push(d);
        }
        moved_all.insert(id, w.moved_any);
    }
    a.diagnostics.extend(diags);
    moved_all
}

/// Where an expression stands, for second-class values (§5.3) and moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Pos {
    /// A borrowed call argument.
    Arg,
    /// An `inout` call argument (must be a mutable place).
    InoutArg,
    /// A `move` call argument.
    MoveArg,
    /// Element of an array literal that is itself an argument (planar spans).
    PlanarElem,
    /// Receiver of a borrowed method, base of an index, source of a `for`.
    Base,
    /// A position that takes the value: `let` / `var` init, return, struct
    /// field, literal element, assignment value, constructor argument.
    Consume,
    /// `match` scrutinee: moves an owned Affine value, borrows a borrowed one.
    Scrutinee,
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Proj {
    Field(u32),
    Index,
}

#[derive(Debug, Clone)]
struct Place {
    local: LocalId,
    proj: Vec<Proj>,
    span: Span,
}

impl Place {
    /// May the two places denote overlapping memory (§5.2)? Different fields
    /// never overlap; indices are never compared, so they always may.
    fn overlaps(&self, other: &Place) -> bool {
        if self.local != other.local {
            return false;
        }
        for (p, q) in self.proj.iter().zip(&other.proj) {
            match (p, q) {
                (Proj::Field(a), Proj::Field(b)) if a != b => return false,
                _ => {}
            }
        }
        true
    }
}

#[derive(Debug, Default, Clone)]
struct State {
    /// Moved locals with the span of the move.
    moved: HashMap<LocalId, Span>,
    /// Moves of locals declared outside the innermost loop, pending a
    /// reassignment before the next iteration (§5.2; E0704).
    pending: Vec<(LocalId, Span)>,
}

struct Walker<'a> {
    a: &'a Analysis,
    ast: &'a Ast,
    text: &'a str,
    body: &'a BodyInfo,
    diag: Option<Diagnostic>,
    state: State,
    diverged: bool,
    /// Start of the body of each enclosing loop (locals declared before it are "outer").
    loops: Vec<u32>,
    closure_depth: u32,
    moved_any: HashSet<LocalId>,
}

impl<'a> Walker<'a> {
    // ------------------------------------------------------------ helpers

    fn src(&self, span: Span) -> String {
        self.text[span.start as usize..span.end as usize].to_string()
    }

    fn report(&mut self, d: Diagnostic) {
        if self.diag.is_none() {
            self.diag = Some(d);
        }
    }

    fn err(&mut self, code: Code, span: Span, msg: impl Into<String>) {
        let found = self.src(span);
        self.report(Diagnostic::new(code, span, msg).with_found(found));
    }

    fn failed(&self) -> bool {
        self.diag.is_some()
    }

    fn span(&self, e: ExprId) -> Span {
        self.ast.expr(e).span
    }

    fn ty_of(&self, e: ExprId) -> Option<TyId> {
        self.body.expr_types.get(&e).copied()
    }

    fn kind_of_expr(&self, e: ExprId) -> Option<Kind> {
        self.ty_of(e).and_then(|t| self.a.kind_of(t))
    }

    fn local(&self, id: LocalId) -> &crate::body::LocalInfo {
        &self.body.locals[id.0 as usize]
    }

    /// Whether a local is a borrow (parameter, borrow binding, `for` without `move`).
    fn is_borrowed(&self, id: LocalId) -> bool {
        let l = self.local(id);
        l.borrow
            || matches!(
                l.kind,
                LocalKind::Param(Mode::Borrow)
                    | LocalKind::SelfParam(Mode::Borrow)
                    | LocalKind::ClosureParam(Mode::Borrow)
                    | LocalKind::For { moved: false }
            )
    }

    fn strip(&self, mut e: ExprId) -> ExprId {
        while let ExprKind::Paren(inner) = &self.ast.expr(e).kind {
            e = *inner;
        }
        e
    }

    /// The place an expression denotes (§5.1): a local with projections.
    fn place_of(&self, e: ExprId) -> Option<Place> {
        let e = self.strip(e);
        let span = self.span(e);
        match &self.ast.expr(e).kind {
            ExprKind::Path(_) => match self.body.targets.get(&e) {
                Some(Target::Local(id)) => Some(Place { local: *id, proj: Vec::new(), span }),
                _ => None,
            },
            ExprKind::Field { base, name } => {
                let mut p = self.place_of(*base)?;
                let idx = self.field_index(*base, &name.name).unwrap_or(u32::MAX);
                p.proj.push(Proj::Field(idx));
                p.span = span;
                Some(p)
            }
            ExprKind::TupleIndex { base, index, .. } => {
                let mut p = self.place_of(*base)?;
                p.proj.push(Proj::Field(*index));
                p.span = span;
                Some(p)
            }
            ExprKind::Index { base, .. } => {
                let mut p = self.place_of(*base)?;
                p.proj.push(Proj::Index);
                p.span = span;
                Some(p)
            }
            _ => None,
        }
    }

    fn field_index(&self, base: ExprId, name: &str) -> Option<u32> {
        let t = self.ty_of(base)?;
        match self.a.types.get(t) {
            Ty::Named(d, _) => match &self.a.def(*d).kind {
                DefKind::Struct(s) => match &s.fields {
                    crate::def::Fields::Named(fs) => fs.iter().position(|f| f.name == name).map(|i| i as u32),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Second-class types (§5.3): `Span[T]` and `[Span[T]; N]`.
    fn is_second_class(&self, t: TyId) -> bool {
        match self.a.types.get(t) {
            Ty::Builtin(BuiltinTy::Span, _) => true,
            Ty::Array(el, _) => matches!(self.a.types.get(*el), Ty::Builtin(BuiltinTy::Span, _)),
            _ => false,
        }
    }

    // ------------------------------------------------------------ prechecks

    /// E0712: closures capture by copy; `inout` parameters and Affine values cannot be captured.
    fn closures(&mut self) {
        let mut items: Vec<(&ExprId, &Vec<LocalId>)> = self.body.captures.iter().collect();
        items.sort_by_key(|(e, _)| self.span(**e).start);
        for (e, caps) in items {
            for &id in caps {
                let l = self.local(id);
                let reason = if matches!(
                    l.kind,
                    LocalKind::Param(Mode::Inout)
                        | LocalKind::SelfParam(Mode::Inout)
                        | LocalKind::ClosureParam(Mode::Inout)
                ) {
                    Some(format!("`{}` is an `inout` parameter", l.name))
                } else if self.a.kind_of(l.ty) == Some(Kind::Affine) {
                    Some(format!("`{}` is Affine and cannot be copied", l.name))
                } else {
                    None
                };
                if let Some(reason) = reason {
                    let span = self.span(*e);
                    let decl = l.span;
                    let d = Diagnostic::new(
                        Code::E0712,
                        span,
                        format!("a closure captures outer values by copy; {reason} (§5.3)"),
                    )
                    .with_found(self.src(span))
                    .with_note(decl, "captured value declared here");
                    self.report(d);
                    return;
                }
            }
        }
    }

    /// `[e; N]`: the element is copied N times, so it must be Dup (§2.4).
    fn repeats(&mut self) {
        for &e in &self.body.repeats {
            let ExprKind::Repeat { elem, .. } = &self.ast.expr(e).kind else { continue };
            if self.kind_of_expr(*elem) == Some(Kind::Affine) {
                let span = self.span(*elem);
                self.err(
                    Code::E0711,
                    span,
                    "`[e; N]` repeats a value; `e` must be Copy or Shared (Affine arrays use `array.from_fn`, §2.4)",
                );
                return;
            }
        }
    }

    // ------------------------------------------------------------ blocks and statements

    fn block(&mut self, b: &Block, pos: Pos) {
        for &s in &b.stmts {
            if self.failed() || self.diverged {
                return;
            }
            self.stmt(s);
        }
        if let Some(t) = b.tail
            && !self.failed()
            && !self.diverged
        {
            self.expr(t, pos);
        }
    }

    fn stmt(&mut self, s: StmtId) {
        let stmt = self.ast.stmt(s);
        match &stmt.kind {
            StmtKind::Let { init, .. } => self.expr(*init, Pos::Consume),
            StmtKind::Var { init, .. } => self.expr(*init, Pos::Consume),
            StmtKind::Assign { target, value } => {
                self.expr(*value, Pos::Consume);
                if self.failed() {
                    return;
                }
                // The target: its base places are read (E0704), the root must be mutable.
                let Some(place) = self.place_of(*target) else { return };
                if !place.proj.is_empty() {
                    self.check_moved(place.local, self.span(*target));
                }
                self.mutable_place(&place, "assign to");
                if place.proj.is_empty() {
                    self.reassigned(place.local);
                } else {
                    // Index expressions inside the target are read.
                    self.target_reads(*target);
                }
            }
            StmtKind::For { iter, body, .. } => {
                self.expr(*iter, Pos::Base);
                self.loop_body(*body);
            }
            StmtKind::While { cond, body } => {
                self.expr(*cond, Pos::Other);
                self.loop_body(*body);
            }
            StmtKind::Break | StmtKind::Continue => self.diverged = true,
            StmtKind::Return(v) => {
                if let Some(v) = v {
                    self.expr(*v, Pos::Consume);
                }
                self.diverged = true;
            }
            StmtKind::Assert(e) => self.expr(*e, Pos::Other),
            StmtKind::Expr(e) => self.expr(*e, Pos::Other),
        }
    }

    fn target_reads(&mut self, target: ExprId) {
        match &self.ast.expr(target).kind {
            ExprKind::Index { base, index } => {
                self.expr(*index, Pos::Other);
                self.target_reads(*base);
            }
            ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } | ExprKind::Paren(base) => {
                self.target_reads(*base)
            }
            _ => {}
        }
    }

    /// A loop body: moves of outer locals must be undone by a reassignment
    /// before the body ends (E0704, "moved in a previous iteration").
    fn loop_body(&mut self, body: ExprId) {
        let start = self.span(body).start;
        let saved_pending = std::mem::take(&mut self.state.pending);
        self.loops.push(start);
        let entry = self.state.clone();
        self.expr(body, Pos::Other);
        self.loops.pop();
        let diverged = std::mem::replace(&mut self.diverged, false);
        if self.failed() {
            return;
        }
        // Pending outer moves on a path that reaches the end of the body repeat next time.
        if !diverged && let Some(&(id, span)) = self.state.pending.first() {
            let name = self.local(id).name.clone();
            let d = Diagnostic::new(
                Code::E0704,
                span,
                format!(
                    "`{name}` is moved here in a previous iteration of the loop; assign it before the loop ends (§5.2)"
                ),
            )
            .with_found(self.src(span));
            self.report(d);
            return;
        }
        // After the loop, moves from the body stay moved (the body may have run).
        let mut moved = entry.moved;
        moved.extend(self.state.moved.drain());
        self.state.moved = moved;
        self.state.pending = saved_pending;
    }

    // ------------------------------------------------------------ expressions

    fn expr(&mut self, e: ExprId, pos: Pos) {
        if self.failed() {
            return;
        }
        let span = self.span(e);
        // Second-class values (§5.3) may only stand in argument-like positions.
        if let Some(t) = self.ty_of(e)
            && self.is_second_class(t)
            && !matches!(pos, Pos::Arg | Pos::InoutArg | Pos::PlanarElem | Pos::Base)
            && !matches!(self.ast.expr(e).kind, ExprKind::Paren(_))
        {
            let shown = self.a.display_type(t);
            self.err(
                Code::E0710,
                span,
                format!(
                    "`{shown}` is second-class: it can only be passed as an argument, not stored or returned (§5.3)"
                ),
            );
            return;
        }
        match &self.ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => {
                for seg in &s.segments {
                    if let StrSeg::Interp(p) = seg {
                        // Interpolated names are reads of locals.
                        if let Some(id) = self.lookup_name(&p.segments[0].name) {
                            self.check_moved(id, p.span);
                        }
                    }
                }
            }
            ExprKind::Lit(_) | ExprKind::Hole | ExprKind::Range { .. } => {}
            ExprKind::Path(_) => {
                if let Some(Target::Local(id)) = self.body.targets.get(&e) {
                    let id = *id;
                    self.check_moved(id, span);
                    self.consume(e, pos);
                }
            }
            ExprKind::Paren(inner) => self.expr(*inner, pos),
            ExprKind::Tuple(elems) | ExprKind::Array(elems) => {
                let inner = if pos == Pos::Arg || pos == Pos::InoutArg { Pos::PlanarElem } else { Pos::Consume };
                for &el in elems {
                    self.expr(el, inner);
                }
            }
            ExprKind::Repeat { elem, len } => {
                self.expr(*elem, Pos::Consume);
                self.expr(*len, Pos::Other);
            }
            ExprKind::Struct { fields, .. } => {
                for (_, f) in fields {
                    self.expr(*f, Pos::Consume);
                }
            }
            ExprKind::Block(b) => self.block(b, pos),
            ExprKind::If { cond, then, else_ } => {
                self.expr(*cond, Pos::Other);
                let before = self.state.clone();
                self.expr(*then, pos);
                let then_state = std::mem::replace(&mut self.state, before);
                let then_div = std::mem::replace(&mut self.diverged, false);
                if let Some(el) = else_ {
                    self.expr(*el, pos);
                }
                let else_div = std::mem::replace(&mut self.diverged, false);
                self.merge(then_state, then_div, else_div);
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(*scrutinee, Pos::Scrutinee);
                let before = self.state.clone();
                let mut acc: Option<(State, bool)> = None;
                for arm in arms {
                    self.state = before.clone();
                    self.diverged = false;
                    if let Some(g) = arm.guard {
                        self.expr(g, Pos::Other);
                    }
                    self.expr(arm.body, pos);
                    let st = std::mem::take(&mut self.state);
                    let div = std::mem::replace(&mut self.diverged, false);
                    acc = Some(match acc {
                        None => (st, div),
                        Some((mut prev, pdiv)) => {
                            if pdiv && !div {
                                (st, false)
                            } else if div {
                                (prev, pdiv)
                            } else {
                                prev.moved.extend(st.moved);
                                prev.pending.extend(st.pending);
                                (prev, false)
                            }
                        }
                    });
                }
                match acc {
                    Some((st, div)) => {
                        self.state = st;
                        self.diverged = div;
                    }
                    None => self.state = before,
                }
            }
            ExprKind::Closure { body, .. } => {
                // Captures are copies (E0712 checked up front); the body reads outer locals.
                if self.body.captures.get(&e).is_some_and(|c| !c.is_empty()) && pos != Pos::Arg {
                    self.err(
                        Code::E0710,
                        span,
                        "a closure that captures outer values is second-class: it can only be passed as an argument (§5.3)",
                    );
                    return;
                }
                let saved = self.state.clone();
                let saved_div = self.diverged;
                self.closure_depth += 1;
                self.expr(*body, Pos::Consume);
                self.closure_depth -= 1;
                self.state = saved;
                self.diverged = saved_div;
            }
            ExprKind::Handle { body, .. } | ExprKind::Unsafe(body) => self.expr(*body, pos),
            ExprKind::Par { from, to, body, .. } => {
                self.expr(*from, Pos::Other);
                self.expr(*to, Pos::Other);
                self.expr(*body, Pos::Other);
            }
            ExprKind::Binary { operands, .. } => {
                for &o in operands {
                    self.expr(o, Pos::Other);
                }
            }
            ExprKind::Cast { expr, .. } | ExprKind::Unary { expr, .. } | ExprKind::Try(expr) => {
                self.expr(*expr, Pos::Other)
            }
            ExprKind::Field { base, .. } | ExprKind::TupleIndex { base, .. } => {
                // Reading a field: the base is read; an Affine field in a consuming
                // position would be a partial move.
                self.expr(*base, Pos::Base);
                self.consume(e, pos);
            }
            ExprKind::Index { base, index } => {
                self.expr(*base, Pos::Base);
                self.expr(*index, Pos::Other);
                self.consume(e, pos);
            }
            ExprKind::Call { callee, kind, args } => self.call(e, *callee, *kind, args),
        }
    }

    fn merge(&mut self, then_state: State, then_div: bool, else_div: bool) {
        match (then_div, else_div) {
            (true, true) => {
                self.diverged = true;
            }
            (true, false) => {}
            (false, true) => {
                self.state = then_state;
            }
            (false, false) => {
                self.state.moved.extend(then_state.moved);
                self.state.pending.extend(then_state.pending);
            }
        }
    }

    fn lookup_name(&self, name: &str) -> Option<LocalId> {
        self.body.locals.iter().rposition(|l| l.name == name).map(|i| LocalId(i as u32))
    }

    /// E0704: a read of a moved local.
    fn check_moved(&mut self, id: LocalId, span: Span) {
        if let Some(&mv) = self.state.moved.get(&id) {
            let name = self.local(id).name.clone();
            let d = Diagnostic::new(Code::E0704, span, format!("`{name}` was moved and cannot be used again (§5.2)"))
                .with_found(self.src(span))
                .with_note(mv, "moved here");
            self.report(d);
        }
    }

    fn reassigned(&mut self, id: LocalId) {
        self.state.moved.remove(&id);
        self.state.pending.retain(|(l, _)| *l != id);
    }

    /// A place (local or projection) in a position that takes its value:
    /// Affine values move (whole locals only), Dup values are copied.
    fn consume(&mut self, e: ExprId, pos: Pos) {
        if !matches!(pos, Pos::Consume | Pos::MoveArg | Pos::Scrutinee) {
            return;
        }
        if self.kind_of_expr(e) != Some(Kind::Affine) {
            return;
        }
        let Some(place) = self.place_of(e) else { return };
        let span = self.span(e);
        let name = self.local(place.local).name.clone();
        if self.is_borrowed(place.local) {
            if pos == Pos::Scrutinee {
                return; // matching a borrowed value binds borrows (§7)
            }
            let what = if pos == Pos::MoveArg { "passed as `move`" } else { "moved out" };
            let d = Diagnostic::new(
                Code::E0711,
                span,
                format!(
                    "`{name}` is borrowed here and Affine, so it cannot be {what}; only owned values move (§5.2, §5.4)"
                ),
            )
            .with_found(self.src(span))
            .with_note(self.local(place.local).span, "borrowed binding declared here");
            self.report(d);
            return;
        }
        if !place.proj.is_empty() {
            let shown = self.src(span);
            self.err(
                Code::E0711,
                span,
                format!("cannot move `{shown}` out of `{name}`: Affine values move as a whole (partial moves are not allowed)"),
            );
            return;
        }
        if self.closure_depth > 0 {
            return; // captures are copies; Affine captures were rejected (E0712)
        }
        self.state.moved.insert(place.local, span);
        self.moved_any.insert(place.local);
        let decl = self.local(place.local).span.start;
        if let Some(&loop_start) = self.loops.last()
            && decl < loop_start
        {
            self.state.pending.push((place.local, span));
        }
    }

    /// The root of a place that is written (`inout`, `!` receiver, assignment)
    /// must be a `var`, an `inout` parameter, or `inout self` (E0701).
    fn mutable_place(&mut self, place: &Place, what: &str) {
        let l = self.local(place.local);
        if l.mutable {
            return;
        }
        let name = l.name.clone();
        let (reason, fix_var) = match l.kind {
            LocalKind::Let if !l.borrow => (format!("`{name}` is immutable (`let`); declare it with `var`"), true),
            LocalKind::Let | LocalKind::MatchBind => (format!("`{name}` is a borrow binding (§5.4), read-only"), false),
            LocalKind::Param(_) | LocalKind::ClosureParam(_) => {
                (format!("`{name}` is a borrowed parameter; declare it `inout {name}`"), false)
            }
            LocalKind::SelfParam(_) => ("`self` is borrowed; declare the method with `inout self`".to_string(), false),
            LocalKind::For { .. } => (format!("`{name}` is a `for` variable, read-only"), false),
            LocalKind::Var => unreachable!(),
        };
        let span = place.span;
        let mut d = Diagnostic::new(Code::E0701, span, format!("cannot {what} this place: {reason} (§5.2)"))
            .with_found(self.src(span))
            .with_note(l.span, "declared here");
        if fix_var {
            d = d.with_note(l.span, "change `let` to `var`");
        }
        self.report(d);
    }

    // ------------------------------------------------------------ calls

    fn call(&mut self, e: ExprId, callee: ExprId, kind: CallKind, args: &[Arg]) {
        let span = self.span(e);
        let target = self.body.targets.get(&e).cloned();
        // Receiver of a method call.
        let recv = match &self.ast.expr(callee).kind {
            ExprKind::Field { base, .. } => Some(*base),
            _ => None,
        };
        let mut inout_places: Vec<Place> = Vec::new();
        let mut borrow_places: Vec<Place> = Vec::new();
        // 1. The receiver.
        let param_modes: Vec<Mode> = match &target {
            Some(Target::Method { def, .. }) => {
                let DefKind::Fn(f) = &self.a.def(*def).kind else { return };
                let self_mode = f.self_mode.unwrap_or(Mode::Borrow);
                let name = self.a.def(*def).name.clone();
                let Some(r) = recv else { return };
                self.bang_check(e, callee, kind, self_mode == Mode::Inout, &name);
                if self.failed() {
                    return;
                }
                self.receiver(r, self_mode, &mut inout_places, &mut borrow_places);
                f.params.iter().map(|p| p.mode).collect()
            }
            Some(Target::BuiltinMethod { name, bang, .. }) => {
                let bang = *bang;
                let name = name.clone();
                if let Some(r) = recv
                    && self.ty_of(r).is_some()
                {
                    // `x.m(...)` on a builtin value (not `Buf.zeroed`-style associated functions).
                    self.bang_check(e, callee, kind, bang, &name);
                    if self.failed() {
                        return;
                    }
                    let mode = if bang { Mode::Inout } else { Mode::Borrow };
                    self.receiver(r, mode, &mut inout_places, &mut borrow_places);
                }
                args.iter().map(|_| Mode::Borrow).collect()
            }
            Some(Target::Fn { def, .. }) => {
                let DefKind::Fn(f) = &self.a.def(*def).kind else { return };
                f.params.iter().map(|p| p.mode).collect()
            }
            Some(Target::Value) => {
                self.expr(callee, Pos::Other);
                if self.failed() {
                    return;
                }
                match self.ty_of(callee).map(|t| self.a.types.get(t).clone()) {
                    Some(Ty::Fn(f)) => f.params.iter().map(|(m, _)| *m).collect(),
                    _ => args.iter().map(|_| Mode::Borrow).collect(),
                }
            }
            // Constructors take their arguments by value (§4.4): no mode keyword, Affine values move.
            Some(Target::Variant { .. }) | Some(Target::Prelude(_)) => {
                for arg in args {
                    if arg.mode == Mode::Inout {
                        let s = arg.span;
                        self.err(Code::E0703, s, "a constructor takes its argument by value; remove `inout`");
                        return;
                    }
                    self.expr(arg.expr, Pos::Consume);
                }
                return;
            }
            _ => return,
        };
        // 2. Arguments: mode must match (E0703), places collected for exclusivity.
        for (i, arg) in args.iter().enumerate() {
            let want = param_modes.get(i).copied().unwrap_or(Mode::Borrow);
            if arg.mode != want {
                let (found, fix) = self.mode_fix(arg, want);
                let msg = match want {
                    Mode::Inout => "this parameter is `inout`; write `inout` before the argument (§5.2)",
                    Mode::Move => "this parameter is `move`; write `move` before the argument (§5.2)",
                    Mode::Borrow => "this parameter is borrowed; the argument takes no mode keyword (§5.2)",
                };
                let d = Diagnostic::new(Code::E0703, arg.span, msg)
                    .with_found(found)
                    .with_fix(Fix::Replace { replace: fix });
                self.report(d);
                return;
            }
            match want {
                Mode::Borrow => {
                    self.expr(arg.expr, Pos::Arg);
                    if let Some(p) = self.place_of(arg.expr) {
                        borrow_places.push(p);
                    }
                }
                Mode::Inout => {
                    self.expr(arg.expr, Pos::InoutArg);
                    if self.failed() {
                        return;
                    }
                    let Some(p) = self.place_of(arg.expr) else {
                        let s = self.span(arg.expr);
                        self.err(
                            Code::E0701,
                            s,
                            "an `inout` argument must be a place (a `var`, an `inout` parameter, or a field / element of one), not a temporary (§5.2)",
                        );
                        return;
                    };
                    self.mutable_place(&p, "pass as `inout`");
                    inout_places.push(p);
                }
                Mode::Move => self.expr(arg.expr, Pos::MoveArg),
            }
            if self.failed() {
                return;
            }
        }
        // 3. Exclusivity (E0702).
        for (i, p) in inout_places.iter().enumerate() {
            for q in &inout_places[i + 1..] {
                if p.overlaps(q) {
                    let name = self.local(p.local).name.clone();
                    let d = Diagnostic::new(
                        Code::E0702,
                        q.span,
                        format!("`{name}` is passed as `inout` twice in one call; the two places may overlap (§5.2)"),
                    )
                    .with_found(self.src(q.span))
                    .with_note(p.span, "first `inout` here");
                    self.report(d);
                    return;
                }
            }
            for q in &borrow_places {
                if p.overlaps(q) {
                    let name = self.local(p.local).name.clone();
                    let d = Diagnostic::new(
                        Code::E0702,
                        q.span,
                        format!(
                            "`{name}` is passed as `inout` and borrowed in the same call; the places may overlap (§5.2)"
                        ),
                    )
                    .with_found(self.src(q.span))
                    .with_note(p.span, "`inout` here");
                    self.report(d);
                    return;
                }
            }
        }
        let _ = span;
    }

    fn receiver(&mut self, r: ExprId, mode: Mode, inout: &mut Vec<Place>, borrow: &mut Vec<Place>) {
        match mode {
            Mode::Borrow => {
                self.expr(r, Pos::Base);
                if let Some(p) = self.place_of(r) {
                    borrow.push(p);
                }
            }
            Mode::Inout => {
                self.expr(r, Pos::Base);
                if self.failed() {
                    return;
                }
                let Some(p) = self.place_of(r) else {
                    let s = self.span(r);
                    self.err(
                        Code::E0701,
                        s,
                        "the receiver of an `inout self` method must be a place, not a temporary (§5.2)",
                    );
                    return;
                };
                self.mutable_place(&p, "call an `inout self` method on");
                inout.push(p);
            }
            Mode::Move => self.expr(r, Pos::Consume),
        }
    }

    /// E0713 / E0714: `!` exactly when the receiver is `inout self` (§5.2).
    fn bang_check(&mut self, e: ExprId, callee: ExprId, kind: CallKind, needs_bang: bool, name: &str) {
        let has_bang = kind == CallKind::Bang;
        if has_bang == needs_bang {
            return;
        }
        let span = self.span(e);
        let ExprKind::Field { name: ident, .. } = &self.ast.expr(callee).kind else { return };
        let src = self.src(span);
        let at = (ident.span.end - span.start) as usize;
        if needs_bang {
            let fix = format!("{}!{}", &src[..at], &src[at..]);
            let d = Diagnostic::new(
                Code::E0713,
                span,
                format!("`{name}` takes `inout self`; the call is written `{name}!(...)` (§5.2)"),
            )
            .with_found(src)
            .with_fix(Fix::Replace { replace: fix });
            self.report(d);
        } else {
            let rest = src[at..].strip_prefix('!').unwrap_or(&src[at..]).to_string();
            let fix = format!("{}{}", &src[..at], rest);
            let d = Diagnostic::new(
                Code::E0714,
                span,
                format!("`{name}` does not take `inout self`; the call is written without `!` (§5.2)"),
            )
            .with_found(src)
            .with_fix(Fix::Replace { replace: fix });
            self.report(d);
        }
    }

    fn mode_fix(&self, arg: &Arg, want: Mode) -> (String, String) {
        let found = self.src(arg.span);
        let inner = self.src(self.span(arg.expr));
        let fix = match want {
            Mode::Inout => format!("inout {inner}"),
            Mode::Move => format!("move {inner}"),
            Mode::Borrow => inner,
        };
        (found, fix)
    }
}
