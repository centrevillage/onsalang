//! The walk of a body: every statement, expression and pattern once, in
//! the source order (a `let` reads its value before it binds, as the types
//! stage declares).

use onsa_diag::hash::HashMap;
use onsa_diag::{Code, Diagnostic, Span, Stage};
use onsa_syntax::ast::{
    Ast, Block, Clock, ExprId, ExprKind, Ident, Lit, MatchArm, Param, ParamName, PatId, PatKind, StmtId, StmtKind,
    StrLit, StrSeg, TypeId, TypeKind,
};

use super::flow::{Outside, par_head};
use super::kinds::Want;
use super::paths::{PANIC, Place};
use super::{BindingId, BindingKind, Fail, Origin, PatRes, PathRes, Typed, W, Walker};
use crate::sig::Pos;

/// The choices open while a pattern is walked (§7): the names bound by the
/// branches before this one (`prev`) and by this branch so far (`cur`). A
/// name of an earlier branch is the same binding, with one more site.
#[derive(Default)]
pub(super) struct Choice {
    prev: HashMap<String, BindingId>,
    cur: HashMap<String, BindingId>,
}

impl Walker<'_> {
    /// The expression `e`, then whether it diverges, after its children (§7).
    pub(super) fn expr(&mut self, e: ExprId) -> W {
        self.expr_inner(e)?;
        let ast = self.ast;
        let panic = match &ast.expr(e).kind {
            ExprKind::Call { callee, .. } => {
                matches!(self.out.paths.get(callee), Some(PathRes::Item { entity, .. }) if *entity == PANIC)
            }
            _ => false,
        };
        self.out.diverging.note_expr(ast, e, panic);
        Ok(())
    }

    /// The arms that bind, open a scope or make a record are here; every
    /// other expression walks its children in the order of
    /// [`onsa_syntax::ast::Ast::sub_exprs`] (R-91 (1)).
    fn expr_inner(&mut self, e: ExprId) -> W {
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => self.interp(e, s),
            ExprKind::Path(_) | ExprKind::Field { .. } | ExprKind::TypeArgs { .. } => self.name_at(e, Place::Value),
            ExprKind::Call { callee, kind, args } => self.call(e, *callee, *kind, args),
            ExprKind::Index { .. } => self.index(e, super::calls::Square::Value),
            ExprKind::Repeat { elem, len } => {
                self.expr(*elem)?;
                self.const_expr(*len)
            }
            ExprKind::Cast { expr, ty } => {
                self.expr(*expr)?;
                self.typed([*ty], Pos::Bind);
                Ok(())
            }
            // What only a flow body holds (§11.1): E0821 at its start, after
            // the expression before a clock.
            ExprKind::At { expr, clock } if !self.flow => {
                self.expr(*expr)?;
                Err(self.outside(Outside::Clock(ast.expr(*expr).span.end), clock.span))
            }
            ExprKind::Feedback(_) if !self.flow => Err(self.outside(Outside::Past, ast.expr(e).span)),
            ExprKind::If { tilde: Some(t), .. } | ExprKind::Match { tilde: Some(t), .. } if !self.flow => {
                Err(self.outside(Outside::Branches, Span { end: t.end, ..ast.expr(e).span }))
            }
            // `par` and `par~` alike (S-745), up to the `~`.
            ExprKind::Par { tilde, .. } if !self.flow => {
                Err(self.outside(Outside::Par, par_head(ast.expr(e).span, *tilde)))
            }
            ExprKind::Par { tilde: None, .. } => Err(self.par_without_tilde(e)),
            // `^y`: a local, or a builtin name of the flow (S-720); any other
            // name is the flow stage's until W7-04.
            ExprKind::Feedback(name) => {
                if let Some(b) = self.lookup(name) {
                    self.out.paths.insert(e, PathRes::Local(b));
                } else if let Some(b) = self.flow_name(&name.name) {
                    let d = b.misplaced([name.span].into_iter(), self.text).with_found(self.src(ast.expr(e).span));
                    return Err(self.fail(Fail::Report(d)));
                }
                Ok(())
            }
            ExprKind::Hole => {
                let visible = self.visible();
                self.out.holes.insert(e, visible);
                Ok(())
            }
            ExprKind::Struct { path, rest, type_args, .. } => {
                self.struct_lit(e, path, type_args, rest.is_some())?;
                self.exprs(ast.sub_exprs(e))
            }
            // A block with statements in a flow body is the flow stage's
            // E0806 (`Self::stmt`); in a constant expression, no constant.
            ExprKind::Block(b) if self.flow && !b.stmts.is_empty() => self.later(),
            ExprKind::Block(b) => self.block(b),
            ExprKind::Match { scrutinee, arms, .. } => self.match_arms(*scrutinee, arms),
            // What a flow body cannot contain (§11.2) and the flow stage
            // reports as its E0806 until W7-04 reports it here (S-267).
            ExprKind::Closure { .. } | ExprKind::Try(_) | ExprKind::Move(_) if self.flow => self.later(),
            ExprKind::Closure { params, ret, ret_clock, body, effects } => {
                self.closure(e, params, (*ret, ret_clock.as_ref()), effects.is_some(), *body)
            }
            // Forms this version does not have (E0200 of the types stage),
            // whose names it does not read.
            ExprKind::Handle { .. } | ExprKind::Unsafe(_) => self.later(),
            ExprKind::Par { var, range, body, .. } => {
                let declare = |w: &mut Self| w.declare(var, BindingKind::ParVar, Origin::Par(e), None).map(drop);
                self.ahead(declare)?;
                self.const_expr(range.lo)?;
                self.const_expr(range.hi)?;
                self.open_scope();
                declare(self)?;
                self.expr(*body)?;
                self.close_scope();
                Ok(())
            }
            _ => self.exprs(ast.sub_exprs(e)),
        }
    }

    /// A form whose error is of a later stage, whose names the walk does not
    /// read: it stops the walk, but in a constant expression, where it is no
    /// constant (the E0417 or E0200 of the reader, `crate::constarg`) and the
    /// names after it are read.
    pub(super) fn later(&mut self) -> W {
        match self.in_const {
            true => Ok(()),
            false => Err(self.fail(Fail::Later)),
        }
    }

    pub(super) fn exprs(&mut self, es: impl IntoIterator<Item = ExprId>) -> W {
        es.into_iter().try_for_each(|e| self.expr(e))
    }

    /// A constant expression (§4.5: the length of `[x; n]`, a bound of
    /// `par`, the constant of a delay), walked as any expression; a name in
    /// it has no candidate that would leave it no constant (§18.1, S-236).
    /// A name held as an error in it stops the walk after it (§18.1, S-692),
    /// and the names after that name in it are read: the reader of the types
    /// stage tells an error of them from a use of the held one
    /// ([`super::BodyNames::held`]).
    pub(super) fn const_expr(&mut self, e: ExprId) -> W {
        let outer = std::mem::replace(&mut self.in_const, true);
        let r = self.expr(e);
        self.in_const = outer;
        r?;
        match !outer && std::mem::take(&mut self.const_held) {
            true => Err(self.fail(Fail::Held)),
            false => Ok(()),
        }
    }

    /// Keep the types `ts` written here at the place `pos` for `lower_types`
    /// ([`Self::site`]).
    fn typed(&mut self, ts: impl IntoIterator<Item = TypeId>, pos: Pos) {
        for t in ts {
            let site = self.site(Typed::Type(t, pos));
            self.type_sites.push(site);
        }
    }

    /// The type or the effect row `t` with the visible locals it names at
    /// the head of a path, of a type or of a constant expression in it:
    /// values, no types, constants or effects (§15.1, §4.5, S-729, S-738).
    pub(super) fn site(&self, t: Typed) -> super::Site {
        let mut names = Vec::new();
        match t {
            Typed::Type(t, _) => heads(self.ast, t, &mut names),
            Typed::Row(e) => {
                if let ExprKind::Closure { effects: Some(row), .. } = &self.ast.expr(e).kind {
                    row_heads(row, &mut names);
                }
            }
            Typed::Args(ref at) => at.args.args.iter().for_each(|&x| heads(self.ast, x, &mut names)),
        }
        (t, names.into_iter().filter(|n| self.sees_local(n)).map(|n| n.name.clone()).collect())
    }

    /// The holes of a string literal (§2.4): the path of each is a chain of
    /// names at the place of a value, resolved and reported as one of an
    /// expression; what follows its records is fields and tuple elements.
    fn interp(&mut self, e: ExprId, s: &StrLit) -> W {
        for (k, seg) in (0..).zip(&s.segments) {
            if let StrSeg::Interp(p) = seg {
                let (records, fail) =
                    self.resolve(&p.segments.iter().map(|s| &s.0).collect::<Vec<_>>(), &[], Place::Value);
                match fail {
                    Some(Fail::Report(d)) => {
                        let d = onsa_syntax::in_literal(d, self.ast.expr(e).span, self.text);
                        return Err(self.fail(Fail::Report(d)));
                    }
                    Some(f) => return Err(self.fail(f)),
                    None => {}
                }
                self.out.interp.insert((e, k), (0..).zip(records).collect());
            }
        }
        Ok(())
    }

    fn block(&mut self, b: &Block) -> W {
        self.open_scope();
        for &s in &b.stmts {
            self.stmt(s)?;
        }
        if let Some(t) = b.tail {
            self.expr(t)?;
        }
        self.close_scope();
        Ok(())
    }

    pub(super) fn stmt(&mut self, s: StmtId) -> W {
        // A flow body holds `let`s at its top level only, which `walk_flow`
        // walks itself; any other statement is the flow stage's E0806 until
        // W7-04 reports it here (§11.2, S-267).
        if self.flow {
            return Err(self.fail(Fail::Later));
        }
        let ast = self.ast;
        match &ast.stmt(s).kind {
            // The names before the value, as in the text (§18.1, R-289).
            StmtKind::Let { pat, init, ty, .. } => {
                self.ahead(|w| w.pattern(*pat, BindingKind::Let, Origin::Let(s)))?;
                self.typed(*ty, Pos::Bind);
                self.expr(*init)?;
                self.pattern(*pat, BindingKind::Let, Origin::Let(s))
            }
            StmtKind::Var { name, init, ty } => {
                let var = |w: &mut Self| w.declare(name, BindingKind::Var, Origin::Var(s), None).map(drop);
                self.ahead(var)?;
                self.typed(*ty, Pos::Bind);
                self.expr(*init)?;
                var(self)
            }
            StmtKind::Assign { target, value } => {
                self.place(*target)?;
                self.expr(*value)
            }
            StmtKind::For { pat, moved, iter, body } => {
                let kind = BindingKind::For { moved: moved.is_some() };
                self.ahead(|w| w.pattern(*pat, kind, Origin::For(s)))?;
                self.expr(*iter)?;
                self.open_scope();
                self.pattern(*pat, kind, Origin::For(s))?;
                self.expr(*body)?;
                self.close_scope();
                Ok(())
            }
            StmtKind::While { cond, body } => {
                self.exprs([*cond, *body])?;
                self.out.diverging.note_while(ast, s);
                Ok(())
            }
            StmtKind::Break | StmtKind::Continue | StmtKind::Return(None) => Ok(()),
            StmtKind::Return(Some(x)) | StmtKind::Assert(x) | StmtKind::Expr(x) => self.expr(*x),
        }
    }

    /// The target of an assignment: the root of a place
    /// ([`onsa_syntax::ast::Ast::place_root`]) is no read (§5.1, E0309), what
    /// else it reads (an index) is.
    fn place(&mut self, e: ExprId) -> W {
        self.expr(e)?;
        if let Some(root) = self.ast.place_root(e) {
            self.unread(root);
        }
        Ok(())
    }

    fn match_arms(&mut self, scrutinee: ExprId, arms: &[MatchArm]) -> W {
        self.expr(scrutinee)?;
        for (k, arm) in arms.iter().enumerate() {
            self.open_scope();
            self.pattern(arm.pat, BindingKind::MatchBind, Origin::Arm { scrutinee, arm: k as u32 })?;
            if let Some(g) = arm.guard {
                self.expr(g)?;
            }
            self.expr(arm.body)?;
            self.close_scope();
        }
        Ok(())
    }

    /// An anonymous function: each parameter, then its type, as in the text
    /// (§18.1, R-289), then the result type and the effect row (`row`). Its
    /// whole heading sees every parameter (§5.1, S-739). A clock of it is
    /// the E0821 of §11.3.
    fn closure(
        &mut self,
        e: ExprId,
        params: &[Param],
        ret: (Option<TypeId>, Option<&Clock>),
        row: bool,
        body: ExprId,
    ) -> W {
        self.open_closure(e);
        self.open_scope();
        // A parameter that is an E0304 is none (§18.1, S-675; `heading_locals`).
        self.heading = params
            .iter()
            .filter_map(|p| match &p.name {
                ParamName::Ident(n) if self.hidden(n, BindingKind::ClosureParam(p.mode)).is_none() => {
                    Some((n.name.clone(), n.span))
                }
                _ => None,
            })
            .collect();
        for (k, p) in params.iter().enumerate() {
            // `self` is no parameter of an anonymous function (E0002, the types stage).
            if let ParamName::Ident(name) = &p.name {
                let origin = Origin::Closure { closure: e, param: k as u32 };
                self.declare(name, BindingKind::ClosureParam(p.mode), origin, None)?;
            }
            self.typed(p.ty, Pos::Arg(p.mode));
            if let Some(c) = &p.clock {
                return Err(self.fail(Fail::Report(super::clock_after(self.ast, self.text, p.ty, c))));
            }
        }
        self.typed(ret.0, Pos::Other);
        if let Some(c) = ret.1 {
            return Err(self.fail(Fail::Report(super::clock_after(self.ast, self.text, ret.0, c))));
        }
        if row {
            let site = self.site(Typed::Row(e));
            self.type_sites.push(site);
        }
        self.heading.clear();
        self.expr(body)?;
        self.close_scope();
        self.close_closure();
        Ok(())
    }

    /// The names a pattern binds, in the innermost scope, and the items its
    /// paths name. A branch of a choice binds the names of its first branch
    /// (E0314 at the first that does not, [`other_names`]).
    pub(super) fn pattern(&mut self, p: PatId, kind: BindingKind, origin: Origin) -> W {
        let ast = self.ast;
        match &ast.pat(p).kind {
            PatKind::Bind(name) => {
                let b = match self.earlier_branch(&name.name) {
                    Some(b) => {
                        self.a.note_use(self.out.bindings[b.0 as usize].span, name.span);
                        self.out.bindings[b.0 as usize].sites.push(p);
                        b
                    }
                    None => self.declare(name, kind, origin, Some(p))?,
                };
                self.out.pats.insert(p, PatRes::Bind(b));
                if let Some(c) = self.choices.last_mut() {
                    c.cur.insert(name.name.clone(), b);
                }
            }
            PatKind::Tuple(ps) => return ps.iter().try_for_each(|&q| self.pattern(q, kind, origin)),
            PatKind::TupleStruct { path, elems } => {
                self.ctor(p, path, Want::Variant)?;
                return elems.iter().try_for_each(|&q| self.pattern(q, kind, origin));
            }
            PatKind::Struct { path, fields, .. } => {
                self.ctor(p, path, Want::Type)?;
                return fields.iter().try_for_each(|(_, q)| self.pattern(*q, kind, origin));
            }
            PatKind::Path(path) => return self.ctor(p, path, Want::VariantOrConstant),
            PatKind::Or(alts) => {
                let first = binds(ast, alts[0]);
                self.choices.push(Choice::default());
                for (k, &alt) in alts.iter().enumerate() {
                    let other = if k > 0 { other_names(ast, &first, alt) } else { None };
                    let waited = self.flow_stop.is_some();
                    let walked = self.pattern(alt, kind, origin);
                    if let Some(d) = other {
                        self.first_in_branch(d, walked.is_err(), waited)?;
                    }
                    walked?;
                    let c = self.choices.last_mut().expect("a choice");
                    let cur = std::mem::take(&mut c.cur);
                    c.prev.extend(cur);
                }
                // The names of a choice are bound by the branch it is in.
                let done = self.choices.pop().expect("a choice");
                if let Some(c) = self.choices.last_mut() {
                    c.cur.extend(done.prev);
                }
            }
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) => {}
        }
        Ok(())
    }

    /// Report the E0314 `d` of a branch, or the error the walk of the branch
    /// stopped at (`stopped`) or, in a `let` of a flow declared ahead, waits
    /// for (none waited before the branch, `waited`): the first in the order
    /// of §18.1 (start, end, code). An error from the start of the branch
    /// that ends in it (`Some(x) | Nope(_)`) or ends with it (`Some(x) |
    /// Non`) comes first; one after its start (`Some(x) | Some(Non)`) after.
    fn first_in_branch(&mut self, d: Diagnostic, stopped: bool, waited: bool) -> W {
        let at = match stopped {
            true => self.failure.as_mut(),
            false if self.prescan.is_some() && !waited => self.flow_stop.as_mut().map(|(_, why)| why),
            false => None,
        };
        match at {
            Some(Fail::Report(e)) if e.order_in_file() < d.order_in_file() => Ok(()),
            Some(why) => {
                *why = Fail::Report(d);
                Ok(())
            }
            None => self.fail_at_let(Fail::Report(d)),
        }
    }

    /// The binding of `name` in an earlier branch of the open choices, unless
    /// this branch binds it already (two bindings of one name, E0304, R-284).
    fn earlier_branch(&self, name: &str) -> Option<BindingId> {
        for c in self.choices.iter().rev() {
            if c.cur.contains_key(name) {
                return None;
            }
            if let Some(&b) = c.prev.get(name) {
                return Some(b);
            }
        }
        None
    }
}

/// The names at the head of the paths of the type `t`, of the constant
/// expressions (§4.5) and of the effect rows (§8.1) in it.
pub(crate) fn heads<'a>(ast: &'a Ast, t: TypeId, out: &mut Vec<&'a Ident>) {
    match &ast.ty(t).kind {
        TypeKind::Path { path, args } => {
            out.extend(path.segments.first());
            args.iter().for_each(|&x| heads(ast, x, out));
        }
        TypeKind::Array { elem, len } => {
            heads(ast, *elem, out);
            expr_heads(ast, *len, out);
        }
        TypeKind::Tuple(ts) => ts.iter().for_each(|&x| heads(ast, x, out)),
        TypeKind::Fn { params, ret, effects, .. } => {
            params.iter().map(|p| p.1).chain(*ret).for_each(|x| heads(ast, x, out));
            effects.iter().for_each(|r| row_heads(r, out));
        }
        TypeKind::ConstArg(e) => expr_heads(ast, *e, out),
        TypeKind::Unit | TypeKind::Error => {}
    }
}

fn row_heads<'a>(row: &'a onsa_syntax::ast::EffectRow, out: &mut Vec<&'a Ident>) {
    out.extend(row.effects.iter().filter_map(|p| p.segments.first()));
}

pub(super) fn expr_heads<'a>(ast: &'a Ast, e: ExprId, out: &mut Vec<&'a Ident>) {
    match &ast.expr(e).kind {
        ExprKind::Path(p) => out.extend(p.segments.first()),
        // The types of the list after a name (`Rg::[F32, n].CAP`, §4.5).
        ExprKind::TypeArgs { base, args } => {
            expr_heads(ast, *base, out);
            args.args.iter().for_each(|&x| heads(ast, x, out));
        }
        _ => ast.sub_exprs(e).into_iter().for_each(|x| expr_heads(ast, x, out)),
    }
}

/// The names the pattern `p` binds, in the order of the text; a choice in
/// it binds the names of its first branch (its other branches bind the
/// same, or are its E0314).
fn binds(ast: &Ast, p: PatId) -> Vec<&Ident> {
    match &ast.pat(p).kind {
        PatKind::Bind(name) => vec![name],
        PatKind::Tuple(ps) | PatKind::TupleStruct { elems: ps, .. } => ps.iter().flat_map(|&q| binds(ast, q)).collect(),
        PatKind::Struct { fields, .. } => fields.iter().flat_map(|(_, q)| binds(ast, *q)).collect(),
        PatKind::Or(alts) => binds(ast, alts[0]),
        PatKind::Path(_) | PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) => Vec::new(),
    }
}

/// The E0314 of the branch `alt` of a choice whose first branch binds
/// `first` (§7, S-318): every branch binds the same set of names. It names
/// one: the first of `first` that `alt` does not bind, else the first that
/// `alt` binds and the first branch does not. No candidate.
fn other_names(ast: &Ast, first: &[&Ident], alt: PatId) -> Option<Diagnostic> {
    let names = binds(ast, alt);
    let has = |ns: &[&Ident], n: &Ident| ns.iter().any(|m| m.name == n.name);
    let message = match first.iter().find(|n| !has(&names, n)) {
        Some(n) => format!("`{}` is bound by the first alternative of this choice and not by this one", n.name),
        None => {
            let n = names.iter().find(|n| !has(first, n))?;
            format!("`{}` is bound by this alternative and not by the first one of this choice", n.name)
        }
    };
    let message = format!("{message}; every alternative binds the same names (§7)");
    let d = Diagnostic::new(Stage::Names, Code::E0314, ast.pat(alt).span, message);
    Some(d.with_rule("bind the same names in every alternative, or write one arm for each alternative"))
}
