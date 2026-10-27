//! The walk of a body: every statement, expression and pattern once, in
//! the source order (a `let` reads its value before it binds, as the types
//! stage declares).

use std::collections::HashMap;

use onsa_diag::Stage;
use onsa_diag::unsupported::Feature;
use onsa_syntax::ast::{
    Block, CallKind, ExprId, ExprKind, Lit, MatchArm, Param, ParamName, PatId, PatKind, StmtId, StmtKind, StrLit,
    StrSeg, TypeId, UnOp,
};

use super::paths::Place;
use super::{BindingId, BindingKind, Fail, Origin, PatRes, PathRes, W, Walker};
use crate::flow_names::FlowBuiltin;

/// The choices open while a pattern is walked (§7): the names bound by the
/// branches before this one (`prev`) and by this branch so far (`cur`). A
/// name of an earlier branch is the same binding, with one more site.
#[derive(Default)]
pub(super) struct Choice {
    prev: HashMap<String, BindingId>,
    cur: HashMap<String, BindingId>,
}

impl Walker<'_> {
    /// The arms that bind, open a scope or make a record are here; every
    /// other expression walks its children in the order of
    /// [`onsa_syntax::ast::Ast::sub_exprs`] (R-91 (1)).
    pub(super) fn expr(&mut self, e: ExprId) -> W {
        let ast = self.ast;
        match &ast.expr(e).kind {
            ExprKind::Lit(Lit::Str(s)) => self.interp(e, s),
            ExprKind::Path(_) | ExprKind::Field { .. } => self.name_at(e, Place::Value),
            ExprKind::Call { callee, kind, args } => {
                let place = match kind {
                    CallKind::Value { .. } => Place::Value,
                    CallKind::Flow => Place::Instance,
                    _ => Place::Callee,
                };
                self.name_at(*callee, place)?;
                // The constant of a delay (`delay~(x, N)`, §11.4).
                let constant = match self.out.paths.get(callee) {
                    Some(PathRes::FlowBuiltin(FlowBuiltin::Delay(d))) => d.const_index(),
                    _ => None,
                };
                (0..).zip(args).try_for_each(|(k, a)| match Some(k) == constant {
                    true => self.const_expr(a.expr),
                    false => self.expr(a.expr),
                })
            }
            ExprKind::Repeat { elem, len } => {
                self.expr(*elem)?;
                self.const_expr(*len)
            }
            ExprKind::Cast { expr, ty } => {
                self.expr(*expr)?;
                self.type_sites.push(*ty);
                Ok(())
            }
            ExprKind::Feedback(name) => {
                if let Some(b) = self.lookup(&name.name) {
                    self.out.paths.insert(e, PathRes::Local(b));
                }
                Ok(())
            }
            // A type argument in an expression: the names stage gives it to
            // its item from W5-10; until then the body stops there (E0200
            // `Feature::TypeArgsInExpressions`, neither dropped nor read, R-81).
            ExprKind::TypeArgs { args, .. } => Err(self.type_args(args.span)),
            ExprKind::Struct { type_args, .. } if !type_args.is_empty() => Err(self.type_args(type_args[0].1.span)),
            ExprKind::Struct { path, .. } => {
                self.struct_lit(e, path)?;
                self.exprs(ast.sub_exprs(e))
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::Match { scrutinee, arms, .. } => self.match_arms(*scrutinee, arms),
            ExprKind::Closure { params, ret, body, .. } => self.closure(e, params, *ret, *body),
            // Forms this version does not have (E0200 of the types stage),
            // whose names it does not read.
            ExprKind::Handle { .. } | ExprKind::Unsafe(_) => Err(self.fail(Fail::Later)),
            ExprKind::Par { var, range, body } => {
                self.const_expr(range.lo)?;
                self.const_expr(range.hi)?;
                self.open_scope();
                self.declare(var, BindingKind::ParVar, Origin::Par(e), None);
                self.expr(*body)?;
                self.close_scope();
                Ok(())
            }
            _ => self.exprs(ast.sub_exprs(e)),
        }
    }

    pub(super) fn exprs(&mut self, es: impl IntoIterator<Item = ExprId>) -> W {
        es.into_iter().try_for_each(|e| self.expr(e))
    }

    /// A constant expression (§4.5: the length of `[x; n]`, a bound of
    /// `par`, the constant of a delay): the names of its leaves under
    /// parentheses, `-` and the operators (as `flow/consts.rs` reads them)
    /// are at [`Place::Const`], until W4-04 U5 makes the words of the errors
    /// of a path one.
    fn const_expr(&mut self, e: ExprId) -> W {
        match &self.ast.expr(e).kind {
            ExprKind::Paren(x) | ExprKind::Unary { op: UnOp::Neg, expr: x } => self.const_expr(*x),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.const_expr(*lhs)?;
                self.const_expr(*rhs)
            }
            ExprKind::Path(_) | ExprKind::Field { .. } => self.name_at(e, Place::Const),
            _ => self.expr(e),
        }
    }

    /// E0200 for the type arguments at `span` of an expression.
    fn type_args(&mut self, span: onsa_diag::Span) -> super::Stop {
        let d = Feature::TypeArgsInExpressions.diagnostic(Stage::Names, span, &[]).with_found(self.src(span));
        self.fail(Fail::Report(d))
    }

    /// The holes of a string literal (§2.4).
    fn interp(&mut self, e: ExprId, s: &StrLit) -> W {
        for (k, seg) in s.segments.iter().enumerate() {
            // Their errors are the types stage's until W4-04 U4.
            if let StrSeg::Interp(p) = seg
                && let (records, None) = self.resolve(&p.segments.iter().collect::<Vec<_>>(), Place::Value)
            {
                let records = (0..).zip(records).collect();
                self.out.interp.insert((e, k as u32), records);
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
        let ast = self.ast;
        match &ast.stmt(s).kind {
            StmtKind::Let { pat, init, ty, .. } => {
                self.type_sites.extend(ty);
                self.expr(*init)?;
                self.pattern(*pat, BindingKind::Let, Origin::Let(s))
            }
            StmtKind::Var { name, init, ty } => {
                self.type_sites.extend(ty);
                self.expr(*init)?;
                self.declare(name, BindingKind::Var, Origin::Var(s), None);
                Ok(())
            }
            // An assignment of a flow body is an error of the flow stage
            // (E0806) until W7-04 reports it here.
            StmtKind::Assign { .. } if self.flow => Err(self.fail(Fail::Later)),
            StmtKind::Assign { target, value } => {
                self.place(*target)?;
                self.expr(*value)
            }
            StmtKind::For { pat, moved, iter, body } => {
                self.expr(*iter)?;
                self.open_scope();
                self.pattern(*pat, BindingKind::For { moved: *moved }, Origin::For(s))?;
                self.expr(*body)?;
                self.close_scope();
                Ok(())
            }
            StmtKind::While { cond, body } => self.exprs([*cond, *body]),
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

    fn closure(&mut self, e: ExprId, params: &[Param], ret: Option<TypeId>, body: ExprId) -> W {
        self.type_sites.extend(params.iter().filter_map(|p| p.ty).chain(ret));
        self.open_closure(e);
        self.open_scope();
        for (k, p) in params.iter().enumerate() {
            // `self` is no parameter of an anonymous function (E0002, the types stage).
            if let ParamName::Ident(name) = &p.name {
                self.declare(
                    name,
                    BindingKind::ClosureParam(p.mode),
                    Origin::Closure { closure: e, param: k as u32 },
                    None,
                );
            }
        }
        self.expr(body)?;
        self.close_scope();
        self.close_closure();
        Ok(())
    }

    /// The names a pattern binds, in the innermost scope, and the items its
    /// paths name.
    pub(super) fn pattern(&mut self, p: PatId, kind: BindingKind, origin: Origin) -> W {
        let ast = self.ast;
        match &ast.pat(p).kind {
            PatKind::Bind(name) => {
                let b = match self.earlier_branch(&name.name) {
                    Some(b) => {
                        self.out.bindings[b.0 as usize].sites.push(p);
                        b
                    }
                    None => self.declare(name, kind, origin, Some(p)),
                };
                self.out.pats.insert(p, PatRes::Bind(b));
                if let Some(c) = self.choices.last_mut() {
                    c.cur.insert(name.name.clone(), b);
                }
            }
            PatKind::Tuple(ps) => return ps.iter().try_for_each(|&q| self.pattern(q, kind, origin)),
            PatKind::TupleStruct { path, elems } => {
                self.ctor(p, path)?;
                return elems.iter().try_for_each(|&q| self.pattern(q, kind, origin));
            }
            PatKind::Struct { path, fields, .. } => {
                self.ctor(p, path)?;
                return fields.iter().try_for_each(|(_, q)| self.pattern(*q, kind, origin));
            }
            PatKind::Path(path) => return self.ctor(p, path),
            PatKind::Or(alts) => {
                self.choices.push(Choice::default());
                for &alt in alts {
                    self.pattern(alt, kind, origin)?;
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

    /// The binding of `name` in an earlier branch of the open choices, unless
    /// this branch binds it already (two bindings of one name, E0304).
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
