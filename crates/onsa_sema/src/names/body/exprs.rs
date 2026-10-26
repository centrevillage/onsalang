//! The walk of a body: every statement, expression and pattern once, in
//! the source order (a `let` reads its value before it binds, as the types
//! stage declares).

use std::collections::HashMap;

use onsa_syntax::ast::{
    Block, ExprId, ExprKind, HandlerRef, Lit, MatchArm, Param, ParamName, PatId, PatKind, Path, StmtId, StmtKind,
    StrLit, StrSeg,
};

use super::{BindingId, BindingKind, Origin, PatRes, PathRes, Stop, W, Walker};

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
            ExprKind::Path(p) => {
                self.path(e, p);
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
            // `Feature::TypeArgsInExpressions`, reported by the types stage).
            ExprKind::TypeArgs { .. } => Err(Stop),
            ExprKind::Struct { type_args, .. } if !type_args.is_empty() => Err(Stop),
            ExprKind::Block(b) => self.block(b),
            ExprKind::Match { scrutinee, arms, .. } => self.match_arms(*scrutinee, arms),
            ExprKind::Closure { params, body, .. } => self.closure(e, params, *body),
            ExprKind::Handle { body, with } => {
                self.expr(*body)?;
                match with {
                    HandlerRef::Named { args, .. } => self.exprs(args.iter().map(|a| a.expr)),
                    // Its functions are items of their own.
                    HandlerRef::Inline { .. } => Ok(()),
                }
            }
            ExprKind::Par { var, range, body } => {
                self.exprs([range.lo, range.hi])?;
                self.open_scope();
                self.declare(var, BindingKind::ParVar, Origin::Par(e), None);
                self.expr(*body)?;
                self.close_scope();
                Ok(())
            }
            _ => self.exprs(ast.sub_exprs(e)),
        }
    }

    fn exprs(&mut self, es: impl IntoIterator<Item = ExprId>) -> W {
        es.into_iter().try_for_each(|e| self.expr(e))
    }

    /// A path whose head is a local: its record. Another head is resolved
    /// from W4-04 U2b.
    fn path(&mut self, e: ExprId, p: &Path) {
        if let Some(b) = self.lookup(&p.segments[0].name) {
            self.out.paths.insert(e, PathRes::Local(b));
        }
    }

    /// The holes of a string literal (§2.4) whose head is a local.
    fn interp(&mut self, e: ExprId, s: &StrLit) -> W {
        for (k, seg) in s.segments.iter().enumerate() {
            if let StrSeg::Interp(p) = seg
                && let Some(b) = self.lookup(&p.segments[0].name)
            {
                self.out.interp.insert((e, k as u32), vec![(0, PathRes::Local(b))]);
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

    fn stmt(&mut self, s: StmtId) -> W {
        let ast = self.ast;
        match &ast.stmt(s).kind {
            StmtKind::Let { pat, init, .. } => {
                self.expr(*init)?;
                self.pattern(*pat, BindingKind::Let, Origin::Let(s));
                Ok(())
            }
            StmtKind::Var { name, init, .. } => {
                self.expr(*init)?;
                self.declare(name, BindingKind::Var, Origin::Var(s), None);
                Ok(())
            }
            StmtKind::Assign { target, value } => {
                self.place(*target)?;
                self.expr(*value)
            }
            StmtKind::For { pat, moved, iter, body } => {
                self.expr(*iter)?;
                self.open_scope();
                self.pattern(*pat, BindingKind::For { moved: *moved }, Origin::For(s));
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
            self.pattern(arm.pat, BindingKind::MatchBind, Origin::Arm { scrutinee, arm: k as u32 });
            if let Some(g) = arm.guard {
                self.expr(g)?;
            }
            self.expr(arm.body)?;
            self.close_scope();
        }
        Ok(())
    }

    fn closure(&mut self, e: ExprId, params: &[Param], body: ExprId) -> W {
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

    /// The names a pattern binds, in the innermost scope. Its constructors
    /// are resolved from W4-04 U2b.
    fn pattern(&mut self, p: PatId, kind: BindingKind, origin: Origin) {
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
            PatKind::Tuple(ps) | PatKind::TupleStruct { elems: ps, .. } => {
                ps.iter().for_each(|&q| self.pattern(q, kind, origin));
            }
            PatKind::Struct { fields, .. } => fields.iter().for_each(|(_, q)| self.pattern(*q, kind, origin)),
            PatKind::Or(alts) => {
                self.choices.push(Choice::default());
                for &alt in alts {
                    self.pattern(alt, kind, origin);
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
            PatKind::Wild | PatKind::Lit(_) | PatKind::Neg(_) | PatKind::Path(_) => {}
        }
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
