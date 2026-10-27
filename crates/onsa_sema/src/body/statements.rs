//! The statements: `let` and its annotation, the iteration of `for`, and
//! the places.

use super::*;

impl<'a> Checker<'a> {
    // ------------------------------------------------------------ statements

    /// One statement, then the deferred checks whose type it decided (§4.5, §4.7, S-235).
    pub(crate) fn check_stmt(&mut self, s: StmtId) -> R<()> {
        // A statement sets its own reasons (an annotation, an argument, `return`).
        self.without_why(|ck| if ck.flow.is_some() { ck.check_flow_stmt(s) } else { ck.check_stmt_inner(s) })?;
        self.check_deferred_now()
    }

    fn check_stmt_inner(&mut self, s: StmtId) -> R<()> {
        let stmt = self.ast.stmt(s);
        match &stmt.kind {
            StmtKind::Let { pat, ty, init, .. } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = match ann {
                    Some(t) => {
                        let why = self.annotation_of(*pat);
                        self.with_why(why, t, |ck| ck.check_expr(*init, ann))?
                    }
                    None => self.check_expr(*init, ann)?,
                };
                let borrow = self.is_borrow_source(*init);
                self.bind_pat(*pat, it, true, borrow)?;
                Ok(())
            }
            StmtKind::Var { name, ty, init } => {
                let ann = match ty {
                    Some(t) => Some(self.lower_type_expr(*t)?),
                    None => None,
                };
                let it = match ann {
                    Some(t) => {
                        self.with_why(format!("the annotation of `{}`", name.name), t, |ck| ck.check_expr(*init, ann))?
                    }
                    None => self.check_expr(*init, ann)?,
                };
                let id = self.local_of(Origin::Var(s))?;
                self.bind_local(id, it, false, name.span)?;
                Ok(())
            }
            StmtKind::Assign { target, value } => {
                if !self.is_place(*target) {
                    let span = self.expr(*target).span;
                    return Err(self.err(
                        Code::E0415,
                        span,
                        "assignment needs a place: a `var`, or a field / element of one (§5.1)",
                    ));
                }
                let tt = self.check_expr(*target, None)?;
                let why = format!("the assignment to `{}`", self.src(self.expr(*target).span));
                self.with_why(why, tt, |ck| ck.check_expr(*value, Some(tt)))?;
                Ok(())
            }
            StmtKind::For { pat, moved, iter, body } => {
                let (elem, borrow) = self.check_iter(*iter, *moved)?;
                self.bind_pat(*pat, elem, true, borrow)?;
                self.frames.last_mut().unwrap().loop_depth += 1;
                let unit = self.unit();
                let r = self.check_expr(*body, Some(unit));
                self.frames.last_mut().unwrap().loop_depth -= 1;
                r.map(|_| ())
            }
            StmtKind::While { cond, body } => {
                let bool_ = self.bool_();
                self.check_expr(*cond, Some(bool_))?;
                self.frames.last_mut().unwrap().loop_depth += 1;
                let unit = self.unit();
                let r = self.check_expr(*body, Some(unit));
                self.frames.last_mut().unwrap().loop_depth -= 1;
                r.map(|_| ())
            }
            StmtKind::Break | StmtKind::Continue => {
                if self.frames.last().unwrap().loop_depth == 0 {
                    let what = if matches!(stmt.kind, StmtKind::Break) { "break" } else { "continue" };
                    return Err(self.err(Code::E0002, stmt.span, format!("`{what}` outside a loop")));
                }
                Ok(())
            }
            StmtKind::Return(value) => {
                let ret = self.frames.last().unwrap().ret;
                match value {
                    Some(v) => {
                        self.with_why("the result of the function".into(), ret, |ck| ck.check_expr(*v, Some(ret)))?;
                    }
                    None => {
                        let unit = self.unit();
                        self.unify_at(stmt.span, unit, ret)?;
                    }
                }
                Ok(())
            }
            StmtKind::Assert(e) => {
                let bool_ = self.bool_();
                self.check_expr(*e, Some(bool_))?;
                Ok(())
            }
            StmtKind::Expr(e) => {
                self.check_expr(*e, None)?;
                Ok(())
            }
        }
    }

    /// How the note of E0416 names an annotated `let` (`the annotation of `ys``).
    fn annotation_of(&self, pat: PatId) -> String {
        match &self.ast.pat(pat).kind {
            PatKind::Bind(id) => format!("the annotation of `{}`", id.name),
            _ => "the annotation of the `let`".to_string(),
        }
    }

    /// Element type of a `for` iteration and whether the binding is a borrow.
    fn check_iter(&mut self, iter: ExprId, moved: bool) -> R<(TyId, bool)> {
        let span = self.expr(iter).span;
        if let ExprKind::Range(r) = &self.expr(iter).kind {
            let r = *r;
            self.range_end_forms(&r)?;
            let lt = self.check_expr(r.lo, None)?;
            self.check_expr(r.hi, Some(lt))?;
            let s = self.shallow(lt);
            match self.ty(s) {
                Ty::Int(_) | Ty::Error => {}
                Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => {}
                Ty::Var(_) => return Err(self.known(lt, span, "range bound").unwrap_err()),
                _ => {
                    let shown = self.display(lt);
                    let msg = format!("the ends of a range are integers; found `{shown}` (§7)");
                    return Err(self.err(Code::E0401, span, msg));
                }
            }
            self.record(iter, lt);
            if moved {
                return Err(self.err(Code::E0401, span, "`move` applies to collections, not ranges (§7)"));
            }
            if r.end == RangeEnd::Included {
                // Until the loop that ends at the type's maximum (W8-03).
                return Err(self.closed_range_unsupported(&r, Stage::Types, Feature::InclusiveRangeFor));
            }
            return Ok((lt, false));
        }
        let it = self.check_expr(iter, None)?;
        let it = self.known(it, span, "iterated value")?;
        match self.ty(it) {
            Ty::Array(el, _) => Ok((el, !moved)),
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, a) => Ok((a[0], !moved)),
            Ty::Builtin(BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Str, _) => {
                Err(self.unsupported(span, Feature::Iteration, &[]))
            }
            Ty::Error => Ok((it, true)),
            _ => {
                let shown = self.display(it);
                Err(self.err(Code::E0401, span, format!("`{shown}` cannot be iterated (§7)")))
            }
        }
    }

    /// A place expression (§5.1): a local, or a field / element / tuple element of a place
    /// ([`onsa_syntax::ast::Ast::place_root_node`], the one definition of the form),
    /// whose root the record has as a local (`self` included).
    pub(super) fn is_place(&self, e: ExprId) -> bool {
        let root = self.ast.place_root_node(e);
        root.is_some_and(|r| matches!(self.names.paths.get(&r), Some(PathRes::Local(_))))
    }

    /// §5.4: `let y = x`, `x.f`, `x[i]` where `x` is a borrowed parameter or a
    /// borrow binding derived from one.
    fn is_borrow_source(&self, e: ExprId) -> bool {
        match &self.expr(e).kind {
            ExprKind::Path(p) if p.segments.len() == 1 => match self.names.paths.get(&e) {
                Some(PathRes::Local(b)) => {
                    let l = &self.info.locals[b.0 as usize];
                    l.borrow || matches!(l.kind, LocalKind::Param(Mode::Borrow) | LocalKind::SelfParam(Mode::Borrow))
                }
                _ => false,
            },
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } | ExprKind::TupleIndex { base, .. } => {
                self.is_borrow_source(*base)
            }
            ExprKind::Paren(inner) => self.is_borrow_source(*inner),
            _ => false,
        }
    }
}
