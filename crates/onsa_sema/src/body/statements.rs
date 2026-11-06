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
        if let Some(part) = self.info.diverging.stmt_part(self.ast, s) {
            return Err(self.never_carried_out(stmt.span, part));
        }
        match &stmt.kind {
            StmtKind::Let { pat, ty, init, .. } => {
                let it = self.check_init(*ty, *init, self.ast.pat(*pat).span, |ck| ck.annotation_of(*pat))?;
                self.bind_pat(*pat, it, true)?;
                Ok(())
            }
            StmtKind::Var { name, ty, init } => {
                let it = self.check_init(*ty, *init, name.span, |_| format!("the annotation of `{}`", name.name))?;
                let id = self.local_of(Origin::Var(s))?;
                self.bind_local(id, it, name.span)?;
                Ok(())
            }
            StmtKind::Assign { target, value } => {
                if !self.is_place(*target) {
                    let span = self.expr(*target).span;
                    let msg = "assignment needs a place: a `var`, or a field / element of one (§5.1)";
                    let mut d = Diagnostic::new(Stage::Types, Code::E0415, span, msg).with_found(self.src(span));
                    // `(a, b) = (b, a)` (S-180): the form with `let` and one assignment each,
                    // written out when each part is a place (no tuple) and it is one line.
                    if let ExprKind::Tuple(parts) = &self.expr(self.ast.without_parens(*target)).kind
                        && !parts.is_empty()
                    {
                        let names: Vec<String> = (0..parts.len()).map(|i| format!("v{i}")).collect();
                        let each =
                            parts.iter().zip(&names).map(|(&p, v)| format!("`{} = {v}`", self.src(self.expr(p).span)));
                        let (names, value) = (names.join(", "), self.src(self.expr(*value).span));
                        let each = each.collect::<Vec<_>>().join(", ");
                        let rule = format!(
                            "a tuple is not a place; take the value apart with `let ({names}) = {value}`, then assign each: {each} (§5.1)"
                        );
                        let words = "a tuple is not a place; take the value apart with `let`, then assign each part to its place (§5.1)";
                        let written = parts.iter().all(|&p| self.is_place(p)) && !rule.contains('\n');
                        d = d.with_rule(if written { rule } else { words.to_string() });
                    }
                    return Err(self.diag(d));
                }
                let tt = self.check_expr(*target, None)?;
                let why = format!("the assignment to `{}`", self.src(self.expr(*target).span));
                self.with_why(why, tt, |ck| ck.check_expr(*value, Some(tt)))?;
                Ok(())
            }
            StmtKind::For { pat, iter, body, .. } => {
                let elem = self.check_iter(*iter)?;
                self.bind_pat(*pat, elem, true)?;
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
                match value.or(self.joined_value(s)) {
                    Some(v) => {
                        self.with_why("the result of the function".into(), ret, |ck| ck.check_expr(v, Some(ret)))?;
                    }
                    None => self.bare_return(stmt.span, ret)?,
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

    /// The annotation and the initializer of the `let` or `var` that binds
    /// at `binding`, `why` naming the annotation. A whole initializer that
    /// diverges stops here, with the binding not yet read (§7, S-268:
    /// `let (a, b) = { return 1 }` is no E0420).
    fn check_init(
        &mut self,
        ty: Option<onsa_syntax::ast::TypeId>,
        init: ExprId,
        binding: Span,
        why: impl FnOnce(&Self) -> String,
    ) -> R<TyId> {
        let it = match ty {
            Some(t) => {
                let t = self.lower_type_expr(t)?;
                let why = why(self);
                self.with_why(why, t, |ck| ck.check_expr(init, Some(t)))?
            }
            None => self.check_expr(init, None)?,
        };
        if self.info.diverging.expr(init) {
            return Err(self.never_bound(binding, init));
        }
        Ok(it)
    }

    /// How the note of E0416 names an annotated `let` (`the annotation of `ys``).
    fn annotation_of(&self, pat: PatId) -> String {
        match &self.ast.pat(pat).kind {
            PatKind::Bind(id) => format!("the annotation of `{}`", id.name),
            _ => "the annotation of the `let`".to_string(),
        }
    }

    /// Element type of a `for` iteration.
    fn check_iter(&mut self, iter: ExprId) -> R<TyId> {
        let span = self.expr(iter).span;
        if let ExprKind::Range(r) = &self.expr(iter).kind {
            let r = *r;
            self.range_end_forms(&r)?;
            let lt = self.check_expr(r.lo, None)?;
            self.check_expr(r.hi, Some(lt))?;
            let s = self.shallow(lt);
            match self.ty(s) {
                Ty::Int(_) | Ty::Error => {}
                Ty::Param(_) if self.satisfies(s, Bound::Int) => {}
                Ty::Var(_) if self.infer.lit_of(&self.a.types, s) == Some(LitKind::Int) => {}
                Ty::Var(_) => return Err(self.known(lt, span, "range bound").unwrap_err()),
                _ => {
                    let shown = self.display(lt);
                    let msg = format!("the ends of a range are integers; found `{shown}` (§7)");
                    return Err(self.err(Code::E0401, span, msg));
                }
            }
            self.record(iter, lt);
            if r.end == RangeEnd::Included {
                // Until the loop that ends at the type's maximum (W8-03).
                return Err(self.closed_range_unsupported(&r, Stage::Types, Feature::InclusiveRangeFor));
            }
            return Ok(lt);
        }
        let it = self.check_expr(iter, None)?;
        // A literal variable is iterated as no type of its kind is (S-860).
        let it = self.known_shape(it, span, "iterated value")?;
        match self.ty(it) {
            Ty::Array(el, _) => Ok(el),
            Ty::Builtin(BuiltinTy::Span | BuiltinTy::Buf | BuiltinTy::Array, a) => Ok(a[0]),
            Ty::Builtin(BuiltinTy::Map | BuiltinTy::Set | BuiltinTy::Str, _) => {
                Err(self.unsupported(span, Feature::Iteration, &[]))
            }
            Ty::Error => Ok(it),
            _ => {
                let shown = self.described(it);
                Err(self.err(Code::E0401, span, format!("{shown} cannot be iterated (§7)")))
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
}
