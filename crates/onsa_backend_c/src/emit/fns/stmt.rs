//! The statements, and the expressions evaluated for their effects.

use super::text::{if_, while_};
use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    // -------------------------------------------------------- statements

    pub(super) fn stmt(&mut self, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                if Some(*l) == self.nrvo {
                    let ty = self.local_ty(*l);
                    return self.assign_into("(*out)", ty, e);
                }
                let ty = self.local_ty(*l);
                if self.def.hoisted.contains(l) {
                    let name = self.locals[l].lvalue.clone();
                    self.assign_into(&name, ty, e)?;
                    return Ok(());
                }
                let name = self.fresh_local(*l);
                self.locals.insert(*l, LocalC { lvalue: name.clone() });
                self.declare(&name, ty, e)?;
                if let Some(void) = self.unread_use(*l, &name) {
                    self.line(&void);
                }
                Ok(())
            }
            StmtKind::Assign(p, e) => {
                let ty = self.place_ty(p)?;
                let target = self.place(p)?;
                self.assign_into(&target, ty, e)
            }
            // `T* r = &g.a[…];` (`const` of an alias not written through, which
            // may name a borrowed parameter's place), and a use of it is `(*r)`,
            // as of an `inout` or a borrowed parameter.
            StmtKind::Alias(l, p) => {
                let target = self.place(p)?;
                let qualifier = match self.def.locals[l.0 as usize].kind {
                    onsa_core::LocalKind::Alias { write: true } => "",
                    onsa_core::LocalKind::Alias { write: false } => "const ",
                    onsa_core::LocalKind::Value => return Err(internal("an alias of a local of a value")),
                };
                let tn = self.cx.names.name(self.local_ty(*l));
                let name = self.fresh_local(*l);
                self.line(&format!("{qualifier}{tn}* {name} = &{target};"));
                if let Some(void) = self.unread_use(*l, &name) {
                    self.line(&void);
                }
                self.locals.insert(*l, LocalC { lvalue: format!("(*{name})") });
                Ok(())
            }
            StmtKind::Expr(e) => self.expr_stmt(e),
            StmtKind::If(c, a, b) => {
                let cs = self.expr(c)?;
                self.open(&format!("{} {{", if_(&cs)));
                self.block_into(a, None)?;
                if b.stmts.is_empty() && b.value.is_none() {
                    self.close("}");
                } else {
                    self.indent -= 1;
                    self.line("} else {");
                    self.indent += 1;
                    self.block_into(b, None)?;
                    self.close("}");
                }
                Ok(())
            }
            StmtKind::While(c, b) => {
                // The condition may need statements: evaluate it inside the loop.
                let mark = self.out.len();
                let saved_indent = self.indent;
                self.indent += 1;
                self.enter_loop(true);
                let cs = self.expr(c)?;
                let cond_stmts = self.out.split_off(mark);
                self.indent = saved_indent;
                if cond_stmts.is_empty() {
                    self.open(&format!("{} {{", while_(&cs)));
                } else {
                    self.open("for (;;) {");
                    self.out.push_str(&cond_stmts);
                    self.line(&format!("{} break;", if_(&format!("!({cs})"))));
                }
                self.loop_body(b)
            }
            StmtKind::ForRange { local, lo, hi, body, inclusive } => {
                let los = self.range_end(lo, true)?;
                let his = self.range_end(hi, !*inclusive)?;
                let ty = self.local_ty(*local);
                let tn = self.cx.names.name(ty);
                let i = self.fresh_local(*local);
                self.locals.insert(*local, LocalC { lvalue: i.clone() });
                let head = if *inclusive {
                    // `g` is 1 while `i` is below `hi`: compared before the
                    // step (where a `continue` goes), `i` stops at `hi`, the
                    // type's maximum too (S-257), and `lo > hi` runs none.
                    let (g, _) = self.temp(ty);
                    format!("{tn} {i} = {los}, {g} = ({tn})({i} <= {his}); {g}; {g} = ({tn})({i} != {his}), {i} += {g}")
                } else {
                    format!("{tn} {i} = {los}; {i} < {his}; {i}++")
                };
                self.open(&format!("for ({head}) {{"));
                self.enter_loop(false);
                self.loop_body(body)
            }
            StmtKind::Break => {
                self.leave_loop(true);
                Ok(())
            }
            StmtKind::Continue => {
                self.leave_loop(false);
                Ok(())
            }
            StmtKind::Return(None) => {
                self.line("return;");
                Ok(())
            }
            StmtKind::Return(Some(e)) => {
                if self.def.sret {
                    let ret = self.def.ret;
                    self.assign_into("(*out)", ret, e)?;
                    self.line("return;");
                } else if self.def.ret == Types::UNIT {
                    self.expr_stmt(e)?;
                    self.line("return;");
                } else {
                    let v = self.expr(e)?;
                    self.line(&format!("return {v};"));
                }
                Ok(())
            }
        }
    }

    /// An end of a `for`, evaluated once before it (§3.5, S-188, R-535): in
    /// a temporary, but a literal when `literal_kept` (the `hi` of `..=` is
    /// not: `i <= 255` of a `U8` is always true, a `-Wtype-limits` of GCC).
    fn range_end(&mut self, e: &Expr, literal_kept: bool) -> R<String> {
        let s = self.expr(e)?;
        if literal_kept && matches!(e.kind, ExprKind::Lit(_)) {
            return Ok(s);
        }
        let (t, tn) = self.temp(e.ty);
        self.line(&format!("{tn} {t} = {s};"));
        Ok(t)
    }

    /// A value of type `ty` where the code never comes (after a `panic` or
    /// a `return`): C still wants one.
    pub(super) fn never_read(&mut self, ty: CTy) -> String {
        if let Some(z) = zero_scalar(self.kind(ty)) {
            return z;
        }
        let (t, tn) = self.temp(ty);
        self.line(&format!("{tn} {t};"));
        self.line(&format!("memset(&{t}, 0, sizeof {t});"));
        t
    }

    pub(super) fn panic_stmt(&mut self, m: onsa_core::MsgId, span: Span) {
        let msg = self.cx.msg(&self.cx.m.messages[m.0 as usize]);
        let loc = self.loc(span);
        self.line(&format!("onsa_panic({msg}, {loc});"));
    }

    /// An expression evaluated for its effects only.
    pub(super) fn expr_stmt(&mut self, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                if def.sret {
                    let ret = def.ret;
                    let (t, tn) = self.temp(ret);
                    self.line(&format!("{tn} {t};"));
                    return self.assign_into(&t, ret, e);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                self.line(&format!("{name}({});", call.join(", ")));
                Ok(())
            }
            ExprKind::Prim { .. } => {
                let v = self.expr(e)?;
                if !Self::is_stable(&v) || e.ty != Types::UNIT {
                    self.line(&format!("(void)({v});"));
                }
                Ok(())
            }
            ExprKind::Panic { msg: m, .. } => {
                self.panic_stmt(*m, e.span);
                Ok(())
            }
            ExprKind::Block(b) => self.block_into(b, None),
            ExprKind::IfExpr { cond, then, else_ } => {
                let cs = self.expr(cond)?;
                self.open(&format!("{} {{", if_(&cs)));
                self.block_into(then, None)?;
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.block_into(else_, None)?;
                self.close("}");
                Ok(())
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let s = self.place_like(scrutinee)?;
                self.switch_into(&s, arms, default.as_ref(), None)
            }
            // A local read for nothing (a comparison Core folded, S-288) is still a use of it.
            ExprKind::Local(_) => {
                let v = self.expr(e)?;
                self.line(&format!("(void){v};"));
                Ok(())
            }
            ExprKind::Lit(_) | ExprKind::Const(_) | ExprKind::Zeroed => Ok(()),
            _ => {
                let v = self.expr(e)?;
                self.line(&format!("(void)({v});"));
                Ok(())
            }
        }
    }

    /// Argument strings for a call, following the callee's parameter modes.
    pub(super) fn call_args(&mut self, f: FnId, args: &[onsa_core::Arg]) -> R<Vec<String>> {
        let callee = self.cx.m.fn_(f);
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        let mut out = Vec::new();
        // Pointer-passed arguments must be places: evaluate them as such.
        let mut strs = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let p = &callee.params[i];
            let by_ptr = matches!(p.mode, Mode::Inout) && !matches!(self.kind(p.ty), TyKind::Span(_))
                || (matches!(p.mode, Mode::Borrow) && self.cx.m.tys.is_aggregate(p.ty));
            if by_ptr {
                let s = self.place_like(&a.expr)?;
                strs.push((s, true));
            } else {
                strs.push((String::new(), false));
            }
        }
        // Value arguments in order (place arguments are stable lvalues).
        let value_exprs: Vec<&Expr> = exprs.iter().enumerate().filter(|(i, _)| !strs[*i].1).map(|(_, e)| *e).collect();
        let values = self.operands(&value_exprs)?;
        let mut vi = 0;
        for (s, by_ptr) in strs {
            if by_ptr {
                out.push(format!("&{s}"));
            } else {
                out.push(values[vi].clone());
                vi += 1;
            }
        }
        Ok(out)
    }
}
