//! The values written into a C lvalue: a declaration, an assignment, a block, an `if` and a `switch`.

use super::text::if_;
use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    /// `T name = e;` or `T name;` followed by construction in place.
    pub(super) fn declare(&mut self, name: &str, ty: CTy, e: &Expr) -> R<()> {
        let tn = self.cx.names.name(ty);
        if matches!(self.kind(ty), TyKind::Buf(_)) {
            return Err(unsupported(e.span, Feature::Buf, &[]));
        }
        if needs_construction(e, &self.cx.m.tys) {
            self.line(&format!("{tn} {name};"));
            self.assign_into(name, ty, e)
        } else {
            let v = self.expr(e)?;
            self.line(&format!("{tn} {name} = {v};"));
            Ok(())
        }
    }

    /// Store the value of `e` into the C lvalue `target` of type `ty`.
    pub(super) fn assign_into(&mut self, target: &str, ty: CTy, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Zeroed if self.cx.m.tys.is_aggregate(ty) => {
                let bulk = match self.kind(ty) {
                    TyKind::Struct(id) => self.cx.bulk.get(id).cloned(),
                    _ => None,
                };
                match bulk {
                    Some(b) if target == "(*out)" => {
                        // The bulk pointer is set by the caller; zero both regions.
                        self.open("{");
                        self.line(&format!("void* onsa_b = {target}.bulk;"));
                        self.line(&format!("memset(&{target}, 0, sizeof {target});"));
                        self.line(&format!("{target}.bulk = onsa_b;"));
                        self.line(&format!("{} memset(onsa_b, 0, sizeof({}));", if_("onsa_b"), b.struct_name));
                        self.close("}");
                    }
                    Some(_) => {
                        return Err(unsupported(e.span, Feature::BulkBuild, &[]));
                    }
                    None => self.line(&format!("memset(&{target}, 0, sizeof {target});")),
                }
                Ok(())
            }
            ExprKind::Call { fn_, args } if self.cx.m.fn_(*fn_).sret => {
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                let mut all = vec![format!("&{target}")];
                all.extend(call);
                self.line(&format!("{name}({});", all.join(", ")));
                Ok(())
            }
            ExprKind::IfExpr { cond, then, else_ } => {
                let cs = self.expr(cond)?;
                self.open(&format!("{} {{", if_(&cs)));
                self.block_into(then, Some((target, ty)))?;
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.block_into(else_, Some((target, ty)))?;
                self.close("}");
                Ok(())
            }
            ExprKind::Switch { scrutinee, arms, default } => {
                let s = self.place_like(scrutinee)?;
                self.switch_into(&s, arms, default.as_ref(), Some((target, ty)))
            }
            ExprKind::Block(b) => self.block_into(b, Some((target, ty))),
            ExprKind::Repeat { elem, n } if *n > 8 => {
                let v = self.materialize(elem)?;
                self.open("{");
                self.line("uint32_t onsa_i;");
                self.line(&format!("for (onsa_i = 0; onsa_i < {n}; onsa_i++) {target}.a[onsa_i] = {v};"));
                self.close("}");
                Ok(())
            }
            ExprKind::Panic { msg: m, .. } => {
                self.panic_stmt(*m, e.span);
                Ok(())
            }
            _ => {
                if let TyKind::Struct(id) = self.kind(ty)
                    && self.cx.bulk.contains_key(id)
                {
                    return Err(unsupported(e.span, Feature::BulkCopy, &[]));
                }
                let v = self.expr(e)?;
                self.line(&format!("{target} = {v};"));
                Ok(())
            }
        }
    }

    /// Emit a block's statements; its value goes to `target` (or is dropped).
    pub(super) fn block_into(&mut self, b: &Block, target: Option<(&str, CTy)>) -> R<()> {
        for s in &b.stmts {
            self.stmt(s)?;
        }
        if let Some(v) = &b.value
            && !b.diverges()
        {
            match target {
                Some((t, ty)) => self.assign_into(t, ty, v)?,
                None => self.expr_stmt(v)?,
            }
        }
        Ok(())
    }

    pub(super) fn switch_into(
        &mut self,
        s: &str,
        arms: &[(u32, Block)],
        default: Option<&Block>,
        target: Option<(&str, CTy)>,
    ) -> R<()> {
        // Every tag is covered when there is no default (Core's `Switch`): the
        // last arm is then the `else`, so a value it assigns is assigned on every
        // path (no `-Wsometimes-uninitialized`, R-145).
        let last_is_else = default.is_none();
        for (i, (tag, b)) in arms.iter().enumerate() {
            let last = i == arms.len() - 1;
            let head = if i == 0 && last && last_is_else {
                "{".to_string()
            } else if i == 0 {
                format!("{} {{", if_(&format!("{s}.tag == {tag}")))
            } else if last && last_is_else {
                "} else {".to_string()
            } else {
                format!("}} else {} {{", if_(&format!("{s}.tag == {tag}")))
            };
            if i == 0 {
                self.open(&head);
            } else {
                self.indent -= 1;
                self.line(&head);
                self.indent += 1;
            }
            self.block_into(b, target)?;
        }
        if let Some(d) = default {
            if arms.is_empty() {
                self.open("{");
            } else {
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
            }
            self.block_into(d, target)?;
        }
        self.close("}");
        Ok(())
    }
}

/// Expressions that are built in place rather than assigned from a C expression.
fn needs_construction(e: &Expr, tys: &Types) -> bool {
    match &e.kind {
        ExprKind::Zeroed => tys.is_aggregate(e.ty),
        ExprKind::Call { .. }
        | ExprKind::IfExpr { .. }
        | ExprKind::Switch { .. }
        | ExprKind::Block(_)
        | ExprKind::Panic { .. } => true,
        ExprKind::Repeat { n, .. } => *n > 8,
        _ => false,
    }
}
