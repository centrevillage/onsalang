//! The signature of a function and its body put together, with the result built in `out` (NRVO, §12.7).

use super::text::{c_param_name, names_result};
use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    /// `(prototype, definition, the guarded twin)`: the twin, for a function
    /// that has a name in [`Cx::guarded_names`], calls it from a function that
    /// is never inlined ([`GUARDED_SUFFIX`]).
    pub fn emit(mut self) -> R<(String, String, Option<String>)> {
        let def = self.def;
        let Some(body) = &def.body else {
            return Err(unsupported(def.span, Feature::TargetFn, &[&def.name]));
        };
        // Signature.
        let name = self.cx.fn_name(self.f).to_string();
        let mut params = Vec::new();
        if def.sret {
            let rt = self.cx.names.name(def.ret);
            params.push(format!("{rt}* out"));
            self.used_names.insert("out".into());
        }
        // The locals the body reads (an assignment to a place is not a read of it).
        walk_block(body, &mut |e| {
            if let ExprKind::Local(l) = &e.kind {
                self.read.insert(*l);
            }
        });
        let mut pre = String::new();
        for p in &def.params {
            let cname = self.fresh_local(p.local);
            let tn = self.cx.names.name(p.ty);
            if matches!(self.kind(p.ty), TyKind::Buf(_)) {
                return Err(unsupported(def.span, Feature::Buf, &[]));
            }
            let (decl, lvalue) =
                match (p.mode, self.cx.m.tys.is_aggregate(p.ty), matches!(self.kind(p.ty), TyKind::Span(_))) {
                    (Mode::Inout, _, false) => (format!("{tn}* {cname}"), format!("(*{cname})")),
                    (Mode::Borrow, true, false) => (format!("const {tn}* {cname}"), format!("(*{cname})")),
                    _ => (format!("{tn} {cname}"), cname.clone()),
                };
            params.push(decl);
            if let Some(void) = self.unread_use(p.local, &cname) {
                let _ = writeln!(pre, "  {void}");
            }
            self.locals.insert(p.local, LocalC { lvalue });
        }
        let ret = if def.sret || def.ret == Types::UNIT { "void".to_string() } else { self.cx.names.name(def.ret) };
        let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
        // `@fp(relaxed)` (spec §15.5, §13.4, S-54, S-287): the function is relaxed
        // by the runtime's marks, the attribute of GCC on the declaration and the
        // pragma of Clang that opens the body.
        let relaxed = if def.fp_relaxed { "ONSA_FP_RELAXED_FN " } else { "" };
        let proto = format!("{relaxed}ONSA_INLINE {ret} {name}({plist})");
        let arg_names: Vec<String> = params.iter().map(|p| c_param_name(p).to_string()).collect();
        self.guarded = self.cx.guarded_names.get(&self.f).map(|twin| {
            format!(
                "static ONSA_NOINLINE ONSA_UNUSED {ret} {twin}({plist}) {{ {}{name}({}); }}",
                if ret == "void" { "" } else { "return " },
                arg_names.join(", ")
            )
        });
        if def.fp_relaxed {
            self.line("ONSA_FP_RELAXED_BODY");
        }

        // NRVO (§12.7): `let s = ...; ...; s` in an sret function builds `s` in `*out`.
        if def.sret
            && !has_return(def)
            && let Some(v) = &body.value
            && let ExprKind::Local(l) = &v.kind
            && body.stmts.iter().any(|s| matches!(&s.kind, StmtKind::Let(x, _) if x == l))
        {
            self.nrvo = Some(*l);
            self.locals.insert(*l, LocalC { lvalue: "(*out)".into() });
        }

        self.out.push_str(&pre);
        // A local whose storage a view out of its scope reads (R-481): declared
        // here, and its `let` assigns it.
        let nrvo = self.nrvo;
        for &l in def.hoisted.iter().filter(|&&l| Some(l) != nrvo) {
            let ty = self.local_ty(l);
            if matches!(self.kind(ty), TyKind::Buf(_)) {
                return Err(unsupported(def.span, Feature::Buf, &[]));
            }
            let name = self.fresh_local(l);
            let tn = self.cx.names.name(ty);
            self.line(&format!("{tn} {name};"));
            self.locals.insert(l, LocalC { lvalue: name });
        }
        let first_stmt = self.out.len();
        for s in &body.stmts {
            self.stmt(s)?;
        }
        if let Some(v) = &body.value {
            if def.sret {
                if self.nrvo.is_none() {
                    self.assign_into("(*out)", def.ret, v)?;
                }
            } else if def.ret == Types::UNIT {
                self.expr_stmt(v)?;
            } else {
                let e = self.expr(v)?;
                self.line(&format!("return {e};"));
            }
        }
        // A body that diverges on every path never writes the result, and a
        // `#pragma` of `@fp(relaxed)` must stay first.
        if def.sret && !names_result(&self.out) {
            self.out.insert_str(first_stmt, "  (void)out;\n");
        }
        let mut body_text = String::new();
        let _ = writeln!(body_text, "{proto} {{");
        body_text.push_str(&self.out);
        let _ = writeln!(body_text, "}}");
        Ok((proto, body_text, self.guarded.take()))
    }
}
