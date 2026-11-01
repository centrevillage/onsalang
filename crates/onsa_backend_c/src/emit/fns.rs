//! The functions of the unit: the body of each, one [`FnEmitter`] for each,
//! and the helpers of the C text they write.

use super::*;

// ------------------------------------------------------------ functions

/// How a local is reached from C.
#[derive(Debug, Clone)]
struct LocalC {
    /// A complete C lvalue (`x`, `(*s)`, `(*out)`).
    lvalue: String,
}

pub(crate) struct FnEmitter<'a, 'm> {
    cx: &'a mut Cx<'m>,
    f: FnId,
    def: &'m FnDef,
    out: String,
    indent: usize,
    locals: HashMap<LocalId, LocalC>,
    used_names: HashSet<String>,
    temps: u32,
    /// The local returned through `out` without a copy (§12.7 NRVO).
    nrvo: Option<LocalId>,
    /// The definition of the guarded twin, once the signature is known.
    guarded: Option<String>,
    /// The locals the body reads ([`Self::unread_use`]).
    read: HashSet<LocalId>,
}

impl<'a, 'm> FnEmitter<'a, 'm> {
    pub fn new(cx: &'a mut Cx<'m>, f: FnId) -> Self {
        let def = cx.m.fn_(f);
        FnEmitter {
            cx,
            f,
            def,
            out: String::new(),
            indent: 1,
            locals: HashMap::new(),
            used_names: HashSet::new(),
            temps: 0,
            nrvo: None,
            guarded: None,
            read: HashSet::new(),
        }
    }

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
            let rt = self.cx.names.name(&def.ret);
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
            let tn = self.cx.names.name(&p.ty);
            if matches!(p.ty, Ty::Buf(_)) {
                return Err(unsupported(def.span, Feature::Buf, &[]));
            }
            let (decl, lvalue) = match (p.mode, p.ty.is_aggregate(), matches!(p.ty, Ty::Span(_))) {
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
        let ret = if def.sret || def.ret == Ty::Unit { "void".to_string() } else { self.cx.names.name(&def.ret) };
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
        for s in &body.stmts {
            self.stmt(s)?;
        }
        if let Some(v) = &body.value {
            if def.sret {
                if self.nrvo.is_none() {
                    self.assign_into("(*out)", &def.ret, v)?;
                }
            } else if def.ret == Ty::Unit {
                self.expr_stmt(v)?;
            } else {
                let e = self.expr(v)?;
                self.line(&format!("return {e};"));
            }
        }
        let mut body_text = String::new();
        let _ = writeln!(body_text, "{proto} {{");
        body_text.push_str(&self.out);
        let _ = writeln!(body_text, "}}");
        Ok((proto, body_text, self.guarded.take()))
    }

    // -------------------------------------------------------- helpers

    fn line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn open(&mut self, s: &str) {
        self.line(s);
        self.indent += 1;
    }

    fn close(&mut self, s: &str) {
        self.indent -= 1;
        self.line(s);
    }

    /// `(void)x;` for a parameter or a binding the body never reads (S-288:
    /// an unused `let`, a pattern's binding, a `var` only assigned, a local
    /// whose comparisons Core folded), so the C has no `-Wunused-*`. The one
    /// place of that decision.
    fn unread_use(&self, l: LocalId, cname: &str) -> Option<String> {
        (!self.read.contains(&l)).then(|| format!("(void){cname};"))
    }

    fn fresh_local(&mut self, l: LocalId) -> String {
        let base = ident(&self.def.locals[l.0 as usize].name);
        let mut name = base.clone();
        if self.used_names.contains(&name) {
            name = format!("{base}_{}", l.0);
        }
        self.used_names.insert(name.clone());
        name
    }

    fn temp(&mut self, ty: &Ty) -> (String, String) {
        self.temps += 1;
        let name = format!("onsa_t{}", self.temps);
        let tn = self.cx.names.name(ty);
        (name, tn)
    }

    fn loc(&self, span: Span) -> String {
        self.cx.loc(span)
    }

    fn local_ty(&self, l: LocalId) -> Ty {
        self.def.locals[l.0 as usize].ty.clone()
    }

    fn place_ty(&self, p: &Place) -> R<Ty> {
        Ok(match p {
            Place::Local(l) => self.local_ty(*l),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                field_ty(self.cx, &bt, *i)?
            }
            Place::Index(b, _, _) => match self.place_ty(b)? {
                Ty::Array(e, _) | Ty::Span(e) | Ty::Buf(e) => *e,
                _ => return Err(internal("index of a non-sequence place")),
            },
        })
    }

    /// Render a field access on a C lvalue / rvalue of type `base_ty`.
    fn field_access(&mut self, base: &str, base_ty: &Ty, index: u32) -> R<String> {
        match base_ty {
            Ty::Tuple(_) => Ok(format!("{}f{index}", dot(base))),
            Ty::Struct(id) => {
                let (fname, _) =
                    self.cx.fields(*id).get(index as usize).cloned().ok_or_else(|| internal("field index"))?;
                if let Some(b) = self.cx.bulk.get(id).cloned()
                    && b.fields.contains(&index)
                {
                    return Ok(format!("(*({}*){}bulk).{}", b.struct_name, dot(base), ident(&fname)));
                }
                Ok(format!("{}{}", dot(base), ident(&fname)))
            }
            _ => Err(internal("field of a non-record")),
        }
    }

    fn place(&mut self, p: &Place) -> R<String> {
        match p {
            Place::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            Place::Field(b, i) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                self.field_access(&bs, &bt, *i)
            }
            Place::Index(b, i, _) => {
                let bt = self.place_ty(b)?;
                let bs = self.place(b)?;
                let idx = self.expr(i)?;
                self.index_access(&bs, &bt, &idx, i.span)
            }
        }
    }

    fn index_access(&mut self, base: &str, base_ty: &Ty, idx: &str, span: Span) -> R<String> {
        let loc = self.loc(span);
        match base_ty {
            Ty::Array(_, n) => Ok(format!("{base}.a[onsa_idx({idx}, UINT32_C({n}), {loc})]")),
            Ty::Span(_) => Ok(format!("{base}.ptr[onsa_idx({idx}, {base}.len, {loc})]")),
            Ty::Buf(_) => Err(unsupported(span, Feature::Buf, &[])),
            _ => Err(internal("index of a non-sequence")),
        }
    }

    /// A stable C expression: unaffected by later side effects.
    fn is_stable(s: &str) -> bool {
        s.starts_with("onsa_t")
            || s.starts_with("INT")
            || s.starts_with("UINT")
            || s.starts_with("((int")
            || s.starts_with("((uint")
            || s.starts_with(|c: char| c.is_ascii_digit())
            || s == "true"
            || s == "false"
            || s == "NAN"
            || s == "INFINITY"
            || s == "(-INFINITY)"
    }

    /// Evaluate operands in order; earlier operands are saved in temporaries
    /// as soon as a later operand needs statements.
    fn operands(&mut self, es: &[&Expr]) -> R<Vec<String>> {
        let mut strs: Vec<String> = Vec::new();
        for e in es {
            let mark = self.out.len();
            let s = self.expr(e)?;
            if self.out.len() != mark {
                // Statements were emitted: snapshot the earlier operands before them.
                let mut decls = String::new();
                for (j, prev) in strs.iter_mut().enumerate() {
                    if !Self::is_stable(prev) {
                        let (t, tn) = self.temp(&es[j].ty);
                        for _ in 0..self.indent {
                            decls.push_str("  ");
                        }
                        let _ = writeln!(decls, "{tn} {t} = {prev};");
                        *prev = t;
                    }
                }
                self.out.insert_str(mark, &decls);
            }
            strs.push(s);
        }
        Ok(strs)
    }

    /// The value of `e` in a temporary (or as is when it is a literal, a
    /// temporary, or a plain local: evaluated exactly where it is used).
    fn materialize(&mut self, e: &Expr) -> R<String> {
        let s = self.expr(e)?;
        if Self::is_stable(&s) || is_c_ident(&s) {
            return Ok(s);
        }
        let (t, tn) = self.temp(&e.ty);
        self.line(&format!("{tn} {t} = {s};"));
        Ok(t)
    }

    /// A place-like C string for `e` (an lvalue, or a temporary holding it).
    fn place_like(&mut self, e: &Expr) -> R<String> {
        if let Some(p) = e.as_place() { self.place(&p) } else { self.materialize(e) }
    }

    // -------------------------------------------------------- statements

    fn stmt(&mut self, s: &Stmt) -> R<()> {
        match &s.kind {
            StmtKind::Let(l, e) => {
                if Some(*l) == self.nrvo {
                    let ty = self.local_ty(*l);
                    return self.assign_into("(*out)", &ty, e);
                }
                let ty = self.local_ty(*l);
                let name = self.fresh_local(*l);
                self.locals.insert(*l, LocalC { lvalue: name.clone() });
                self.declare(&name, &ty, e)?;
                if let Some(void) = self.unread_use(*l, &name) {
                    self.line(&void);
                }
                Ok(())
            }
            StmtKind::Assign(p, e) => {
                let ty = self.place_ty(p)?;
                let target = self.place(p)?;
                self.assign_into(&target, &ty, e)
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
                self.block_into(b, None)?;
                self.close("}");
                Ok(())
            }
            StmtKind::ForRange(l, lo, hi, b) => {
                let los = self.materialize(lo)?;
                let his = {
                    let v = self.expr(hi)?;
                    if Self::is_stable(&v) { v } else { self.materialize_str(&v, &hi.ty) }
                };
                let ty = self.local_ty(*l);
                let tn = self.cx.names.name(&ty);
                let name = self.fresh_local(*l);
                self.locals.insert(*l, LocalC { lvalue: name.clone() });
                self.open(&format!("for ({tn} {name} = {los}; {name} < {his}; {name}++) {{"));
                self.block_into(b, None)?;
                self.close("}");
                Ok(())
            }
            StmtKind::Break => {
                self.line("break;");
                Ok(())
            }
            StmtKind::Continue => {
                self.line("continue;");
                Ok(())
            }
            StmtKind::Return(None) => {
                self.line("return;");
                Ok(())
            }
            StmtKind::Return(Some(e)) => {
                if self.def.sret {
                    let ret = self.def.ret.clone();
                    self.assign_into("(*out)", &ret, e)?;
                    self.line("return;");
                } else if self.def.ret == Ty::Unit {
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

    /// `T name = e;` or `T name;` followed by construction in place.
    fn declare(&mut self, name: &str, ty: &Ty, e: &Expr) -> R<()> {
        let tn = self.cx.names.name(ty);
        if matches!(ty, Ty::Buf(_)) {
            return Err(unsupported(e.span, Feature::Buf, &[]));
        }
        if needs_construction(e) {
            self.line(&format!("{tn} {name};"));
            self.assign_into(name, ty, e)
        } else {
            let v = self.expr(e)?;
            self.line(&format!("{tn} {name} = {v};"));
            Ok(())
        }
    }

    /// Store the value of `e` into the C lvalue `target` of type `ty`.
    fn assign_into(&mut self, target: &str, ty: &Ty, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Zeroed if ty.is_aggregate() => {
                let bulk = match ty {
                    Ty::Struct(id) => self.cx.bulk.get(id).cloned(),
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
                if let (Ty::Struct(id), true) = (ty, self.cx.bulk.contains_key(&struct_id(ty))) {
                    let _ = id;
                    return Err(unsupported(e.span, Feature::BulkCopy, &[]));
                }
                let v = self.expr(e)?;
                self.line(&format!("{target} = {v};"));
                Ok(())
            }
        }
    }

    /// Emit a block's statements; its value goes to `target` (or is dropped).
    fn block_into(&mut self, b: &Block, target: Option<(&str, &Ty)>) -> R<()> {
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

    fn switch_into(
        &mut self,
        s: &str,
        arms: &[(u32, Block)],
        default: Option<&Block>,
        target: Option<(&str, &Ty)>,
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

    fn panic_stmt(&mut self, m: onsa_core::MsgId, span: Span) {
        let msg = self.cx.msg(&self.cx.m.messages[m.0 as usize]);
        let loc = self.loc(span);
        self.line(&format!("onsa_panic({msg}, {loc});"));
    }

    /// An expression evaluated for its effects only.
    fn expr_stmt(&mut self, e: &Expr) -> R<()> {
        match &e.kind {
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                if def.sret {
                    let ret = def.ret.clone();
                    let (t, tn) = self.temp(&ret);
                    self.line(&format!("{tn} {t};"));
                    return self.assign_into(&t, &ret, e);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                self.line(&format!("{name}({});", call.join(", ")));
                Ok(())
            }
            ExprKind::Prim { .. } => {
                let v = self.expr(e)?;
                if !Self::is_stable(&v) || e.ty != Ty::Unit {
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
    fn call_args(&mut self, f: FnId, args: &[onsa_core::Arg]) -> R<Vec<String>> {
        let callee = self.cx.m.fn_(f);
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        let mut out = Vec::new();
        // Pointer-passed arguments must be places: evaluate them as such.
        let mut strs = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let p = &callee.params[i];
            let by_ptr = matches!(p.mode, Mode::Inout) && !matches!(p.ty, Ty::Span(_))
                || (matches!(p.mode, Mode::Borrow) && p.ty.is_aggregate());
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

    // -------------------------------------------------------- expressions

    fn expr(&mut self, e: &Expr) -> R<String> {
        match &e.kind {
            ExprKind::Lit(l) => Ok(lit(l, &e.ty)),
            ExprKind::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            ExprKind::Const(c) => Ok(self.cx.const_names.get(c).cloned().ok_or_else(|| internal("unknown const"))?),
            ExprKind::Zeroed => {
                if let Some(z) = zero_scalar(&e.ty) {
                    return Ok(z);
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("memset(&{t}, 0, sizeof {t});"));
                Ok(t)
            }
            ExprKind::Unary(op, x) => {
                let v = self.expr(x)?;
                Ok(match (op, &e.ty) {
                    (UnOp::Neg, Ty::Int(k)) => format!("onsa_neg_{}({v}, {})", int_tag(*k), self.loc(e.span)),
                    (UnOp::Neg, Ty::Float(FloatKind::F32)) => format!("(float)(-{v})"),
                    (UnOp::Neg, _) => format!("(-{v})"),
                    (UnOp::Not, Ty::Bool) => format!("(!{v})"),
                    (UnOp::Not, Ty::Int(k)) => format!("(({})~{v})", crate::names::int_c(*k)),
                    (UnOp::Not, _) => format!("(!{v})"),
                })
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                let ops = self.operands(&[lhs, rhs])?;
                let (a, b) = (&ops[0], &ops[1]);
                let loc = self.loc(e.span);
                Ok(match &e.ty {
                    Ty::Float(k) => {
                        let s = match op {
                            BinOp::Add => format!("{a} + {b}"),
                            BinOp::Sub => format!("{a} - {b}"),
                            BinOp::Mul => format!("{a} * {b}"),
                            BinOp::Div => format!("{a} / {b}"),
                            BinOp::Rem => return Ok(format!("onsa_fmod_{}({a}, {b})", float_tag(*k))),
                            _ => return Err(internal("bitwise operator on a float")),
                        };
                        match k {
                            FloatKind::F32 => format!("(float)({s})"),
                            FloatKind::F64 => format!("({s})"),
                        }
                    }
                    Ty::Int(k) => {
                        let t = int_tag(*k);
                        let c = crate::names::int_c(*k);
                        match (op, overflow) {
                            (BinOp::Add, Overflow::Checked) => format!("onsa_add_{t}({a}, {b}, {loc})"),
                            (BinOp::Sub, Overflow::Checked) => format!("onsa_sub_{t}({a}, {b}, {loc})"),
                            (BinOp::Mul, Overflow::Checked) => format!("onsa_mul_{t}({a}, {b}, {loc})"),
                            (BinOp::Add, Overflow::Wrap) => format!("onsa_wadd_{t}({a}, {b})"),
                            (BinOp::Sub, Overflow::Wrap) => format!("onsa_wsub_{t}({a}, {b})"),
                            (BinOp::Mul, Overflow::Wrap) => format!("onsa_wmul_{t}({a}, {b})"),
                            (BinOp::Add, Overflow::Sat) => format!("onsa_sadd_{t}({a}, {b})"),
                            (BinOp::Sub, Overflow::Sat) => format!("onsa_ssub_{t}({a}, {b})"),
                            (BinOp::Mul, Overflow::Sat) => format!("onsa_smul_{t}({a}, {b})"),
                            (BinOp::Div, _) => format!("onsa_div_{t}({a}, {b}, {loc})"),
                            (BinOp::Rem, _) => format!("onsa_rem_{t}({a}, {b}, {loc})"),
                            (BinOp::BitAnd, _) => format!("(({c})({a} & {b}))"),
                            (BinOp::BitOr, _) => format!("(({c})({a} | {b}))"),
                            (BinOp::BitXor, _) => format!("(({c})({a} ^ {b}))"),
                            (BinOp::Shl, _) => format!("onsa_shl_{t}({a}, {b}, {loc})"),
                            (BinOp::Shr, _) => format!("onsa_shr_{t}({a}, {b}, {loc})"),
                        }
                    }
                    Ty::Bool => match op {
                        BinOp::BitAnd => format!("((bool)({a} & {b}))"),
                        BinOp::BitOr => format!("((bool)({a} | {b}))"),
                        BinOp::BitXor => format!("((bool)({a} ^ {b}))"),
                        _ => return Err(internal("arithmetic on Bool")),
                    },
                    _ => return Err(internal("binary operator on a non-scalar")),
                })
            }
            ExprKind::Cmp { op, lhs, rhs } => {
                let ops = self.operands(&[lhs, rhs])?;
                let c = match op {
                    CmpOp::Eq => "==",
                    CmpOp::Ne => "!=",
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                    CmpOp::Gt => ">",
                    CmpOp::Ge => ">=",
                };
                Ok(format!("({} {c} {})", ops[0], ops[1]))
            }
            ExprKind::Logic { op, lhs, rhs } => {
                let a = self.expr(lhs)?;
                let mark = self.out.len();
                let saved = self.indent;
                self.indent += 1;
                let b = self.expr(rhs)?;
                let rhs_stmts = self.out.split_off(mark);
                self.indent = saved;
                let c = match op {
                    LogicOp::And => "&&",
                    LogicOp::Or => "||",
                };
                if rhs_stmts.is_empty() {
                    return Ok(format!("({a} {c} {b})"));
                }
                // Short-circuit with statements on the right-hand side.
                let (t, _) = self.temp(&Ty::Bool);
                self.line(&format!("bool {t} = {a};"));
                let test = if matches!(op, LogicOp::And) { t.clone() } else { format!("!{t}") };
                self.open(&format!("{} {{", if_(&test)));
                self.out.push_str(&rhs_stmts);
                self.line(&format!("{t} = {b};"));
                self.close("}");
                Ok(t)
            }
            ExprKind::Cast(x) => {
                let v = self.expr(x)?;
                let tn = self.cx.names.name(&e.ty);
                Ok(format!("(({tn}){v})"))
            }
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                let ret = def.ret.clone();
                if def.sret {
                    let (t, tn) = self.temp(&ret);
                    self.line(&format!("{tn} {t};"));
                    self.assign_into(&t, &ret, e)?;
                    return Ok(t);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                if ret == Ty::Unit {
                    self.line(&format!("{name}({});", call.join(", ")));
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(&ret);
                self.line(&format!("{tn} {t} = {name}({});", call.join(", ")));
                Ok(t)
            }
            ExprKind::Prim { prim, args } => self.prim(prim, args, e),
            ExprKind::Field { base, index } => {
                let bs = self.place_like(base)?;
                let bt = base.ty.clone();
                self.field_access(&bs, &bt, *index)
            }
            ExprKind::Index { base, index } => {
                let bs = self.place_like(base)?;
                let idx = self.materialize(index)?;
                let bt = base.ty.clone();
                self.index_access(&bs, &bt, &idx, e.span)
            }
            ExprKind::SpanOf(x) => {
                let xs = self.place_like(x)?;
                match &x.ty {
                    Ty::Array(el, n) => {
                        let tag = self.cx.names.tag(el);
                        let _ = self.cx.names.name(&e.ty);
                        Ok(format!("onsa_span_{tag}_of({xs}.a, UINT32_C({n}))"))
                    }
                    Ty::Span(_) => Ok(xs),
                    Ty::Buf(_) => Err(unsupported(e.span, Feature::Buf, &[])),
                    _ => Err(internal("span of a non-sequence")),
                }
            }
            ExprKind::Struct { ty, fields } => {
                let tn = self.cx.names.name(&e.ty);
                let names: Vec<String> = self.cx.fields(*ty).iter().map(|(n, _)| ident(n)).collect();
                if fields.is_empty() {
                    return Ok(format!("(({tn}){{ .onsa_empty = 0 }})"));
                }
                let refs: Vec<&Expr> = fields.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().zip(names).map(|(v, n)| format!(".{n} = {v}")).collect();
                Ok(format!("(({tn}){{ {} }})", parts.join(", ")))
            }
            ExprKind::Variant { ty, tag, fields } => {
                let tn = self.cx.names.name(&e.ty);
                let vname = ident(&self.cx.variants(*ty)[*tag as usize].0);
                if fields.is_empty() {
                    return Ok(format!("(({tn}){{ .tag = {tag} }})"));
                }
                let refs: Vec<&Expr> = fields.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                Ok(format!("(({tn}){{ .tag = {tag}, .u = {{ .v_{vname} = {{ {} }} }} }})", parts.join(", ")))
            }
            ExprKind::Array(xs) => {
                let tn = self.cx.names.name(&e.ty);
                if xs.is_empty() {
                    return Ok(format!("(({tn}){{ {{ 0 }} }})"));
                }
                let refs: Vec<&Expr> = xs.iter().collect();
                let vs = self.operands(&refs)?;
                Ok(format!("(({tn}){{ {{ {} }} }})", vs.join(", ")))
            }
            ExprKind::Repeat { elem, n } => {
                let tn = self.cx.names.name(&e.ty);
                let v = self.materialize(elem)?;
                if *n <= 8 {
                    return Ok(format!("(({tn}){{ {{ {} }} }})", vec![v; *n as usize].join(", ")));
                }
                let (t, _) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.open("{");
                self.line("uint32_t onsa_i;");
                self.line(&format!("for (onsa_i = 0; onsa_i < {n}; onsa_i++) {t}.a[onsa_i] = {v};"));
                self.close("}");
                Ok(t)
            }
            ExprKind::Tuple(xs) => {
                let tn = self.cx.names.name(&e.ty);
                if xs.is_empty() {
                    return Ok("((onsa_unit){0})".into());
                }
                let refs: Vec<&Expr> = xs.iter().collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = vs.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                Ok(format!("(({tn}){{ {} }})", parts.join(", ")))
            }
            ExprKind::Tag(x) => {
                let xs = self.place_like(x)?;
                Ok(format!("{xs}.tag"))
            }
            ExprKind::Payload { base, tag, index } => {
                let bs = self.place_like(base)?;
                let Ty::Enum(id) = &base.ty else { return Err(internal("payload of a non-enum")) };
                let vname = ident(&self.cx.variants(*id)[*tag as usize].0);
                Ok(format!("{bs}.u.v_{vname}.f{index}"))
            }
            ExprKind::IfExpr { .. } | ExprKind::Switch { .. } => {
                if e.ty == Ty::Unit {
                    self.expr_stmt(e)?;
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                let ty = e.ty.clone();
                self.assign_into(&t, &ty, e)?;
                Ok(t)
            }
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    self.stmt(s)?;
                }
                match &b.value {
                    Some(v) if !b.diverges() => self.expr(v),
                    _ => Ok("((onsa_unit){0})".into()),
                }
            }
            ExprKind::Panic { msg: m, .. } => {
                self.panic_stmt(*m, e.span);
                if let Some(z) = zero_scalar(&e.ty) {
                    return Ok(z);
                }
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("memset(&{t}, 0, sizeof {t});"));
                Ok(t)
            }
        }
    }

    fn prim(&mut self, prim: &Prim, args: &[onsa_core::Arg], e: &Expr) -> R<String> {
        let loc = self.loc(e.span);
        let refs: Vec<&Expr> = args.iter().map(|a| &a.expr).collect();
        match prim {
            Prim::Math(f, k) => {
                let vs = self.operands(&refs)?;
                let (a, b) = (vs[0].clone(), vs.get(1).cloned().unwrap_or_default());
                let sfx = match k {
                    FloatKind::F32 => "f",
                    FloatKind::F64 => "",
                };
                let t = float_tag(*k);
                Ok(match f {
                    MathFn::Exp => format!("exp{sfx}({a})"),
                    MathFn::Exp2 => format!("exp2{sfx}({a})"),
                    MathFn::Log => format!("log{sfx}({a})"),
                    MathFn::Log2 => format!("log2{sfx}({a})"),
                    MathFn::Sin => format!("sin{sfx}({a})"),
                    MathFn::Cos => format!("cos{sfx}({a})"),
                    MathFn::Tan => format!("tan{sfx}({a})"),
                    MathFn::Tanh => format!("tanh{sfx}({a})"),
                    MathFn::Pow => format!("pow{sfx}({a}, {b})"),
                    MathFn::Sqrt => format!("sqrt{sfx}({a})"),
                    MathFn::Floor => format!("floor{sfx}({a})"),
                    MathFn::Ceil => format!("ceil{sfx}({a})"),
                    MathFn::Trunc => format!("trunc{sfx}({a})"),
                    MathFn::Round => format!("onsa_round_{t}({a})"),
                    MathFn::Abs => format!("fabs{sfx}({a})"),
                    MathFn::Min => format!("onsa_fmin_{t}({a}, {b})"),
                    MathFn::Max => format!("onsa_fmax_{t}({a}, {b})"),
                    MathFn::Fmod => format!("onsa_fmod_{t}({a}, {b})"),
                })
            }
            Prim::IntAbs(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_abs_{}({}, {loc})", int_tag(*k), vs[0]))
            }
            Prim::IntMin(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_min_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IntMax(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_max_{}({}, {})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::Narrow { from, to } => {
                // The range check is the runtime's (ONSA_DEFINE_NARROW): no comparison
                // that the types decide, none of a signed and an unsigned value (R-11, R-145).
                let vs = self.operands(&refs)?;
                let Ty::Enum(id) = &e.ty else { return Err(internal("narrow result")) };
                let (t, tn) = self.temp(&e.ty);
                let (r, rc) = self.temp(&Ty::Int(*to));
                let some = ident(&self.cx.variants(*id)[1].0);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("{rc} {r};"));
                self.open(&format!(
                    "{} {{",
                    if_(&format!("onsa_narrow_{}_{}({}, &{r})", int_tag(*from), int_tag(*to), vs[0]))
                ));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = {r} }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::IntToFloat { to, .. } | Prim::FloatToFloat { to, .. } => {
                let vs = self.operands(&refs)?;
                Ok(format!("(({}){})", crate::names::float_c(*to), vs[0]))
            }
            Prim::TruncToInt { from, to, sat } => {
                let vs = self.operands(&refs)?;
                let (f, t) = (float_tag(*from), int_tag(*to));
                Ok(if *sat {
                    format!("onsa_trunc_sat_{t}_{f}({})", vs[0])
                } else {
                    format!("onsa_trunc_{t}_{f}({}, {loc})", vs[0])
                })
            }
            Prim::ToBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::FromBits(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_from_bits_{}({})", float_tag(*k), vs[0]))
            }
            Prim::Checked(op, k) => {
                let vs = self.operands(&refs)?;
                let Ty::Enum(id) = &e.ty else { return Err(internal("checked result")) };
                let (t, tn) = self.temp(&e.ty);
                let (r, rc) = self.temp(&Ty::Int(*k));
                let some = ident(&self.cx.variants(*id)[1].0);
                let opn = match op {
                    CheckedOp::Add => "cadd",
                    CheckedOp::Sub => "csub",
                    CheckedOp::Mul => "cmul",
                    CheckedOp::Div => "cdiv",
                };
                self.line(&format!("{tn} {t};"));
                self.line(&format!("{rc} {r};"));
                self.open(&format!("{} {{", if_(&format!("onsa_{opn}_{}({}, {}, &{r})", int_tag(*k), vs[0], vs[1]))));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = {r} }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::DivEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_div_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::RemEuclid(k) => {
                let vs = self.operands(&refs)?;
                Ok(format!("onsa_rem_euclid_{}({}, {}, {loc})", int_tag(*k), vs[0], vs[1]))
            }
            Prim::IsNan(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isnan({}))", vs[0]))
            }
            Prim::IsFinite(_) => {
                let vs = self.operands(&refs)?;
                Ok(format!("((bool)isfinite({}))", vs[0]))
            }
            Prim::Len => {
                let s = self.place_like(&args[0].expr)?;
                match &args[0].expr.ty {
                    Ty::Span(_) => Ok(format!("{s}.len")),
                    Ty::Array(_, n) => Ok(format!("UINT32_C({n})")),
                    _ => Err(unsupported(e.span, Feature::Buf, &[])),
                }
            }
            Prim::Slice => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                Ok(format!("onsa_slice_{tag}({s}, {}, {}, {loc})", vs[0], vs[1]))
            }
            Prim::Get => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let i = self.materialize_str(&vs[0], &Ty::u32());
                let Ty::Enum(id) = &e.ty else { return Err(internal("get result")) };
                let some = ident(&self.cx.variants(*id)[1].0);
                let (t, tn) = self.temp(&e.ty);
                self.line(&format!("{tn} {t};"));
                self.open(&format!("{} {{", if_(&format!("{i} < {s}.len"))));
                self.line(&format!("{t} = ({tn}){{ .tag = 1, .u = {{ .v_{some} = {{ .f0 = {s}.ptr[{i}] }} }} }};"));
                self.indent -= 1;
                self.line("} else {");
                self.indent += 1;
                self.line(&format!("{t} = ({tn}){{ .tag = 0 }};"));
                self.close("}");
                Ok(t)
            }
            Prim::Fill => {
                let s = self.span_arg(&args[0].expr)?;
                let vs = self.operands(&refs[1..])?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                self.line(&format!("onsa_fill_{tag}({s}, {});", vs[0]));
                Ok("((onsa_unit){0})".into())
            }
            Prim::AddFrom | Prim::CopyFrom => {
                let d = self.span_arg(&args[0].expr)?;
                let s = self.span_arg(&args[1].expr)?;
                let tag = self.span_tag(&args[0].expr.ty)?;
                let f = if matches!(prim, Prim::AddFrom) { "add_from" } else { "copy_from" };
                self.line(&format!("onsa_{f}_{tag}({d}, {s}, {loc});"));
                Ok("((onsa_unit){0})".into())
            }
            Prim::BufZeroed => Err(unsupported(e.span, Feature::Buf, &[])),
            Prim::Std(name) => Err(unsupported(e.span, Feature::StdFn, &[name])),
        }
    }

    fn materialize_str(&mut self, s: &str, ty: &Ty) -> String {
        if Self::is_stable(s) {
            return s.to_string();
        }
        let (t, tn) = self.temp(ty);
        self.line(&format!("{tn} {t} = {s};"));
        t
    }

    /// A span-typed argument as a C value (arrays become spans over the place).
    fn span_arg(&mut self, e: &Expr) -> R<String> {
        match &e.ty {
            Ty::Span(_) => self.place_like(e),
            Ty::Array(el, n) => {
                let p = self.place_like(e)?;
                let tag = self.cx.names.tag(el);
                let _ = self.cx.names.name(&Ty::Span(el.clone()));
                Ok(format!("onsa_span_{tag}_of({p}.a, UINT32_C({n}))"))
            }
            _ => Err(unsupported(e.span, Feature::Buf, &[])),
        }
    }

    fn span_tag(&mut self, ty: &Ty) -> R<String> {
        match ty {
            Ty::Span(el) | Ty::Array(el, _) => Ok(self.cx.names.tag(el)),
            _ => Err(unsupported(no_span(), Feature::Buf, &[])),
        }
    }
}

/// `if (cond)`: every `if` the backend writes is made here, so its condition
/// goes through [`condition`] (R-142).
fn if_(cond: &str) -> String {
    format!("if ({})", condition(cond))
}

/// `while (cond)`, as [`if_`].
fn while_(cond: &str) -> String {
    format!("while ({})", condition(cond))
}

/// A C expression as the condition of `if (…)` / `while (…)`: without the
/// parentheses that wrap the whole of it (a comparison is emitted as
/// `(a == b)`, and `if ((a == b))` is clang's `-Wparentheses-equality`, R-142).
fn condition(s: &str) -> &str {
    let b = s.as_bytes();
    if b.first() != Some(&b'(') || b.last() != Some(&b')') {
        return s;
    }
    let mut depth = 0usize;
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return if i == b.len() - 1 { &s[1..s.len() - 1] } else { s };
                }
            }
            _ => {}
        }
    }
    s
}

/// The suffix of the guarded twin of a function: what a `panic = "poison"`
/// wrapper calls after its `setjmp` (R-167). The twin is never inlined, so the
/// body's variables live in the twin's frame and not in the frame that
/// `longjmp` returns to (no gcc `-Wclobbered`, and nothing that the wrapper
/// changes after the `setjmp` is read after the `longjmp`, C11 §7.13.2.1).
pub(crate) const GUARDED_SUFFIX: &str = "__guarded";

/// The name of a C parameter declaration (`const T* x` → `x`).
fn c_param_name(decl: &str) -> &str {
    let start = decl.rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).map_or(0, |i| i + 1);
    &decl[start..]
}

/// `base.` — or `p->` when `base` is a dereferenced pointer parameter `(*p)`.
fn dot(base: &str) -> String {
    if let Some(inner) = base.strip_prefix("(*").and_then(|r| r.strip_suffix(')'))
        && inner.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return format!("{inner}->");
    }
    format!("{base}.")
}

fn is_c_ident(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn struct_id(ty: &Ty) -> TypeId {
    match ty {
        Ty::Struct(id) => *id,
        _ => TypeId(u32::MAX),
    }
}

/// Expressions that are built in place rather than assigned from a C expression.
fn needs_construction(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Zeroed => e.ty.is_aggregate(),
        ExprKind::Call { .. }
        | ExprKind::IfExpr { .. }
        | ExprKind::Switch { .. }
        | ExprKind::Block(_)
        | ExprKind::Panic { .. } => true,
        ExprKind::Repeat { n, .. } => *n > 8,
        _ => false,
    }
}

pub(crate) fn field_ty(cx: &Cx, base: &Ty, index: u32) -> R<Ty> {
    match base {
        Ty::Tuple(ts) => ts.get(index as usize).cloned().ok_or_else(|| internal("tuple index")),
        Ty::Struct(id) => {
            cx.fields(*id).get(index as usize).map(|(_, t)| t.clone()).ok_or_else(|| internal("field index"))
        }
        _ => Err(internal("field of a non-record")),
    }
}

/// A state the C backend cannot be in: an internal error (S-67), not E0200.
/// The driver's guard reports it with the function being emitted.
pub(crate) fn internal(msg: &str) -> Diagnostic {
    onsa_diag::internal::bug(None, format!("internal C backend error: {msg}"))
}
