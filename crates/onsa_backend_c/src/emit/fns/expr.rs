//! The expressions, as C expression strings.

use super::text::if_;
use super::*;

impl<'a, 'm> FnEmitter<'a, 'm> {
    // -------------------------------------------------------- expressions

    pub(super) fn expr(&mut self, e: &Expr) -> R<String> {
        match &e.kind {
            ExprKind::Lit(l) => Ok(lit(l, self.kind(e.ty))),
            ExprKind::Local(l) => Ok(self.locals.get(l).ok_or_else(|| internal("unknown local"))?.lvalue.clone()),
            ExprKind::Const(c) => Ok(self.cx.const_names.get(c).cloned().ok_or_else(|| internal("unknown const"))?),
            ExprKind::Zeroed => {
                if let Some(z) = zero_scalar(self.kind(e.ty)) {
                    return Ok(z);
                }
                let (t, tn) = self.temp(e.ty);
                self.line(&format!("{tn} {t};"));
                self.line(&format!("memset(&{t}, 0, sizeof {t});"));
                Ok(t)
            }
            ExprKind::Unary(op, x) => {
                let v = self.expr(x)?;
                Ok(match (op, self.kind(e.ty)) {
                    (UnOp::Neg, TyKind::Int(k)) => format!("onsa_neg_{}({v}, {})", int_tag(*k), self.loc(e.span)),
                    (UnOp::Neg, TyKind::Float(FloatKind::F32)) => format!("(float)(-{v})"),
                    (UnOp::Neg, _) => format!("(-{v})"),
                    (UnOp::Not, TyKind::Bool) => format!("(!{v})"),
                    (UnOp::Not, TyKind::Int(k)) => format!("(({})~{v})", crate::names::int_c(*k)),
                    (UnOp::Not, _) => format!("(!{v})"),
                })
            }
            ExprKind::Binary { op, overflow, lhs, rhs } => {
                let ops = self.operands(&[lhs, rhs])?;
                let (a, b) = (&ops[0], &ops[1]);
                let loc = self.loc(e.span);
                Ok(match self.kind(e.ty) {
                    TyKind::Float(k) => {
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
                    TyKind::Int(k) => {
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
                    TyKind::Bool => match op {
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
                let (t, _) = self.temp(Types::BOOL);
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
                let tn = self.cx.names.name(e.ty);
                Ok(format!("(({tn}){v})"))
            }
            ExprKind::Call { fn_, args } => {
                let def = self.cx.m.fn_(*fn_);
                let ret = def.ret;
                if def.sret {
                    let (t, tn) = self.temp(ret);
                    self.line(&format!("{tn} {t};"));
                    self.assign_into(&t, ret, e)?;
                    return Ok(t);
                }
                let call = self.call_args(*fn_, args)?;
                let name = self.cx.fn_name(*fn_).to_string();
                if ret == Types::UNIT {
                    self.line(&format!("{name}({});", call.join(", ")));
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(ret);
                self.line(&format!("{tn} {t} = {name}({});", call.join(", ")));
                Ok(t)
            }
            ExprKind::Prim { prim, args } => self.prim(prim, args, e),
            ExprKind::Field { base, index } => {
                let bs = self.place_like(base)?;
                let bt = base.ty;
                self.field_access(&bs, bt, *index)
            }
            ExprKind::Index { base, index, bounds } => {
                let bs = self.place_like(base)?;
                let idx = self.materialize(index)?;
                let bt = base.ty;
                self.index_access(&bs, bt, &idx, e.span, *bounds)
            }
            ExprKind::SpanOf(x) => {
                let xs = self.place_like(x)?;
                match self.kind(x.ty) {
                    TyKind::Array(el, n) => Ok(self.array_span(&xs, e.ty, *el, *n)),
                    TyKind::Span(_) => Ok(xs),
                    TyKind::Buf(_) => Err(unsupported(e.span, Feature::Buf, &[])),
                    _ => Err(internal("span of a non-sequence")),
                }
            }
            ExprKind::Struct { ty, fields } => {
                let tn = self.cx.names.name(e.ty);
                if fields.is_empty() {
                    return Ok(format!("(({tn}){{ .onsa_empty = 0 }})"));
                }
                let refs: Vec<&Expr> = fields.iter().map(|(_, x)| x).collect();
                let vs = self.operands(&refs)?;
                let parts: Vec<String> = fields
                    .iter()
                    .zip(vs)
                    .map(|((k, _), v)| Ok(format!(".{} = {v}", self.cx.field_name(*ty, *k)?)))
                    .collect::<R<_>>()?;
                Ok(format!("(({tn}){{ {} }})", parts.join(", ")))
            }
            ExprKind::Variant { ty, tag, fields } => {
                let tn = self.cx.names.name(e.ty);
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
                let tn = self.cx.names.name(e.ty);
                let refs: Vec<&Expr> = xs.iter().collect();
                let vs = self.operands(&refs)?;
                Ok(format!("(({tn}){})", consts::array_init(self.cx, e.ty, &vs)))
            }
            ExprKind::Repeat { elem, n } => {
                let tn = self.cx.names.name(e.ty);
                let v = self.materialize(elem)?;
                // The element of none is evaluated, as in the interpreter,
                // and not read (no unused temporary, R-432).
                if *n == 0 {
                    self.line(&format!("(void){v};"));
                }
                if *n <= 8 {
                    return Ok(format!("(({tn}){})", consts::array_init(self.cx, e.ty, &vec![v; *n as usize])));
                }
                let (t, _) = self.temp(e.ty);
                self.line(&format!("{tn} {t};"));
                self.open("{");
                self.line("uint32_t onsa_i;");
                self.line(&format!("for (onsa_i = 0; onsa_i < {n}; onsa_i++) {t}.a[onsa_i] = {v};"));
                self.close("}");
                Ok(t)
            }
            ExprKind::Tuple(xs) => {
                let tn = self.cx.names.name(e.ty);
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
                let TyKind::Enum(id) = self.kind(base.ty) else { return Err(internal("payload of a non-enum")) };
                let vname = ident(&self.cx.variants(*id)[*tag as usize].0);
                Ok(format!("{bs}.u.v_{vname}.f{index}"))
            }
            ExprKind::IfExpr { .. } | ExprKind::Switch { .. } => {
                if e.ty == Types::UNIT {
                    self.expr_stmt(e)?;
                    return Ok("((onsa_unit){0})".into());
                }
                let (t, tn) = self.temp(e.ty);
                self.line(&format!("{tn} {t};"));
                let ty = e.ty;
                self.assign_into(&t, ty, e)?;
                Ok(t)
            }
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    self.stmt(s)?;
                }
                match &b.value {
                    Some(v) if !b.diverges() => self.expr(v),
                    // `{ return e }` in value position (R-365), or a block of `()`.
                    _ => Ok(self.never_read(e.ty)),
                }
            }
            ExprKind::Panic { msg: m, .. } => {
                self.panic_stmt(*m, e.span);
                Ok(self.never_read(e.ty))
            }
        }
    }
}
