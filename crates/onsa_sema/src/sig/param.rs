//! `@param` (§11.7): the metadata of a `block` input, in the stage of the
//! items flows generate.

use super::*;

/// The kind of the value type of an input with `@param` (§11.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParamKind {
    Float(FloatKind),
    Int(IntKind),
    Bool,
}

/// The value types of an input with `@param` (§11.7, S-87): the one list.
const PARAM_KINDS: [ParamKind; 9] = [
    ParamKind::Float(FloatKind::F32),
    ParamKind::Float(FloatKind::F64),
    ParamKind::Int(IntKind::I8),
    ParamKind::Int(IntKind::I16),
    ParamKind::Int(IntKind::I32),
    ParamKind::Int(IntKind::U8),
    ParamKind::Int(IntKind::U16),
    ParamKind::Int(IntKind::U32),
    ParamKind::Bool,
];

impl ParamKind {
    fn ty(self) -> Ty {
        match self {
            ParamKind::Float(k) => Ty::Float(k),
            ParamKind::Int(k) => Ty::Int(k),
            ParamKind::Bool => Ty::Bool,
        }
    }
}

/// The kind of the value type `ty` of an input (an alias is lowered by
/// then), `None` of a type `@param` does not go on (E0809).
pub(crate) fn param_kind(ty: &Ty) -> Option<ParamKind> {
    PARAM_KINDS.into_iter().find(|k| k.ty() == *ty)
}

/// Where a key of `@param` puts its value in [`ParamMeta`], by the kind of
/// the value.
#[derive(Clone, Copy)]
enum Slot {
    /// A value of the input's type.
    Number(fn(&mut ParamMeta) -> &mut Option<f64>),
    /// A `Str`.
    Text(fn(&mut ParamMeta) -> &mut Option<String>),
    /// One of the strings listed.
    Choice(&'static [&'static str], fn(&mut ParamMeta) -> &mut Option<String>),
}

/// A key of `@param`: its name, its value, and whether an attribute needs it.
struct Key {
    name: &'static str,
    slot: Slot,
    required: bool,
}

/// The keys of `@param` (§11.7, a closed list): the one table.
const KEYS: [Key; 8] = [
    Key { name: "min", slot: Slot::Number(|m| &mut m.min), required: false },
    Key { name: "max", slot: Slot::Number(|m| &mut m.max), required: false },
    Key { name: "default", slot: Slot::Number(|m| &mut m.default), required: true },
    Key { name: "step", slot: Slot::Number(|m| &mut m.step), required: false },
    Key { name: "unit", slot: Slot::Text(|m| &mut m.unit), required: false },
    Key { name: "scale", slot: Slot::Choice(&["linear", "log"], |m| &mut m.scale), required: false },
    Key { name: "label", slot: Slot::Text(|m| &mut m.label), required: false },
    Key { name: "id", slot: Slot::Text(|m| &mut m.id), required: false },
];

/// A number of `@param` as this stage reads it: a literal, or `-` and a
/// literal, of the float width `width`.
fn number(cx: &Cx<'_>, e: onsa_syntax::ast::ExprId, width: onsa_syntax::FloatWidth) -> Option<Result<f64, FloatRange>> {
    let float = |text: &str| onsa_syntax::float_value(text, width);
    match &cx.ast.expr(e).kind {
        ExprKind::Lit(Lit::Float { text }) => Some(float(text)),
        ExprKind::Lit(Lit::Int { value, .. }) => Some(Ok(*value as f64)),
        ExprKind::Unary { op: UnOp::Neg, expr } => match &cx.ast.expr(*expr).kind {
            ExprKind::Lit(Lit::Float { text }) => Some(float(text).map(|v| -v)),
            ExprKind::Lit(Lit::Int { value, .. }) => Some(Ok(-(*value as f64))),
            _ => None,
        },
        _ => None,
    }
}

/// A string of `@param` as this stage reads it: the text of a string
/// literal, its holes dropped (R-291).
fn text(cx: &Cx<'_>, e: onsa_syntax::ast::ExprId) -> Option<String> {
    match &cx.ast.expr(e).kind {
        ExprKind::Lit(Lit::Str(s)) => Some(
            s.segments
                .iter()
                .map(|seg| match seg {
                    onsa_syntax::ast::StrSeg::Text(t) => t.clone(),
                    _ => String::new(),
                })
                .collect(),
        ),
        _ => None,
    }
}

fn e0809(span: Span, msg: String) -> Diagnostic {
    Diagnostic::new(Stage::Flow, Code::E0809, span, msg)
}

impl<'p> Sema<'p> {
    /// The metadata of the `@param` `attr` of an input of the flow `id`, of
    /// the clock `rate` and of the value type `ty` written at `ty_span`
    /// (§11.7), and its E0809s. An attribute or a key an E0809 rejects is not
    /// read further: an input not of `block` or of a type not in the list
    /// gives no metadata, and a key written twice no value. The missing
    /// `default` is the last check, made only when the keys written have no
    /// E0809.
    pub(super) fn lower_param_attr(
        &mut self,
        cx: &Cx<'p>,
        id: DefId,
        attr: &Attr,
        rate: Rate,
        (ty, ty_span): (TyId, Span),
    ) -> Option<ParamMeta> {
        if rate != Rate::Ctl {
            self.report(id, e0809(attr.span, "`@param` goes on `block` inputs only (§11.7)".into()));
            return None;
        }
        // A type with the error type in it has its diagnostic (§18.1).
        if self.a.types.has_error(ty) {
            return None;
        }
        // SPEC-GAP(S-1121): a value type out of the list is the one E0809 of the attribute.
        let Some(kind) = param_kind(self.a.types.get(ty)) else {
            self.wrong_param_type(id, ty, ty_span);
            return None;
        };
        // A number of `@param` is a value of the input's type (§11.7): a float
        // literal is rounded once to it (§2.4, R-20), and out of its range is
        // E0408 (R-45).
        let width = match kind {
            ParamKind::Float(k) => k.width(),
            _ => onsa_syntax::FloatWidth::F64,
        };
        let mut meta = ParamMeta::empty(attr.span, width);
        let mut seen: [Option<Span>; KEYS.len()] = [None; KEYS.len()];
        let mut errs = Vec::new();
        for arg in &attr.args {
            let AttrArg::Named { key, value } = arg else {
                errs.push(e0809(attr.span, "`@param` takes `key: value` pairs".into()));
                continue;
            };
            let Some(k) = KEYS.iter().position(|k| k.name == key.name) else {
                let names: Vec<&str> = KEYS.iter().map(|k| k.name).collect();
                let msg = format!("unknown `@param` key `{}`; keys are {} (§11.7)", key.name, names.join(" "));
                errs.push(e0809(key.span, msg).with_found(key.name.clone()));
                continue;
            };
            if let Some(first) = seen[k] {
                let msg = format!("the `@param` key `{}` is written twice; a key is written once (§11.7)", key.name);
                errs.push(e0809(key.span, msg).with_note(first, "written first here"));
                continue;
            }
            seen[k] = Some(key.span);
            let vspan = cx.ast.expr(*value).span;
            let bad = |what: &str| e0809(vspan, format!("`@param` `{}` must be {what}", key.name));
            match KEYS[k].slot {
                Slot::Number(at) => match number(cx, *value, width).map(|v| v.map_err(FloatRange::why)) {
                    Some(Ok(v)) => *at(&mut meta) = Some(v),
                    Some(Err(Some(why))) => {
                        self.report(
                            id,
                            Diagnostic::new(
                                Stage::Types,
                                Code::E0408,
                                vspan,
                                format!("this literal is out of range for the type of the input: {why} (§2.4, §11.7)"),
                            )
                            .with_found(src(cx, vspan)),
                        );
                    }
                    // A text that is no float has the lexer's E0001 (`1.5abc`).
                    Some(Err(None)) | None => errs.push(bad("a numeric literal")),
                },
                Slot::Text(at) => match text(cx, *value) {
                    Some(v) => *at(&mut meta) = Some(v),
                    None => errs.push(bad("a string literal")),
                },
                Slot::Choice(choices, at) => match text(cx, *value) {
                    Some(v) if choices.contains(&v.as_str()) => *at(&mut meta) = Some(v),
                    _ => {
                        let listed: Vec<String> = choices.iter().map(|c| format!("\"{c}\"")).collect();
                        errs.push(bad(&listed.join(" or ")));
                    }
                },
            }
        }
        if errs.is_empty()
            && let Some(k) = KEYS.iter().zip(&seen).find_map(|(k, s)| (k.required && s.is_none()).then_some(k))
        {
            errs.push(e0809(attr.span, format!("`@param` needs the key `{}` (§11.7)", k.name)));
        }
        for d in errs {
            self.report(id, d);
        }
        Some(meta)
    }

    /// The E0809 of an input with `@param` whose value type `ty`, written at
    /// `span`, is not in the list (§11.7).
    fn wrong_param_type(&mut self, id: DefId, ty: TyId, span: Span) {
        let listed: Vec<String> = PARAM_KINDS
            .iter()
            .map(|k| {
                let t = self.a.types.intern(k.ty());
                self.a.display_type(t)
            })
            .collect();
        let msg = format!(
            "`@param` goes on an input whose value type is one of {}; this one is `{}` (§11.7)",
            listed.join(" "),
            self.a.display_type(ty)
        );
        self.report(id, e0809(span, msg));
    }
}
