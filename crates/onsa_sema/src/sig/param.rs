//! `@param` (§11.7): the metadata of a `block` input, in the stage of the
//! items flows generate.

use super::*;
use onsa_syntax::ast::ExprId;

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

/// What a key of `@param` takes: a value of the input's type, a `Str`, or
/// one of the words listed.
#[derive(Clone, Copy)]
enum Takes {
    Number,
    Text,
    Word(&'static [&'static str]),
}

/// A key of `@param`: what it takes, whether an attribute needs it, and
/// whether a `Bool` input takes it.
struct Key {
    key: ParamKey,
    takes: Takes,
    required: bool,
    of_bool: bool,
}

/// The keys of `@param` (§11.7, a closed list): the one table.
const KEYS: [Key; 8] = [
    Key { key: ParamKey::Min, takes: Takes::Number, required: false, of_bool: false },
    Key { key: ParamKey::Max, takes: Takes::Number, required: false, of_bool: false },
    Key { key: ParamKey::Default, takes: Takes::Number, required: true, of_bool: true },
    Key { key: ParamKey::Step, takes: Takes::Number, required: false, of_bool: false },
    Key { key: ParamKey::Unit, takes: Takes::Text, required: false, of_bool: true },
    Key { key: ParamKey::Scale, takes: Takes::Word(&["linear", "log"]), required: false, of_bool: false },
    Key { key: ParamKey::Label, takes: Takes::Text, required: false, of_bool: true },
    Key { key: ParamKey::Id, takes: Takes::Text, required: false, of_bool: true },
];

/// The form of a value of `@param` this version takes (§11.7; the
/// evaluation of the other forms is W9-03).
pub(crate) enum Literal {
    /// A literal that is no string, under parentheses and prefix `-`.
    Number,
    /// The text of a string literal with no hole, under parentheses.
    Text(String),
}

/// The form of the value `e` of `@param`, `None` when it is not one of the
/// literals ([`Literal`]): the one test of it, for the types stage's E0200
/// and the text of a text key.
pub(crate) fn literal(ast: &Ast, e: ExprId) -> Option<Literal> {
    match &ast.expr(ast.without_parens(e)).kind {
        ExprKind::Unary { op: UnOp::Neg, expr } => match literal(ast, *expr)? {
            Literal::Number => Some(Literal::Number),
            Literal::Text(_) => None,
        },
        ExprKind::Lit(Lit::Str(s)) => s.value().map(Literal::Text),
        ExprKind::Lit(_) => Some(Literal::Number),
        _ => None,
    }
}

/// The candidate of the E0401 at the value `e` of `@param` on an input of
/// the type `ty` (§11.7, S-200): when the whole of `e` is a number literal
/// (under a prefix `-` too, under no parentheses) of the other kind, the
/// literal of the kind of `ty` with the same value (`1` → `1.0`, `0x10` →
/// `16.0`, `2.00` → `2`), and none for a fraction, a value out of the
/// type, `-` on an unsigned type or `-0` on a float type. It replaces the
/// literal, keeping `-`.
pub(crate) fn candidate(ast: &Ast, e: ExprId, ty: &Ty) -> Option<(Span, Fix)> {
    let (lit, negative) = match &ast.expr(e).kind {
        ExprKind::Unary { op: UnOp::Neg, expr } => (*expr, true),
        _ => (e, false),
    };
    let text = match (&ast.expr(lit).kind, ty) {
        // `-0` is 0, and `-0.0` another value: no candidate.
        (ExprKind::Lit(Lit::Int { value, .. }), Ty::Float(_)) if *value != 0 || !negative => format!("{value}.0"),
        (ExprKind::Lit(Lit::Float { text }), Ty::Int(k)) if k.signed() || !negative => {
            let (n, (lo, hi)) = (whole_value(text)?, k.range());
            (lo..=hi).contains(&if negative { -n } else { n }).then(|| n.to_string())?
        }
        _ => return None,
    };
    let at = ast.expr(lit).span;
    Some((ast.expr(e).span, Fix::replace(format!("write `{text}`"), at, text)))
}

/// The value of the float literal `text` when it is a whole number
/// (`2.00`, `1e3`), read exactly from its digits (no rounding makes
/// `2.0000000000000001` whole); `None` for one of more than 30 digits.
fn whole_value(text: &str) -> Option<i128> {
    let t = text.replace('_', "").to_ascii_lowercase();
    let (mantissa, exp) = match t.split_once('e') {
        Some((m, x)) => (m, x.parse::<i64>().ok()?),
        None => (t.as_str(), 0),
    };
    let (int, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{int}{frac}");
    let digits = digits.trim_start_matches('0');
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return digits.is_empty().then_some(0);
    }
    // The value is `digits` times ten to `shift`; the digits after the point are zeros.
    let shift = exp.checked_sub(frac.len() as i64)?;
    let kept = usize::try_from(digits.len() as i64 + shift.min(0)).ok()?;
    let zeros = usize::try_from(shift.max(0)).ok()?;
    if digits[kept..].bytes().any(|b| b != b'0') || zeros.saturating_add(kept) > 30 {
        return None;
    }
    format!("{}{}", &digits[..kept], "0".repeat(zeros)).parse().ok()
}

fn e0809(span: Span, msg: String) -> Diagnostic {
    Diagnostic::new(Stage::Flow, Code::E0809, span, msg)
}

impl<'p> Sema<'p> {
    /// The metadata of the `@param` `attr` of an input of the flow `id`, of
    /// the clock `clock` and of the value type `ty` written at `ty_span`
    /// (§11.7), and its E0809s. An attribute with an E0809 is not read
    /// further and gives no metadata (§6.5): its values are no defs, so that
    /// no later stage reports them first. The missing `default` is the last
    /// check, made only when the keys written have no E0809. Each value of
    /// a number or a text is a def of a `const` of its type, which the later
    /// stages check as an initializer (§11.7: the rules of a `const`).
    pub(super) fn lower_param_attr(
        &mut self,
        cx: &Cx<'p>,
        id: DefId,
        attr: &Attr,
        clock: Clock,
        (ty, ty_span): (TyId, Span),
    ) -> Option<ParamMeta> {
        if clock != Clock::Block {
            self.report(id, e0809(attr.span, "`@param` goes on `block` inputs only (§11.7)".into()));
            return None;
        }
        // SPEC-GAP(S-1121): a value type out of the list is the one E0809 of the attribute.
        let Some(kind) = param_kind(self.a.types.get(ty)) else {
            self.wrong_param_type(id, ty, ty_span);
            return None;
        };
        let mut seen: [Option<Span>; KEYS.len()] = [None; KEYS.len()];
        let (mut errs, mut values) = (Vec::new(), Vec::new());
        for arg in &attr.args {
            let AttrArg::Named { key, value } = arg else {
                errs.push(e0809(attr.span, "`@param` takes `key: value` pairs".into()));
                continue;
            };
            let named = |k: &Key| k.key.name() == key.name;
            let Some(k) = KEYS.iter().position(named) else {
                let names: Vec<&str> = KEYS.iter().map(|k| k.key.name()).collect();
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
            if kind == ParamKind::Bool && !KEYS[k].of_bool {
                let of_bool: Vec<&str> = KEYS.iter().filter(|k| k.of_bool).map(|k| k.key.name()).collect();
                let msg = format!("a `Bool` input takes the `@param` keys {} alone (§11.7)", of_bool.join(" "));
                errs.push(e0809(key.span, msg).with_found(key.name.clone()));
                continue;
            }
            let text = match literal(cx.ast, *value) {
                Some(Literal::Text(t)) => Some(t),
                _ => None,
            };
            if let Takes::Word(words) = KEYS[k].takes
                && !text.as_deref().is_some_and(|t| words.contains(&t))
            {
                let listed: Vec<String> = words.iter().map(|c| format!("\"{c}\"")).collect();
                let msg = format!("`@param` `{}` must be {}", key.name, listed.join(" or "));
                errs.push(e0809(cx.ast.expr(*value).span, msg));
                continue;
            }
            values.push((k, key.span, *value, text));
        }
        if errs.is_empty()
            && let Some(k) = KEYS.iter().zip(&seen).find_map(|(k, s)| (k.required && s.is_none()).then_some(k))
        {
            errs.push(e0809(attr.span, format!("`@param` needs the key `{}` (§11.7)", k.key.name())));
        }
        // A flow cut by a syntax error or `@mem` is not checked further (§18.1).
        if !errs.is_empty() || self.a.failed.contains_key(&id) {
            errs.into_iter().for_each(|d| self.report(id, d));
            return None;
        }
        let values = values.into_iter().map(|(k, key_span, value, text)| {
            let ty = match KEYS[k].takes {
                Takes::Number => ty,
                Takes::Text => self.a.types.intern(Ty::Builtin(BuiltinTy::Str, Vec::new())),
                Takes::Word(_) => return ParamValue { key: KEYS[k].key, key_span, def: None, text },
            };
            let def = self.param_value_def(cx, id, KEYS[k].key, value, ty);
            ParamValue { key: KEYS[k].key, key_span, def: Some(def), text }
        });
        Some(ParamMeta { values: values.collect(), span: attr.span })
    }

    /// The def of the value `value` of the key `key` of `@param` on an
    /// input of the flow `flow`: a `const` of the type `ty`, of the flow's
    /// item and unit (§18.1), in the scope of its module.
    fn param_value_def(&mut self, cx: &Cx<'p>, flow: DefId, key: ParamKey, value: ExprId, ty: TyId) -> DefId {
        let span = cx.ast.expr(value).span;
        let of_attr = Some(AttrValue::Param(key));
        let kind = DefKind::Const(ConstDef { ty, value: Some(value), int_value: None, param: None, of_attr });
        let (name, module, item) = (format!("@param {}", key.name()), cx.m, self.a.def(flow).item);
        self.add_def(Def {
            name,
            module,
            vis: Vis::Priv,
            span,
            name_span: span,
            kind,
            item,
            owner: Some(flow),
            export: None,
        })
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

impl crate::Analysis {
    /// The values of the `@param` of `input` (§11.7), evaluated: the one
    /// reading of them for the readers after the analysis (Core, `onsa
    /// interface`), of an analysis with no error.
    pub fn param_info(&self, input: &FlowInput) -> Option<ParamInfo> {
        use crate::consteval::ConstValue as C;
        let meta = input.param.as_ref()?;
        let bug = |at: Span| -> ! { onsa_diag::internal::bug(Some(at), "a value of `@param` with no value") };
        let kind = param_kind(self.types.get(input.ty)).unwrap_or_else(|| bug(meta.span));
        let mut info = ParamInfo { kind, numbers: Vec::new(), texts: Vec::new() };
        for v in &meta.values {
            let takes = KEYS.iter().find(|k| k.key == v.key).map(|k| k.takes);
            match (takes, v.def.and_then(|d| self.const_values.get(&d)), &v.text) {
                (Some(Takes::Number), Some(C::Float(x)), _) => info.numbers.push((v.key, ParamNumber::Float(*x))),
                (Some(Takes::Number), Some(C::Int(x)), _) => info.numbers.push((v.key, ParamNumber::Int(*x))),
                (Some(Takes::Number), Some(C::Bool(x)), _) => info.numbers.push((v.key, ParamNumber::Bool(*x))),
                (Some(Takes::Text | Takes::Word(_)), _, Some(t)) => info.texts.push((v.key, t.clone())),
                _ => bug(v.key_span),
            }
        }
        Some(info)
    }
}
