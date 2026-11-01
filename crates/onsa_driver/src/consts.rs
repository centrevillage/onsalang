//! The build-time evaluation of the `const`s (spec §6.6, T3-9): a stage
//! between the lowering and the C backend (`build`).

use std::collections::BTreeSet;

use onsa_core::{ConstId, Expr, ExprKind, Lit, Module, Ty, TypeDefKind};
use onsa_interp::{ArrayData, Interp, Value};

use crate::{CoreStage, InternalError};

/// The build-time `const` evaluation as a stage: [`inline_consts`] of the
/// `const`s that `roots` reach, then the verifier at its boundary (R-82).
///
/// The evaluation and the reach are the same set (S-242, W2-13): a `const`
/// that no entry reaches is not evaluated, so its initializer cannot stop the
/// build (an internal error of the evaluation), and every `const` the C unit
/// reaches after the evaluation was offered to it (the reach of the
/// evaluated module from the same roots is a part of this one: an evaluated
/// initializer calls nothing).
pub(crate) fn consts_stage(mut module: Module, roots: &[onsa_core::FnId]) -> Result<Module, InternalError> {
    let reached = onsa_core::reach(&module, roots).consts;
    let replacements = crate::guard_on_stack(|| inline_consts(&module, &reached))?;
    for (i, e) in replacements {
        module.consts[i].init = e;
    }
    crate::verify_core(&module, CoreStage::Consts)?;
    Ok(module)
}

/// `const` initializers that call functions are evaluated with the
/// interpreter at build time (spec §6.6, T3-9): the literals that replace
/// them, so the C backend can emit a static initializer. Only the `const`s
/// of `reached`, and only through [`consts_stage`], which runs it on the
/// stack of a command (R-05).
fn inline_consts(module: &Module, reached: &BTreeSet<ConstId>) -> Vec<(usize, Expr)> {
    let mut replacements: Vec<(usize, Expr)> = Vec::new();
    {
        let interp = Interp::new(module);
        for &id in reached {
            let (i, c) = (id.0 as usize, module.const_(id));
            if is_static_init(&c.init) {
                continue;
            }
            // A panic names this `const` (S-67).
            let _scope = onsa_diag::internal::item_scope(c.init.span);
            // Each `const` is an evaluation of its own from call depth 0, as
            // in `onsa test` (spec §12.5). One that panics or reaches a form
            // the interpreter cannot run stays as it is, and the C backend
            // stops at it with E0200; E0419 at the initializer (spec §6.6,
            // S-222) is W9-03's. A failure of the interpreter itself unwinds
            // to the guard of `consts_stage` (S-67).
            let v = match interp.const_value(id) {
                Ok(v) => v,
                Err(onsa_interp::Failure::Panic(_) | onsa_interp::Failure::Unsupported(_)) => continue,
            };
            if let Some(e) = value_to_expr(module, &v, &c.ty, c.init.span) {
                replacements.push((i, e));
            }
        }
    }
    replacements
}

fn is_static_init(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(_) | ExprKind::Const(_) | ExprKind::Zeroed => true,
        ExprKind::Unary(_, x) => is_static_init(x),
        ExprKind::Struct { fields, .. } | ExprKind::Variant { fields, .. } => fields.iter().all(is_static_init),
        ExprKind::Array(xs) | ExprKind::Tuple(xs) => xs.iter().all(is_static_init),
        ExprKind::Repeat { elem, .. } => is_static_init(elem),
        _ => false,
    }
}

/// A literal / aggregate expression with the value `v`.
pub fn value_to_expr(m: &Module, v: &Value, ty: &Ty, span: onsa_diag::Span) -> Option<Expr> {
    let lit = |l: Lit| Some(Expr::new(ty.clone(), span, ExprKind::Lit(l)));
    match (v, ty) {
        (Value::I8(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I16(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I32(x), _) => lit(Lit::Int(*x as i128)),
        (Value::I64(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U8(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U16(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U32(x), _) => lit(Lit::Int(*x as i128)),
        (Value::U64(x), _) => lit(Lit::Int(*x as i128)),
        (Value::F32(x), _) => lit(Lit::F32(*x)),
        (Value::F64(x), _) => lit(Lit::F64(*x)),
        (Value::Bool(x), _) => lit(Lit::Bool(*x)),
        (Value::Char(x), _) => lit(Lit::Char(*x)),
        (Value::Unit, _) => lit(Lit::Unit),
        (Value::Array(data), Ty::Array(elem, _)) => {
            let xs: Vec<Expr> = match data {
                ArrayData::F32(xs) => {
                    xs.iter().map(|x| Expr::new((**elem).clone(), span, ExprKind::Lit(Lit::F32(*x)))).collect()
                }
                ArrayData::Any(vs) => vs.iter().map(|x| value_to_expr(m, x, elem, span)).collect::<Option<Vec<_>>>()?,
            };
            Some(Expr::new(ty.clone(), span, ExprKind::Array(xs)))
        }
        (Value::Tuple(vs), Ty::Tuple(ts)) => {
            let xs = vs.iter().zip(ts).map(|(x, t)| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Tuple(xs)))
        }
        (Value::Struct(vs), Ty::Struct(id)) => {
            let TypeDefKind::Struct { fields } = &m.ty(*id).kind else { return None };
            let xs =
                vs.iter().zip(fields).map(|(x, (_, t))| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Struct { ty: *id, fields: xs }))
        }
        (Value::Enum { tag, fields: vs }, Ty::Enum(id)) => {
            let TypeDefKind::Enum { variants } = &m.ty(*id).kind else { return None };
            let (_, tys) = variants.get(*tag as usize)?;
            let xs = vs.iter().zip(tys).map(|(x, t)| value_to_expr(m, x, t, span)).collect::<Option<Vec<_>>>()?;
            Some(Expr::new(ty.clone(), span, ExprKind::Variant { ty: *id, tag: *tag, fields: xs }))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Loaded, PackageInput};

    /// S-242, W2-13: the build-time evaluation evaluates the `const`s that the
    /// entries reach (one reaches `READ` through `get`), and no other
    /// (`UNREAD` keeps its initializer, a call), so the evaluation and the
    /// reach are the same set.
    #[test]
    fn the_const_stage_evaluates_only_the_reached_consts() {
        let src = "fn three() -> U32 {\n  3\n}\n\nfn four() -> U32 {\n  4\n}\n\nconst READ: U32 = three()\n\nconst UNREAD: U32 = four()\n\npub fn get() -> U32 {\n  READ\n}\n";
        let mut loaded = Loaded::from_input(PackageInput::single_file("t.onsa", src)).unwrap();
        let analyzed = crate::analyze_loaded(&mut loaded).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        assert!(analyzed.diagnostics.is_empty());
        let module = crate::lower_core(&analyzed).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let get = module.fns.iter().position(|f| f.name.ends_with("get")).map(|i| onsa_core::FnId(i as u32));
        let module = consts_stage(module, &[get.unwrap()]).unwrap_or_else(|e| panic!("{}", e.render(&loaded.sources)));
        let init = |name: &str| &module.consts.iter().find(|c| c.name.ends_with(name)).unwrap().init.kind;
        assert!(matches!(init("READ"), ExprKind::Lit(Lit::Int(3))), "{:?}", init("READ"));
        assert!(matches!(init("UNREAD"), ExprKind::Call { .. }), "{:?}", init("UNREAD"));
    }
}
