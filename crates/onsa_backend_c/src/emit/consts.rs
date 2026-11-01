//! The static initializers of the `const`s of the unit ([`const_init`]).

use super::*;

// ------------------------------------------------------------ constants

/// A C constant expression (static initializer) for a `const` initializer.
pub(super) fn const_init(cx: &mut Cx, e: &Expr) -> R<String> {
    match &e.kind {
        ExprKind::Lit(l) => Ok(lit(l, &e.ty)),
        ExprKind::Const(c) => {
            let init = cx.m.const_(*c).init.clone();
            const_init(cx, &init)
        }
        ExprKind::Unary(UnOp::Neg, x) => match (&x.kind, &e.ty) {
            (ExprKind::Lit(Lit::Int(v)), Ty::Int(k)) => Ok(int_lit(*k, -*v)),
            (ExprKind::Lit(Lit::F32(v)), _) => Ok(f32_lit(-*v)),
            (ExprKind::Lit(Lit::F64(v)), _) => Ok(f64_lit(-*v)),
            _ => Err(unsupported(e.span, Feature::ConstInitializer, &[])),
        },
        ExprKind::Cast(x) => {
            let inner = const_init(cx, x)?;
            let ty = cx.names.name(&e.ty);
            Ok(format!("(({ty}){inner})"))
        }
        ExprKind::Array(xs) => {
            let parts: Vec<String> = xs.iter().map(|x| const_init(cx, x)).collect::<R<_>>()?;
            Ok(format!("{{ {{ {} }} }}", parts.join(", ")))
        }
        ExprKind::Repeat { elem, n } => {
            let v = const_init(cx, elem)?;
            Ok(format!("{{ {{ {} }} }}", vec![v; *n as usize].join(", ")))
        }
        ExprKind::Tuple(xs) => {
            let parts: Vec<String> =
                xs.iter().enumerate().map(|(i, x)| Ok(format!(".f{i} = {}", const_init(cx, x)?))).collect::<R<_>>()?;
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        ExprKind::Struct { ty, fields } => {
            let names: Vec<String> = cx.fields(*ty).iter().map(|(n, _)| ident(n)).collect();
            if names.is_empty() {
                return Ok("{ 0 }".into());
            }
            let parts: Vec<String> = fields
                .iter()
                .zip(names)
                .map(|(x, n)| Ok(format!(".{n} = {}", const_init(cx, x)?)))
                .collect::<R<_>>()?;
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        ExprKind::Variant { ty, tag, fields } => {
            let vname = ident(&cx.variants(*ty)[*tag as usize].0);
            if fields.is_empty() {
                return Ok(format!("{{ .tag = {tag} }}"));
            }
            let parts: Vec<String> = fields
                .iter()
                .enumerate()
                .map(|(i, x)| Ok(format!(".f{i} = {}", const_init(cx, x)?)))
                .collect::<R<_>>()?;
            Ok(format!("{{ .tag = {tag}, .u = {{ .v_{vname} = {{ {} }} }} }}", parts.join(", ")))
        }
        // The driver inlines the value of a `const` evaluated at build time (T4-5).
        _ => Err(unsupported(e.span, Feature::ConstInitializer, &[])),
    }
}
