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
            Ok(array_init(cx, &e.ty, &parts))
        }
        ExprKind::Repeat { elem, n } => {
            let v = const_init(cx, elem)?;
            Ok(array_init(cx, &e.ty, &vec![v; *n as usize]))
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

/// The braces of an array of the type `ty` of the elements `parts`. The C
/// array of none has one element (`a[1]`), zero: braced to its first scalar,
/// as gcc's `-Wmissing-braces` takes it in another initializer (an empty one
/// is C23, R-432).
pub(super) fn array_init(cx: &Cx, ty: &Ty, parts: &[String]) -> String {
    match (parts.is_empty(), ty) {
        (true, Ty::Array(el, _)) => format!("{{ {{ {} }} }}", zero(cx, el)),
        _ => format!("{{ {{ {} }} }}", parts.join(", ")),
    }
}

/// A zero of the type `ty` as a C initializer, braced to its first scalar.
fn zero(cx: &Cx, ty: &Ty) -> String {
    match ty {
        Ty::Array(..) => array_init(cx, ty, &[]),
        Ty::Struct(id) => match cx.fields(*id).first() {
            Some((n, t)) => format!("{{ .{} = {} }}", ident(n), zero(cx, t)),
            None => "{ 0 }".into(),
        },
        Ty::Tuple(ts) => match ts.first() {
            Some(t) => format!("{{ .f0 = {} }}", zero(cx, t)),
            None => "{ 0 }".into(),
        },
        // A tag, a pointer or a unit first.
        Ty::Enum(_) | Ty::Unit | Ty::Span(_) | Ty::Buf(_) => "{ 0 }".into(),
        _ => "0".into(),
    }
}
