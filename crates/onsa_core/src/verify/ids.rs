//! The ids of a module the verifier reads (V-20). The tables of the module
//! are checked once, before any item ([`table`]); in an item, every look-up
//! of the verifier goes through the methods here, which give an id out of
//! range back as an error, never a panic.

use super::{R, Rule, V, VerifyError};
use crate::ir::*;

/// The tables of `m`, each entry once and with no recursion: every id in
/// them is in range, a part of a type is before it in the table (a walk
/// of a type ends), a struct or an enum type is of a definition of its
/// kind, and the facts cover the table. Past it, the types the items name
/// through the tables are in range.
pub(super) fn table(m: &Module) -> R<()> {
    let n = m.tys.kinds().len();
    let fail = |name: &str, span, message| Err(VerifyError { rule: Rule::V20, fn_name: name.into(), span, message });
    let def = |id: TypeId| m.types.get(id.0 as usize).map(|d| &d.kind);
    for (i, k) in m.tys.kinds().iter().enumerate() {
        if let Some(t) = k.parts().find(|t| t.index() >= i) {
            return fail("the type table", None, format!("ty {i} has the part {} not before it", t.index()));
        }
        let of_its_kind = match *k {
            TyKind::Struct(id) => matches!(def(id), Some(TypeDefKind::Struct { .. } | TypeDefKind::Opaque)),
            TyKind::Enum(id) => matches!(def(id), Some(TypeDefKind::Enum { .. })),
            _ => true,
        };
        if !of_its_kind {
            return fail("the type table", None, format!("ty {i} is of no definition of its kind"));
        }
    }
    for d in &m.types {
        let tys: Box<dyn Iterator<Item = CTy>> = match &d.kind {
            TypeDefKind::Struct { fields } => Box::new(fields.iter().map(|f| f.1)),
            TypeDefKind::Enum { variants } => Box::new(variants.iter().flat_map(|v| v.1.iter().copied())),
            TypeDefKind::Opaque => Box::new(std::iter::empty()),
        };
        if let Some(e) = out(n, tys) {
            return fail(&d.name, None, e);
        }
    }
    for c in &m.consts {
        if let Some(e) = out(n, [c.ty]) {
            return fail(&c.name, Some(c.init.span), e);
        }
    }
    for f in &m.fns {
        let tys = f.params.iter().map(|p| p.ty).chain(f.locals.iter().map(|l| l.ty)).chain([f.ret]);
        let local = |l: LocalId| l.0 as usize >= f.locals.len();
        let params = f.params.iter().any(|p| local(p.local)).then(|| "parameter local out of range".to_string());
        let hoisted = f.hoisted.iter().find(|&&h| local(h)).map(|h| format!("hoisted local {} out of range", h.0));
        if let Some(e) = out(n, tys).or(params).or(hoisted) {
            return fail(&f.name, Some(f.span), e);
        }
    }
    let fn_out = |f: FnId| (f.0 as usize >= m.fns.len()).then(|| format!("fn {} out of range", f.0));
    for fl in &m.flows {
        let (fns, ins) = (&fl.fns, fl.params.iter().map(|p| p.1).chain(fl.sig_inputs.iter().map(|p| p.1)));
        let defs = [fns.state, fns.config, fns.params, fns.out].into_iter().find(|&id| def(id).is_none());
        let defs = defs.map(|id| format!("type {} out of range", id.0));
        let tys = out(n, ins.chain(fl.outputs.iter().map(|o| o.1)));
        if let Some(e) = fns.generated().find_map(fn_out).or(defs).or(tys) {
            return fail(&fl.name, Some(fl.name_span), e);
        }
    }
    for mv in &m.moves {
        if let Some(e) = fn_out(mv.fn_).or_else(|| out(n, [mv.ty])) {
            return fail("the copies", Some(mv.span), format!("a copy of {e}"));
        }
    }
    if !m.has_all_facts() {
        return fail("the facts", None, "the facts do not cover the type table".into());
    }
    Ok(())
}

/// The first of `tys` out of a table of `n` types.
fn out(n: usize, tys: impl IntoIterator<Item = CTy>) -> Option<String> {
    tys.into_iter().find(|t| t.index() >= n).map(|t| format!("ty {} out of range", t.index()))
}

impl<'a> V<'a> {
    pub(super) fn local_ty(&self, l: LocalId) -> R<CTy> {
        let f = self.f.ok_or_else(|| self.err(Rule::V20, "local used outside a function"))?;
        f.locals.get(l.0 as usize).map(|x| x.ty).ok_or_else(|| self.err(Rule::V20, "local out of range"))
    }

    pub(super) fn kind(&self, t: CTy) -> R<&'a TyKind> {
        let out = || self.err(Rule::V20, format!("ty {} out of range", t.index()));
        self.m.tys.kinds().get(t.index()).ok_or_else(out)
    }

    /// The table of the types, to ask of `t`, which is in it.
    pub(super) fn tys_of(&self, t: CTy) -> R<&'a Types> {
        self.kind(t).map(|_| &self.m.tys)
    }

    pub(super) fn ty(&self, id: TypeId) -> R<&'a TypeDef> {
        self.m.types.get(id.0 as usize).ok_or_else(|| self.err(Rule::V20, format!("type {} out of range", id.0)))
    }

    /// The variants of the enum type `Enum(id)`, which [`table`] made an enum.
    pub(super) fn variants(&self, id: TypeId) -> R<&'a [(String, Vec<CTy>)]> {
        match &self.ty(id)?.kind {
            TypeDefKind::Enum { variants } => Ok(variants),
            _ => Err(self.err(Rule::V20, format!("an enum type of the type {}, not an enum", id.0))),
        }
    }

    pub(super) fn const_(&self, c: ConstId) -> R<&'a ConstDef> {
        self.m.consts.get(c.0 as usize).ok_or_else(|| self.err(Rule::V20, format!("const {} out of range", c.0)))
    }

    pub(super) fn callee(&self, f: FnId) -> R<&'a FnDef> {
        self.m.fns.get(f.0 as usize).ok_or_else(|| self.err(Rule::V20, "call to an unknown fn"))
    }
}
