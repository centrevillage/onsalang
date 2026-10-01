//! Unification variables for body inference (spec §4.7, T2-5). Variables are
//! interned as `Ty::Var(i)`; a literal variable carries the `IntLit` /
//! `FloatLit` constraint. Array lengths use `Len::Var(i)` bound to a
//! `Ty::ConstVal(n)`.

use crate::ty::{Len, Ty, TyId, Types};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LitKind {
    Int,
    Float,
}

#[derive(Debug, Clone)]
enum VarState {
    Unbound(Option<LitKind>),
    Bound(TyId),
}

#[derive(Debug, Default)]
pub struct Infer {
    vars: Vec<VarState>,
}

/// Why two types did not unify (for messages).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mismatch {
    /// Plain structural mismatch.
    Types,
    /// An integer literal where a non-integer type is required (or vice versa).
    Literal,
}

impl Infer {
    pub fn fresh(&mut self, types: &mut Types, lit: Option<LitKind>) -> TyId {
        let i = self.vars.len() as u32;
        self.vars.push(VarState::Unbound(lit));
        types.intern(Ty::Var(i))
    }

    pub fn fresh_len(&mut self) -> Len {
        let i = self.vars.len() as u32;
        self.vars.push(VarState::Unbound(None));
        Len::Var(i)
    }

    /// Follow bindings at the top level only.
    pub fn shallow(&self, types: &Types, mut ty: TyId) -> TyId {
        loop {
            match types.get(ty) {
                Ty::Var(i) => match &self.vars[*i as usize] {
                    VarState::Bound(t) => ty = *t,
                    VarState::Unbound(_) => return ty,
                },
                _ => return ty,
            }
        }
    }

    /// The literal constraint of an unbound variable, if any.
    pub fn lit_of(&self, types: &Types, ty: TyId) -> Option<LitKind> {
        match types.get(self.shallow(types, ty)) {
            Ty::Var(i) => match &self.vars[*i as usize] {
                VarState::Unbound(l) => *l,
                VarState::Bound(_) => None,
            },
            _ => None,
        }
    }

    pub fn is_unresolved(&self, types: &Types, ty: TyId) -> bool {
        matches!(types.get(self.shallow(types, ty)), Ty::Var(_))
    }

    fn root_var(&self, types: &Types, ty: TyId) -> Option<u32> {
        match types.get(self.shallow(types, ty)) {
            Ty::Var(i) => Some(*i),
            _ => None,
        }
    }

    pub fn shallow_len(&self, types: &Types, len: Len) -> Len {
        let mut len = len;
        loop {
            match len {
                Len::Var(i) => match &self.vars[i as usize] {
                    VarState::Bound(t) => match types.get(*t) {
                        Ty::ConstVal(n) => return Len::Const(*n),
                        Ty::Var(j) => len = Len::Var(*j),
                        _ => return len,
                    },
                    VarState::Unbound(_) => return len,
                },
                other => return other,
            }
        }
    }

    fn occurs(&self, types: &Types, var: u32, ty: TyId) -> bool {
        let ty = self.shallow(types, ty);
        match types.get(ty) {
            Ty::Var(i) => *i == var,
            Ty::Array(e, _) => self.occurs(types, var, *e),
            Ty::Tuple(ts) | Ty::Named(_, ts) | Ty::Builtin(_, ts) => ts.iter().any(|&t| self.occurs(types, var, t)),
            Ty::Fn(f) => f.params.iter().any(|(_, t)| self.occurs(types, var, *t)) || self.occurs(types, var, f.ret),
            _ => false,
        }
    }

    fn bind(&mut self, types: &Types, var: u32, ty: TyId) -> Result<(), Mismatch> {
        let lit = match &self.vars[var as usize] {
            VarState::Unbound(l) => *l,
            VarState::Bound(_) => unreachable!("bind of a bound variable"),
        };
        let ty_s = self.shallow(types, ty);
        match (lit, types.get(ty_s)) {
            (_, Ty::Var(j)) => {
                let j = *j;
                if j == var {
                    return Ok(());
                }
                let other = match &self.vars[j as usize] {
                    VarState::Unbound(l) => *l,
                    VarState::Bound(_) => None,
                };
                let merged = match (lit, other) {
                    (Some(a), Some(b)) if a != b => return Err(Mismatch::Literal),
                    (a, b) => a.or(b),
                };
                self.vars[j as usize] = VarState::Unbound(merged);
            }
            (Some(LitKind::Int), Ty::Int(_)) | (Some(LitKind::Float), Ty::Float(_)) | (None, _) => {}
            (Some(_), Ty::Error) => {}
            (Some(_), _) => return Err(Mismatch::Literal),
        }
        if self.occurs(types, var, ty_s) && !matches!(types.get(ty_s), Ty::Var(_)) {
            return Err(Mismatch::Types);
        }
        self.vars[var as usize] = VarState::Bound(ty_s);
        Ok(())
    }

    fn unify_len(&mut self, types: &mut Types, a: Len, b: Len) -> Result<(), Mismatch> {
        let a = self.shallow_len(types, a);
        let b = self.shallow_len(types, b);
        if a == b {
            return Ok(());
        }
        match (a, b) {
            (Len::Var(i), Len::Const(n)) | (Len::Const(n), Len::Var(i)) => {
                let t = types.intern(Ty::ConstVal(n));
                self.vars[i as usize] = VarState::Bound(t);
                Ok(())
            }
            (Len::Var(i), Len::Var(j)) => {
                let t = types.intern(Ty::Var(j));
                self.vars[i as usize] = VarState::Bound(t);
                Ok(())
            }
            _ => Err(Mismatch::Types),
        }
    }

    /// Unify two types. `Ty::Error` unifies with anything (no cascades).
    pub fn unify(&mut self, types: &mut Types, a: TyId, b: TyId) -> Result<(), Mismatch> {
        let a = self.shallow(types, a);
        let b = self.shallow(types, b);
        if a == b {
            return Ok(());
        }
        let (ta, tb) = (types.get(a).clone(), types.get(b).clone());
        match (&ta, &tb) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),
            (Ty::Var(i), _) => self.bind(types, *i, b),
            (_, Ty::Var(j)) => self.bind(types, *j, a),
            (Ty::Array(e1, l1), Ty::Array(e2, l2)) => {
                self.unify(types, *e1, *e2)?;
                self.unify_len(types, *l1, *l2)
            }
            (Ty::Tuple(xs), Ty::Tuple(ys)) if xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(types, *x, *y)?;
                }
                Ok(())
            }
            (Ty::Named(d1, xs), Ty::Named(d2, ys)) if d1 == d2 && xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(types, *x, *y)?;
                }
                Ok(())
            }
            (Ty::Builtin(b1, xs), Ty::Builtin(b2, ys)) if b1 == b2 && xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(types, *x, *y)?;
                }
                Ok(())
            }
            // `rt` is checked by the rt pass (T2-9); modes and effects are part of the type.
            (Ty::Fn(f1), Ty::Fn(f2)) if f1.params.len() == f2.params.len() && f1.effects == f2.effects => {
                for ((m1, x), (m2, y)) in f1.params.iter().zip(&f2.params) {
                    if m1 != m2 {
                        return Err(Mismatch::Types);
                    }
                    self.unify(types, *x, *y)?;
                }
                self.unify(types, f1.ret, f2.ret)
            }
            (Ty::ConstVal(n), Ty::ConstVal(m)) if n == m => Ok(()),
            _ => Err(Mismatch::Types),
        }
    }

    /// Substitute every bound variable, interning the result.
    pub fn resolve(&self, types: &mut Types, ty: TyId) -> TyId {
        let ty = self.shallow(types, ty);
        match types.get(ty).clone() {
            Ty::Array(e, l) => {
                let e2 = self.resolve(types, e);
                let l2 = self.shallow_len(types, l);
                if e2 == e && l2 == l { ty } else { types.intern(Ty::Array(e2, l2)) }
            }
            Ty::Tuple(ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.resolve(types, t)).collect();
                if ns == ts { ty } else { types.intern(Ty::Tuple(ns)) }
            }
            Ty::Named(d, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.resolve(types, t)).collect();
                if ns == ts { ty } else { types.intern(Ty::Named(d, ns)) }
            }
            Ty::Builtin(b, ts) => {
                let ns: Vec<TyId> = ts.iter().map(|&t| self.resolve(types, t)).collect();
                if ns == ts { ty } else { types.intern(Ty::Builtin(b, ns)) }
            }
            Ty::Fn(f) => {
                let params: Vec<_> = f.params.iter().map(|(m, t)| (*m, self.resolve(types, *t))).collect();
                let ret = self.resolve(types, f.ret);
                if params == f.params && ret == f.ret {
                    ty
                } else {
                    types.intern(Ty::Fn(crate::ty::FnTy { rt: f.rt, params, ret, effects: f.effects }))
                }
            }
            _ => ty,
        }
    }

    /// Whether the resolved type still contains a variable.
    pub fn has_vars(&self, types: &Types, ty: TyId) -> bool {
        let ty = self.shallow(types, ty);
        match types.get(ty) {
            Ty::Var(_) => true,
            Ty::Array(e, l) => self.has_vars(types, *e) || matches!(self.shallow_len(types, *l), Len::Var(_)),
            Ty::Tuple(ts) | Ty::Named(_, ts) | Ty::Builtin(_, ts) => ts.iter().any(|&t| self.has_vars(types, t)),
            Ty::Fn(f) => f.params.iter().any(|(_, t)| self.has_vars(types, *t)) || self.has_vars(types, f.ret),
            _ => false,
        }
    }

    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Whether variable `i` (as a `TyId` of `Ty::Var`) is the same root as `ty`.
    pub fn same_var(&self, types: &Types, a: TyId, b: TyId) -> bool {
        match (self.root_var(types, a), self.root_var(types, b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
}
