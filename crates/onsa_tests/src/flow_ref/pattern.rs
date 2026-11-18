//! The patterns of the evaluator (§7): `match` (the arms from the top, the guard after the bindings of its arm, only
//! the arm taken is evaluated, §3.5) and the `let` that takes a value apart (§11.2). A pattern matches a value
//! structurally and collects what it binds; the arm or the `let` commits the bindings. The variants are by the
//! number of the table (`pat_ctors`); the fields of a struct and the elements of a variant are read from the type
//! of the value (`Ty::Named`, the table of the types of the expressions), as the fields of a literal are. A `|` is
//! a choice, and with a guard each way a pattern matches is tried, as in Rust, until the guard is true ([`Way`]).

use onsa_diag::Span;
use onsa_sema::{LocalId, Target, Ty, TyId};
use onsa_syntax::ast::{ExprId, ExprKind, Ident, Lit, PatId, PatKind};

use super::expr::{Eval, Frame, Stop};
use super::scalar::Fault;
use super::value::{Env, Value};

type Binds = Vec<(LocalId, Value)>;

/// One way a pattern matches: what it binds, and the choice made at each `|` it met, in the order met (the
/// alternative taken, and how many there are). The ways follow Rust's order: the first `|` moves on last.
#[derive(Default)]
struct Way {
    binds: Binds,
    picks: Vec<(usize, usize)>,
    met: usize,
}

impl Way {
    /// The alternative of the next `|`, which has `n`: the first one, until [`Way::next`] moves on.
    fn pick(&mut self, n: usize) -> usize {
        if self.met == self.picks.len() {
            self.picks.push((0, n));
        }
        self.met += 1;
        self.picks[self.met - 1].0
    }

    /// The way after this one (the last `|` met moves on first), or `false` when there is none.
    fn next(&mut self) -> bool {
        self.binds.clear();
        self.met = 0;
        while let Some((i, n)) = self.picks.last_mut() {
            if *i + 1 < *n {
                *i += 1;
                return true;
            }
            self.picks.pop();
        }
        false
    }
}

/// A literal pattern against a value (a float literal is not a pattern, E0020); `neg` is the `-` before it.
fn literal(lit: &Lit, neg: bool, v: &Value) -> Result<bool, Fault> {
    Ok(match (lit, v) {
        (Lit::Int { value, .. }, Value::Int(_, n, _)) => {
            *n == if neg { -i128::from(*value) } else { i128::from(*value) }
        }
        (Lit::Bool(b), Value::Bool(c)) => b == c,
        (Lit::Char(a), Value::Char(c)) => a == c,
        (Lit::Str(_), _) => return Err(Fault::Unavailable("a string pattern")),
        _ => return Err(Fault::Internal("a literal pattern that is not of the type of the value")),
    })
}

impl<'a> Frame<'a> {
    /// `let pat = v` of the type `ty`: the pattern is irrefutable (the checker), so it matches. `let _ = e`
    /// evaluates `e` and drops it.
    pub(super) fn destructure(&mut self, pat: PatId, v: &Value, ty: &'a Ty) -> Result<(), Stop> {
        let at = self.body.ast.pat(pat).span;
        if !self.arm(pat, v, ty, None, at)? {
            return Err(Stop { fault: Fault::Internal("a pattern of a `let` that does not match"), at });
        }
        Ok(())
    }

    /// `match`: the first arm whose pattern matches and whose guard (with the bindings of the arm) is true.
    #[inline(never)]
    pub(super) fn select(&mut self, e: ExprId, at: Span) -> Eval {
        let ExprKind::Match { scrutinee, arms, .. } = &self.body.ast.expr(e).kind else {
            return Err(Stop { fault: Fault::Internal("not a match"), at });
        };
        let v = self.eval(*scrutinee)?;
        let ty = self.body.ty(*scrutinee).map_err(|fault| Stop { fault, at })?;
        for arm in arms {
            if self.arm(arm.pat, &v, ty, arm.guard, at)? {
                return self.eval(arm.body);
            }
        }
        Err(Stop { fault: Fault::Internal("no arm of a match is taken"), at })
    }

    /// Does `v` match `pat` in a way `guard` accepts? The ways come in Rust's order, and the bindings of each are put
    /// to the locals before the guard reads them (the ones of a way the guard refuses are written over by the next).
    pub(super) fn arm(
        &mut self,
        pat: PatId,
        v: &Value,
        ty: &'a Ty,
        guard: Option<ExprId>,
        at: Span,
    ) -> Result<bool, Stop> {
        let mut way = Way::default();
        loop {
            if self.matches(pat, v, ty, None, &mut way)? {
                self.locals.extend(way.binds.drain(..));
                if guard.map_or(Ok(true), |g| self.truth(g, at))? {
                    return Ok(true);
                }
            }
            if !way.next() {
                return Ok(false);
            }
        }
    }

    /// Does `v`, of the type `ty` (read under `env`), match `p` in the way `way` goes? What it binds is pushed to `way`.
    fn matches(&mut self, p: PatId, v: &Value, ty: &'a Ty, env: Option<&Env>, way: &mut Way) -> Result<bool, Stop> {
        let ast = self.body.ast;
        let here = |fault| Stop { fault, at: ast.pat(p).span };
        let (ty, env) = Env::follow(self.body.view, ty, env);
        Ok(match (&ast.pat(p).kind, v) {
            (PatKind::Wild, _) => true,
            (PatKind::Bind(_), _) => {
                way.binds.push((self.body.pat_local(p).map_err(here)?, v.clone()));
                true
            }
            (PatKind::Lit(l), _) => literal(l, false, v).map_err(here)?,
            (PatKind::Neg(l), _) => literal(l, true, v).map_err(here)?,
            (PatKind::Path(_), Value::Enum { tag, .. }) if self.body.is_ctor(p) => {
                self.body.pat_ctor(p).map_err(here)? == *tag
            }
            (PatKind::Path(_), _) => self.is_const(p, v)?,
            (PatKind::TupleStruct { elems, .. }, Value::Enum { tag, fields }) => {
                if self.body.pat_ctor(p).map_err(here)? != *tag {
                    return Ok(false);
                }
                let Ty::Named(def, args) = ty else {
                    return Err(here(Fault::Internal("a variant of what is not an enum")));
                };
                let variants = self.body.view.variants(*def).map_err(here)?;
                let Some(variant) = variants.get(*tag as usize) else {
                    return Err(here(Fault::Internal("a variant that is not there")));
                };
                self.each(elems, fields, &variant.fields, Some(&Env { args, outer: env }), way)?
            }
            (PatKind::Tuple(ps), Value::Tuple(vs, _)) => {
                let Ty::Tuple(ts) = ty else {
                    return Err(here(Fault::Internal("a tuple pattern on what is not a tuple")));
                };
                self.each(ps, vs, ts, env, way)?
            }
            (PatKind::Tuple(ps), Value::Unit) => ps.is_empty(),
            (PatKind::Struct { fields, .. }, Value::Struct(vs)) => self.named(p, fields, vs, ty, env, way)?,
            (PatKind::Or(ps), _) => self.matches(ps[way.pick(ps.len())], v, ty, env, way)?,
            _ => return Err(here(Fault::Internal("a pattern that is not of the type of the value"))),
        })
    }

    /// The patterns against the values of the same places, which have the types `ts` (read under `env`).
    #[inline(never)]
    fn each(
        &mut self,
        ps: &[PatId],
        vs: &[Value],
        ts: &[TyId],
        env: Option<&Env>,
        way: &mut Way,
    ) -> Result<bool, Stop> {
        let mut ok = ps.len() == vs.len() && ts.len() == vs.len();
        for ((q, w), t) in ps.iter().zip(vs).zip(ts) {
            ok = ok && self.matches(*q, w, self.body.view.ty(*t), env, way)?;
        }
        Ok(ok)
    }

    /// `Item { x: a, _ }`: the fields named, by the declaration of the struct `ty` is; the rest is not looked at.
    #[inline(never)]
    fn named(
        &mut self,
        p: PatId,
        fields: &[(Ident, PatId)],
        vs: &[Value],
        ty: &'a Ty,
        env: Option<&Env>,
        way: &mut Way,
    ) -> Result<bool, Stop> {
        let ast = self.body.ast;
        let here = |fault| Stop { fault, at: ast.pat(p).span };
        let Ty::Named(def, args) = ty else {
            return Err(here(Fault::Internal("a struct pattern on what is not a struct")));
        };
        let decl = self.body.view.struct_fields(*def).map_err(here)?;
        let env = Env { args, outer: env };
        let mut ok = decl.len() == vs.len();
        for (name, q) in fields {
            let place = decl.iter().position(|f| f.name == name.name).filter(|i| *i < vs.len());
            let i = place.ok_or(here(Fault::Internal("a field the struct has not")))?;
            ok = ok && self.matches(*q, &vs[i], self.body.view.ty(decl[i].ty), Some(&env), way)?;
        }
        Ok(ok)
    }

    /// A constant as a pattern: `v == LIMIT` (§7).
    #[inline(never)]
    fn is_const(&mut self, p: PatId, v: &Value) -> Result<bool, Stop> {
        let at = self.body.ast.pat(p).span;
        let here = |fault| Stop { fault, at };
        let Target::Const { def, .. } = self.body.pat_const(p).map_err(here)? else {
            return Err(here(Fault::Internal("a path pattern that is not a constant")));
        };
        let (body, init) = self.body.view.const_init(*def).map_err(here)?;
        let ty = body.ty(init).map_err(here)?;
        Ok(self.const_def(*def, ty, at)?.same(v))
    }
}
