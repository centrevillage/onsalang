//! E0413 for a method a receiver has not (§3.3, §3.4, §4.2): of a method
//! the spec leaves out and gives another form of, the candidate of that
//! form, or a note of the rule where no candidate keeps the promise of
//! §18.1 (the form put there would leave an error).

use onsa_diag::Edit;
use onsa_syntax::ast::{OperandPlace, Vis};

use crate::def::ParamSig;

use super::slot::{Form, Slot, slot_of};
use super::*;

/// What the spec gives instead of a method it leaves out.
#[derive(Debug, Clone, Copy)]
enum Named {
    /// `is_empty` of a type with a length: `len() == 0` (§4.2).
    Length,
}

/// The methods the spec leaves out, by name.
const NAMED: &[(&str, Named)] = &[("is_empty", Named::Length)];

/// The one method of a type with a length (§4.2).
const LEN: &str = "len";

/// The note of an `is_empty` with no candidate.
const LEN_RULE: &str = "a type with a length has `len()` only, and an empty test is `len() == 0` (§4.2)";

impl<'a> Checker<'a> {
    /// E0413 for the method `name` that `recv` has not, called by `e` with
    /// `args`, where the type `expected` is expected (§4.7).
    pub(super) fn removed_method(
        &mut self,
        e: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> Stop {
        let shown = self.display(recv);
        let message = format!("`{shown}` has no method `{}`", name.name);
        let d = Diagnostic::new(Stage::Types, Code::E0413, name.span, message).with_found(self.src(name.span));
        // The family of the name: its candidate, or the rule of its note.
        let found = match NAMED.iter().find(|(n, _)| *n == name.name) {
            Some((_, Named::Length)) if self.has_method(recv, LEN) => {
                Some(self.len_test(e, name, args, expected, kind).ok_or_else(|| LEN_RULE.to_string()))
            }
            _ => self.math_fn(recv, &name.name).map(|f| self.function_form(e, recv, name, args, expected, kind, f)),
        };
        self.diag(match found {
            Some(Ok(fix)) => d.with_fix(fix),
            Some(Err(rule)) => d.with_rule(rule),
            None => d,
        })
    }

    /// The `pub fn` of `std.math` of the name of the method `name` of a
    /// number or of a type parameter: a computation the spec gives as a
    /// function, not a method (§3.4). The functions are std's declarations.
    fn math_fn(&self, recv: TyId, name: &str) -> Option<DefId> {
        if !matches!(self.ty(recv), Ty::Int(_) | Ty::Float(_) | Ty::Param(_)) {
            return None;
        }
        let d = *self.a.modules.get(crate::prim::math_module(self.a)?).items.get(name)?;
        let def = self.a.def(d);
        (def.vis == Vis::Pub && matches!(&def.kind, DefKind::Fn(f) if f.self_mode.is_none())).then_some(d)
    }

    /// The candidate `f(x, …)` of `x.f(…)`, where `f` is the function `d`
    /// of `std.math` (§3.4), with the `use` of `f` added where the name is
    /// free; else the rule of the note. None of another form of the call,
    /// of an expression statement, where its type cannot be, of a name taken
    /// in the module, or of arguments that do not fit (§18.1).
    #[allow(clippy::too_many_arguments)]
    fn function_form(
        &mut self,
        e: ExprId,
        recv: TyId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
        d: DefId,
    ) -> Result<Fix, String> {
        let def = self.a.def(d).clone();
        let path = format!("{}.{}", self.a.modules.abs_path(self.m, def.module).join("."), def.name);
        let rule = format!("the computation is the function `{path}`; integers and floats have no method form (§3.4)");
        // The form `f[T: …](x: T, …)`, which takes the receiver first.
        let DefKind::Fn(f) = &def.kind else { return Err(rule) };
        let ([GenericDef { name: t, kind: GenericKind::Type { bounds, .. }, .. }], true) =
            (&f.generics[..], f.params.len() == 1 + args.len())
        else {
            return Err(rule);
        };
        if !f.params.iter().all(|p| matches!(self.ty(p.ty), Ty::Param(0))) {
            return Err(rule);
        }
        if bounds.iter().any(|&b| !self.satisfies(recv, b)) {
            let bounds: Vec<&str> = bounds.iter().map(|b| b.name()).collect();
            let shown = self.display(recv);
            return Err(format!(
                "`{path}` takes `{t}: {}`, which `{shown}` does not satisfy; integers and floats have no method form (§3.4)",
                bounds.join(" + ")
            ));
        }
        let ret = self.a.types.subst(f.ret, &[recv]);
        if kind != CallKind::Plain || expected.is_some_and(|t| !self.may_fit(t, ret)) || !self.form_fits(e, ret) {
            return Err(rule);
        }
        let Some(mut edits) = self.call_edits(e, name, args) else { return Err(rule) };
        let mut title = format!("call `{path}`");
        match self.a.modules.lookup(self.m, &def.name, &self.a.prelude) {
            Some(Entity::Def(x)) if x == d => {}
            Some(_) => return Err(rule),
            None => {
                let added = (!self.binds_in_module(&def.name))
                    .then(|| self.a.modules.std_use(self.m, (d, &def), &self.a.prelude))
                    .flatten();
                let Some((added, edit)) = added else { return Err(rule) };
                title.push_str(&format!(" and add `use {added}`"));
                edits.push(edit);
            }
        }
        if !self.args_fit(args, &f.params[1..], recv, self.expr(e).span) {
            return Err(rule);
        }
        Ok(Fix::new(title, edits))
    }

    /// Whether a call of the type `ret` in the place of `e` leaves no error
    /// there (§18.1): none in an expression statement (its value is
    /// dropped), and as a receiver only of a method `ret` has (in
    /// `x.abs().sqrt()` the missing `sqrt` would be the error left).
    fn form_fits(&mut self, e: ExprId, ret: TyId) -> bool {
        match slot_of(self.ast, self.root, e) {
            None | Some((Slot::Discarded, _)) => false,
            Some((Slot::Operand(OperandPlace::Postfix), parent)) => match parent.map(|p| &self.expr(p).kind) {
                Some(ExprKind::Field { name, .. }) => {
                    let name = name.name.clone();
                    self.has_method(ret, &name)
                }
                _ => false,
            },
            Some(_) => true,
        }
    }

    /// The edits of `x.f(a, …)` into `f(x, a, …)` (§18.1): `f(` before the
    /// receiver, and `.f(` taken off or made `, `; the `)` stays. A call is a
    /// postfix form, written bare in every place (§3.1).
    fn call_edits(&self, e: ExprId, name: &Ident, args: &[Arg]) -> Option<Vec<Edit>> {
        let ExprKind::Call { callee, .. } = &self.expr(e).kind else { return None };
        let ExprKind::Field { base, .. } = &self.expr(*callee).kind else { return None };
        let at = self.expr(*base).span;
        let (dot, open) = (name.span.start.checked_sub(1)?, name.span.end);
        let bytes = self.text.as_bytes();
        if bytes.get(dot as usize) != Some(&b'.') || bytes.get(open as usize) != Some(&b'(') {
            return None;
        }
        let call = Span::new(at.file, dot, open + 1);
        let gone = match args.is_empty() {
            true => Edit::delete(call),
            false => Edit::replace(call, ", "),
        };
        Some(vec![Edit::insert(at.file, at.start, format!("{}(", name.name)), gone])
    }

    /// Whether a declaration of this module binds `name` in its body or as a
    /// generic parameter (§5.1), as `names/rename.rs` reads them: a `use` of
    /// it added to the module would make that binding an E0304 (S-79). The
    /// bindings of this body are in `self.names`.
    fn binds_in_module(&self, name: &str) -> bool {
        let binds = |n: &BodyNames| n.bindings.iter().any(|b| b.name == name);
        binds(&self.names)
            || (self.a.defs.iter().enumerate()).filter(|(_, d)| d.module == self.m).any(|(i, d)| {
                d.generics().iter().any(|g| g.name == name) || self.a.names.get(&DefId(i as u32)).is_some_and(binds)
            })
    }

    /// Whether `args` fit the parameters `params` of a function form at the
    /// receiver's type `recv`: a trial check with no diagnostic. Its `Err`
    /// is the answer "they do not" (`max(a, 1)` of an `F32` is an E0401),
    /// not a failure dropped. What it leaves in this body stops with the
    /// E0413; what leaks out of it (`read_held`, `uses`) is undone. Of an
    /// argument that reads what the check does not, an error is elsewhere
    /// (§18.1): no fit.
    fn args_fit(&mut self, args: &[Arg], params: &[ParamSig], recv: TyId, span: Span) -> bool {
        let params: Vec<(Mode, TyId)> = params.iter().map(|p| (p.mode, recv)).collect();
        let (failed, held, uses) = (self.failed, self.a.read_held.contains(&self.def), self.a.uses.borrow().len());
        self.failed = true;
        let fits = self.check_args(args, &params, span).is_ok();
        self.failed = failed;
        self.a.uses.borrow_mut().truncate(uses);
        let read_unread = !held && self.a.read_held.remove(&self.def);
        fits && !read_unread
    }

    /// Whether the builtin type `recv` has the method `name`: of `len`,
    /// whether it is a type with a length (§4.2), as far as this version
    /// gives it `len`. A method of a user type is none.
    fn has_method(&mut self, recv: TyId, name: &str) -> bool {
        let (key, owner, _) = self.method_key(recv, name);
        if owner.is_some() {
            return false;
        }
        let table = key.and_then(|k| self.a.modules.assoc_builtin.get(&k));
        match self.a.modules.assoc_member(table, name) {
            Ok(Some(md)) => matches!(&self.a.def(md).kind, DefKind::Fn(f) if f.self_mode.is_some()),
            Ok(None) => builtin::method(&mut self.a.types, recv, name).is_some(),
            // Two declarations clash on it: no method a candidate can call.
            Err(_) => false,
        }
    }

    /// The candidate `….len() == 0` of `….is_empty()`: none of another form
    /// of the call, of an expression statement (its value is dropped), or
    /// where a `Bool` cannot be.
    fn len_test(
        &mut self,
        e: ExprId,
        name: &Ident,
        args: &[Arg],
        expected: Option<TyId>,
        kind: CallKind,
    ) -> Option<Fix> {
        let bool_ = self.bool_();
        if kind != CallKind::Plain || !args.is_empty() || expected.is_some_and(|t| !self.may_fit(t, bool_)) {
            return None;
        }
        // A `Bool` has no member and no `as` (§6.3, §3.3): in the place of a
        // receiver or before `as` and `at`, the form leaves an error.
        let wrap = match slot_of(self.ast, self.root, e)?.0 {
            Slot::Discarded | Slot::Operand(OperandPlace::Postfix | OperandPlace::AsAtLeft) => return None,
            slot => slot.wraps(Form::Binary(BinOp::Eq)),
        };
        let span = self.expr(e).span;
        let close = if wrap { ")" } else { "" };
        let mut edits = vec![
            Edit::replace(name.span, LEN),
            Edit::insert(span.file, span.end, format!(" {} 0{close}", BinOp::Eq.symbol())),
        ];
        if wrap {
            edits.insert(0, Edit::insert(span.file, span.start, "("));
        }
        Some(Fix::new("test `len() == 0`", edits))
    }

    /// Whether a value of the type `c` may be where the type `t` is expected
    /// (§4.7): `t` is `c`, a variable not of a literal or of a literal of
    /// the kind of `c`, or the error type. `c` has no parts (a number,
    /// `Bool`, a type parameter): this is whether they unify.
    fn may_fit(&self, t: TyId, c: TyId) -> bool {
        let t = self.shallow(t);
        match (self.ty(t), self.ty(c)) {
            (Ty::Error, _) => true,
            (Ty::Var(i), c) => match self.infer.var_lit(i) {
                None => true,
                Some(LitKind::Int) => matches!(c, Ty::Int(_)),
                Some(LitKind::Float) => matches!(c, Ty::Float(_)),
            },
            _ => t == c,
        }
    }
}
