//! E0413 for a method a receiver has not (§3.3, §3.4, §4.2): of a method
//! the spec leaves out and gives another form of, the candidate of that
//! form, or a note of the rule where no candidate keeps the promise of
//! §18.1 (the form put there would leave an error).

use onsa_diag::Edit;
use onsa_syntax::ast::{OperandPlace, Vis};

use crate::def::ParamSig;
use crate::lang;

use super::*;
use crate::slot::{Form, Slot, slot_of};

/// What the spec gives instead of a method it leaves out.
#[derive(Debug, Clone, Copy)]
enum Named {
    /// `is_empty` of a type with a length: `len() == 0` (§4.2).
    Length,
    /// What `Option` or `Result` (the row of [`lang`]) leaves to `match`
    /// (§9.1, R-96): on a receiver of that type, a note of what it has and
    /// of the form. No candidate: the arms are the writer's.
    Match(usize, &'static str),
    /// `checked_neg`, of the signed integers: no member of `Int` (S-238).
    SignedOnly,
}

/// The methods the spec leaves out, by name.
const NAMED: &[(&str, Named)] = &[
    ("is_empty", Named::Length),
    ("is_some", Named::Match(lang::OPTION, "match o { Some(_) => true, None => false }")),
    ("is_none", Named::Match(lang::OPTION, "match o { Some(_) => false, None => true }")),
    ("unwrap_or", Named::Match(lang::OPTION, "match o { Some(x) => x, None => d }")),
    ("is_ok", Named::Match(lang::RESULT, "match r { Ok(_) => true, Err(_) => false }")),
    ("is_err", Named::Match(lang::RESULT, "match r { Ok(_) => false, Err(_) => true }")),
    (crate::prim::CHECKED_NEG, Named::SignedOnly),
];

/// The one method of a type with a length (§4.2).
const LEN: &str = "len";

/// The note of an `is_empty` with no candidate.
const LEN_RULE: &str = "a type with a length has `len()` only, and an empty test is `len() == 0` (§4.2)";

/// Where what a read that is not kept leaves in the analysis starts.
pub(super) struct Marks {
    held: bool,
    uses: usize,
}

impl Marks {
    pub(super) fn of(a: &Analysis, def: DefId) -> Marks {
        Marks { held: a.read_held.contains(&def), uses: a.uses.borrow().len() }
    }

    /// Undo it: whether the read read what the check does not read.
    pub(super) fn undo(self, a: &mut Analysis, def: DefId) -> bool {
        a.uses.borrow_mut().truncate(self.uses);
        !self.held && a.read_held.remove(&def)
    }
}

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
        let found = match (NAMED.iter().find(|(n, _)| *n == name.name), self.ty(recv)) {
            (Some((_, Named::Length)), _) if self.has_method(recv, LEN) => {
                Some(self.len_test(e, name, args, expected, kind).ok_or_else(|| LEN_RULE.to_string()))
            }
            (Some(&(_, Named::Match(row, form))), Ty::Named(d, _)) if self.a.modules.lang.is(row, d) => {
                Some(Err(format!("{}; write it with `match`: `{form}` (§9.1)", self.std_methods(d))))
            }
            (Some((_, Named::SignedOnly)), Ty::Param(_)) if self.satisfies(recv, Bound::Int) => Some(Err(format!(
                "`{}` is of the signed integers, no member of `Int`; write `{shown}.ZERO.checked_sub(x)` (§3.4, §6.3)",
                name.name
            ))),
            _ => (self.math_fn(recv, &name.name))
                .map(|f| self.function_form(e, recv, name, args, expected, kind, f))
                .or_else(|| self.method_of_a_trait(recv, &name.name).map(Err)),
        };
        self.diag(match found {
            Some(Ok(fix)) => d.with_fix(fix),
            Some(Err(rule)) => d.with_rule(rule),
            None => d,
        })
    }

    /// The note of the method `name` of a number trait the bounds of the type
    /// parameter `recv` do not give (S-238). No candidate: to narrow the bound
    /// and to take the types it leaves out are two intents.
    fn method_of_a_trait(&self, recv: TyId, name: &str) -> Option<String> {
        let (Ty::Param(_), Some(b)) = (self.ty(recv), crate::traits::member_trait(name)) else { return None };
        let d = crate::traits::member(self.a, &[b], name)?;
        matches!(&self.a.def(d).kind, DefKind::Fn(f) if f.self_mode.is_some())
            .then(|| format!("`{name}` is a method of the values of `{}` (§6.3)", b.name()))
    }

    /// What the enum `d` of std has, by the declarations of std (§9.1).
    fn std_methods(&self, d: DefId) -> String {
        let table = self.a.modules.assoc.get(&d).into_iter().flatten();
        let mut methods: Vec<DefId> =
            table.map(|(_, &m)| m).filter(|&m| self.a.modules.is_std(self.a.def(m).module)).collect();
        methods.sort();
        let names: Vec<String> = methods.iter().map(|&m| format!("`{}`", self.a.def(m).name)).collect();
        format!("`{}` has {} only", self.a.def(d).name, names.join(" and "))
    }

    /// The `pub fn` of `std.math` of the name of the method `name` of a
    /// number or of a type parameter: a computation the spec gives as a
    /// function, not a method (§3.4). The functions are std's declarations.
    fn math_fn(&self, recv: TyId, name: &str) -> Option<DefId> {
        let t = self.ty(recv);
        if !t.is_number() && !matches!(t, Ty::Param(_)) {
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
        if kind != CallKind::Plain
            || expected.is_some_and(|t| !self.may_fit(t, ret))
            || self.place_fits(e, ret).is_none()
        {
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
        if !self.args_fit(args, &f.params[1..], recv, e) {
            return Err(rule);
        }
        Ok(Fix::new(title, edits))
    }

    /// The slot of `e` when a value of the type `c` put there by a candidate
    /// leaves no error of its parent (§18.1); none in an expression
    /// statement (its value is dropped). As a receiver, only of a method `c`
    /// has (in `x.abs().sqrt()` the missing `sqrt` would be the error left);
    /// before `as`, only where `as` converts `c` (§3.3); before `at`, any (the
    /// type of `e at k` is that of `e`, §11.3). In parentheses, the place of
    /// the outermost. The one answer of the candidates of every family.
    pub(super) fn place_fits(&mut self, e: ExprId, c: TyId) -> Option<Slot> {
        let place = slot_of(self.ast, self.root, e)?;
        let parent = place.parent.map(|p| &self.ast.expr(p).kind);
        let fits = match (place.outer, parent) {
            (Slot::Discarded, _) => false,
            (Slot::Operand(OperandPlace::Postfix), Some(ExprKind::Field { name, .. })) => {
                self.has_method(c, &name.name)
            }
            (Slot::Operand(OperandPlace::Postfix), _) => false,
            (Slot::Operand(OperandPlace::AsAtLeft), Some(&ExprKind::Cast { ty, .. })) => {
                // The type after `as`, lowered as its check does, quietly.
                let to = self.quietly(|ck| ck.lower_type_expr(ty));
                let error = |t: TyId| matches!(self.a.types.get(t), Ty::Error);
                to.is_some_and(|to| crate::cast::cast_allowed(&self.a.types, c, to) || error(to))
            }
            _ => true,
        };
        fits.then_some(place.slot)
    }

    /// The edits of `x.f(a, …)` into `f(x, a, …)` (§18.1): `f(` before the
    /// receiver, and `.f(` taken off or made `, `; the `)` stays. A call is a
    /// postfix form, written bare in every place (§3.1).
    fn call_edits(&self, e: ExprId, name: &Ident, args: &[Arg]) -> Option<Vec<Edit>> {
        let ExprKind::Call { callee, .. } = &self.expr(e).kind else { return None };
        // The form with no type arguments after the name alone: the edits are of `.name(`, and a
        // callee with them (`v.m::[I32](x)`) has no candidate.
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
    /// generic parameter ([`crate::names::rename::bound_by`]): a `use` of it
    /// added to the module would make that binding an E0304 (S-79). The set
    /// of the module is made once in the check of the package (the bindings
    /// of this body are in `self.names`).
    fn binds_in_module(&mut self, name: &str) -> bool {
        if !self.bound.contains_key(&self.m) {
            let mut set: HashSet<String> = self.names.bindings.iter().map(|b| b.name.clone()).collect();
            for (i, _) in self.a.defs.iter().enumerate().filter(|(_, d)| d.module == self.m) {
                set.extend(crate::names::rename::bound_by(self.a, DefId(i as u32)).map(String::from));
            }
            self.bound.insert(self.m, set);
        }
        self.bound[&self.m].contains(name)
    }

    /// Whether `args` fit the parameters `params` of a function form at the
    /// receiver's type `recv` (`max(a, 1)` of an `F32` is an E0401).
    fn args_fit(&mut self, args: &[Arg], params: &[ParamSig], recv: TyId, e: ExprId) -> bool {
        let params: Vec<(Mode, TyId)> = params.iter().map(|p| (p.mode, recv)).collect();
        self.quietly(|ck| ck.check_args(args, &params, e)).is_some()
    }

    /// A trial of a candidate: `f` run with no diagnostic. Its `Err` is the
    /// answer "it does not fit", not a failure dropped. What it leaves in
    /// this body stops with the E0413; what leaks out of it (`read_held`,
    /// `uses`) is undone. Of what reads what the check does not, an error is
    /// elsewhere (§18.1): none.
    pub(super) fn quietly<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> Option<T> {
        let (failed, marks) = (self.failed, Marks::of(self.a, self.def));
        self.failed = true;
        let out = f(self);
        self.failed = failed;
        let read_unread = marks.undo(self.a, self.def);
        out.ok().filter(|_| !read_unread)
    }

    /// Whether the builtin type `recv` has the method `name`: of `len`,
    /// whether it is a type with a length (§4.2), as far as this version
    /// gives it `len`. A method of a user type is none.
    fn has_method(&mut self, recv: TyId, name: &str) -> bool {
        self.method_key(recv, name).1.is_none() && self.is_method(recv, name)
    }

    /// Whether `recv` has the method `name`, declared or builtin.
    pub(super) fn is_method(&mut self, recv: TyId, name: &str) -> bool {
        let (key, owner, _) = self.method_key(recv, name);
        let table = match owner {
            Some(d) => self.a.modules.assoc.get(&d),
            None => key.and_then(|k| self.a.modules.assoc_builtin.get(&k)),
        };
        match self.a.modules.assoc_member(table, name) {
            Ok(Some(md)) => matches!(&self.a.def(md).kind, DefKind::Fn(f) if f.self_mode.is_some()),
            Ok(None) => false,
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
        let wrap = self.place_fits(e, bool_)?.wraps(Form::Binary(BinOp::Eq));
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
    /// the kind of `c`, the error type, or the same type of what fits. `c`
    /// has no variable and is a number, `Bool`, a type parameter or an
    /// `Option` of one: this is whether they unify.
    pub(super) fn may_fit(&self, t: TyId, c: TyId) -> bool {
        let t = self.shallow(t);
        match (self.ty(t), self.ty(c)) {
            (Ty::Error, _) => true,
            (Ty::Var(i), c) => match self.infer.var_lit(i) {
                None => true,
                Some(LitKind::Int) => matches!(c, Ty::Int(_)),
                Some(LitKind::Float) => self.infer.float_fits(&c),
            },
            (Ty::Named(a, t), Ty::Named(b, c)) if a == b => t.iter().zip(&c).all(|(&t, &c)| self.may_fit(t, c)),
            _ => t == c,
        }
    }
}
