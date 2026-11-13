//! The help of an E0401 of a function type fit to an expected one that
//! differs from it in the modes of parameters alone, the default on one side
//! and `move` on the other ([`Mismatch::Modes`]): the candidate of S-872 for
//! an anonymous function written as an argument, else the note of S-874
//! (§8.1). Its text is no promise (§18.1).

use onsa_diag::Edit;

use super::*;

/// The form of what was found where a function type is expected, which
/// chooses the help of [`Mismatch::Modes`] (§8.1).
#[derive(Debug, Clone, Copy)]
pub(crate) enum Found<'p> {
    /// A constructor (`Mode.Gain`), written at the span.
    Ctor(Span),
    /// A function item (`conv`, `Calc.bump`, `id::[U32]`), written at the span.
    Item(Span),
    /// An anonymous function, with its parameters when it is written
    /// directly as an argument (the candidate of S-872).
    Closure(Option<&'p [Param]>),
    /// Anything else (a variable, a parameter, a call, a field).
    Other,
}

impl Checker<'_> {
    /// `d`, the E0401 of `actual` where `expected` is expected, which differ
    /// in the modes of the parameters `ps` alone, with its help: the
    /// candidate that adds `move` when an anonymous function written as an
    /// argument has the default where each of them expects `move` (S-872:
    /// the fix leaves no parameter that differs, so the candidates end);
    /// else a note that names `ps` and shows the mending of the form found
    /// (S-874): a wrapping function for a constructor whose elements are
    /// Dup, the declaration or a wrapping function for an item whose
    /// parameters `ps` are Copy (none a function type), the modes to write
    /// for an anonymous function. A wrapping function of anything else would
    /// capture it or take what cannot be copied (§5.2).
    pub(crate) fn modes_help(
        &mut self,
        d: Diagnostic,
        found: Found,
        ps: &[usize],
        (actual, expected): (TyId, TyId),
    ) -> Diagnostic {
        let (Ty::Fn(f), Ty::Fn(g)) = (self.ty(self.shallow(actual)), self.ty(self.shallow(expected))) else {
            onsa_diag::internal::bug(Some(d.span), "the modes of types that are no function types");
        };
        if let Found::Closure(Some(params)) = found {
            let at = |k: usize| match &params[k].name {
                ParamName::Ident(Ident { span, .. }) | ParamName::Wild(span) if g.params[k].0 == Mode::Move => {
                    Some(Edit::insert(span.file, span.start, "move "))
                }
                _ => None,
            };
            if let Some(edits) = ps.iter().map(|&k| at(k)).collect::<Option<Vec<_>>>() {
                return d.with_fix(Fix::new("add `move`", edits));
            }
        }
        let nums: Vec<String> = ps.iter().map(|k| (k + 1).to_string()).collect();
        let which = match nums.split_last() {
            Some((one, [])) => format!("the mode of the parameter {one} differs"),
            Some((last, rest)) => format!("the modes of the parameters {} and {last} differ", rest.join(", ")),
            None => onsa_diag::internal::bug(Some(d.span), "no parameter whose mode differs"),
        };
        let kinds = |me: &Self, ks: &[usize], b: Bound| {
            ks.iter().all(|&k| {
                let t = me.shallow(f.params[k].1);
                !matches!(me.ty(t), Ty::Fn(_)) && me.satisfies(t, b)
            })
        };
        let every: Vec<usize> = (0..f.params.len()).collect();
        let mend = match found {
            Found::Ctor(at) if kinds(self, &every, Bound::Dup) => {
                format!("; wrap the constructor: `{}`", self.wrap(at, &g))
            }
            Found::Item(at) if kinds(self, ps, Bound::Copy) => {
                let name = self.src(at);
                format!("; change the modes in the declaration of `{name}`, or wrap it: `{}`", self.wrap(at, &g))
            }
            Found::Closure(_) => "; write each in the mode expected (`move x` takes the value, `x` borrows it)".into(),
            _ => String::new(),
        };
        d.with_rule(format!("only {which} from the expected type, the default or `move` (§4.1){mend}"))
    }

    /// An anonymous function of the type `g` that calls what is written at
    /// `at` with its parameters (`fn(x) { Mode.Gain(x) }`).
    fn wrap(&self, at: Span, g: &FnTy) -> String {
        let one = g.params.len() == 1;
        let (params, args): (Vec<String>, Vec<String>) = (1..)
            .zip(&g.params)
            .map(|(k, (mode, _))| {
                let x = if one { "x".to_string() } else { format!("x{k}") };
                match mode {
                    Mode::Borrow => (x.clone(), x),
                    Mode::Move => (format!("move {x}"), x),
                    Mode::Inout => (format!("inout {x}"), format!("inout {x}")),
                }
            })
            .unzip();
        format!("fn({}) {{ {}({}) }}", params.join(", "), self.src(at), args.join(", "))
    }
}
