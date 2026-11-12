//! The fields of a struct pattern against its declaration (spec §7, §4.4;
//! S-109, S-366): the one check of a struct pattern, for the bodies and the
//! flows. A pattern names every field once, or ends in a `_` that ignores the
//! fields it does not name, the ones not visible here too (S-903); a `_` that
//! ignores nothing is E0410. The rest `..` of other languages is E0020 here,
//! where the fields are known, and its candidate writes the remaining ones
//! with `_`, or the last `_` when one of them is not visible. The last `...`
//! of a struct literal is judged here too ([`Checker::literal_rest`], §4.4,
//! S-697).
//!
//! The order of the errors is the order of reading: the fields as written,
//! each name checked and then its sub-pattern (through the caller), and the
//! fields that are missing (or the rest) last. An inner pattern's error is
//! so reported before an outer one's `..`.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Ident, PatId, Path, RestMark, StructRest};
use onsa_syntax::foreign::{self, RowId};

use crate::body::{Checker, R, Stop};
use crate::def::{DefId, DefKind, FieldDef, Fields};
use crate::resolve::{Entity, Owner};
use crate::ty::{Ty, TyId};

/// What names the fields of a struct (`Checker::whole_reach`).
#[derive(Clone, Copy)]
pub(crate) enum Whole {
    /// With or without the last `...`.
    Literal {
        filled: bool,
    },
    Pattern,
}

/// What the caller does with a written field: its pattern, the type it
/// matches and its index in the declaration. A field that a struct whose
/// unit failed in the syntax stage may have has the error type and no index
/// (S-260).
pub(crate) type SubPattern<'s, 'a> = &'s mut dyn FnMut(&mut Checker<'a>, PatId, TyId, Option<usize>) -> R<()>;

/// A struct pattern as written: `path { fields, rest }`.
pub(crate) struct Written<'p> {
    pub pat: PatId,
    pub path: &'p Path,
    pub fields: &'p [(Ident, PatId)],
    pub rest: Option<StructRest>,
}

impl<'a> Checker<'a> {
    /// The struct pattern `written` of type `ty` at `span`:
    /// the struct is resolved and unified with `ty`, each written field is
    /// checked and given to `sub`, in the order written, and the number of
    /// the declared fields is returned. The diagnostics are of `stage`.
    /// An alias of the error type is no struct here: its path has no record
    /// (S-728, `names/body/paths.rs`).
    pub(crate) fn struct_pattern(
        &mut self,
        stage: Stage,
        span: Span,
        ty: TyId,
        written: Written<'_>,
        sub: SubPattern<'_, 'a>,
    ) -> R<usize> {
        let Written { pat, path, fields, rest } = written;
        let (entity, owner) = self.ctor_of(pat)?;
        let d = match entity {
            Entity::Def(d) | Entity::Member(d) if matches!(self.a.def(d).kind, DefKind::Struct(_)) => d,
            _ => return Err(self.pattern_err(stage, Code::E0401, path.span, "a struct pattern needs a struct")),
        };
        let Some(sd) = self.a.def(d).as_struct() else {
            return Err(self.pattern_err(stage, Code::E0401, path.span, "a struct pattern needs a struct"));
        };
        let Fields::Named(defs) = sd.fields.clone() else {
            return Err(self.pattern_err(stage, Code::E0410, path.span, "this struct has no named fields"));
        };
        let name = self.a.def(d).name.clone();
        let args = self.fresh_args(d);
        self.of_owner(d, &args, owner, span)?;
        let named = self.a.types.intern(Ty::Named(d, args.clone()));
        self.unify_at(span, named, ty)?;
        // SPEC-GAP(S-260): as for the fields of a struct literal.
        let failed = self.a.partly_read(d);
        let written: Vec<&Ident> = fields.iter().map(|(f, _)| f).collect();
        match rest {
            Some(_) => self.written_reach(d, &defs, &written)?,
            None => self.whole_reach(d, &defs, &written, path.span, Whole::Pattern)?,
        }
        let mut seen: Vec<&str> = Vec::new();
        for (field, fp) in fields {
            let Some(i) = defs.iter().position(|f| f.name == field.name) else {
                if failed {
                    let error = self.a.types.error();
                    sub(self, *fp, error, None)?;
                    continue;
                }
                let msg = format!("`{name}` has no field `{}`", field.name);
                return Err(self.pattern_err(stage, Code::E0410, field.span, msg));
            };
            if seen.contains(&field.name.as_str()) {
                let msg = format!("field `{}` is given twice", field.name);
                return Err(self.pattern_err(stage, Code::E0410, field.span, msg));
            }
            seen.push(&field.name);
            self.a.note_use(defs[i].span, field.span);
            let ft = self.a.types.subst(defs[i].ty, &args);
            sub(self, *fp, ft, Some(i))?;
        }
        if failed {
            return Ok(defs.len());
        }
        let missing: Vec<&FieldDef> = defs.iter().filter(|f| !seen.contains(&f.name.as_str())).collect();
        match rest {
            // The last `_` ignores what is left (§7, S-903).
            Some(StructRest { mark: RestMark::Underscore, .. }) if !missing.is_empty() => Ok(defs.len()),
            Some(rest @ StructRest { mark: RestMark::Underscore, .. }) => {
                let msg = format!("every field of `{name}` is written: the `_` ignores nothing");
                let diag = Diagnostic::new(stage, Code::E0410, rest.span, msg)
                    .with_found(self.src(rest.span))
                    .with_fix(rest_removal(rest));
                Err(self.diag(diag))
            }
            // `..`: the remaining fields with `_`, in the order of the
            // declaration, or the last `_` when one is not visible here; none
            // left, the `, ..` goes (§7, S-109, S-903).
            Some(rest) => {
                let fix = if missing.is_empty() {
                    rest_removal(rest)
                } else if missing.iter().any(|f| !self.field_visible(d, f)) {
                    let mark = RestMark::Underscore.text();
                    Fix::new("ignore the remaining fields with `_`", vec![Edit::replace(rest.span, mark)])
                } else {
                    let list = missing.iter().map(|f| format!("{}: _", f.name)).collect::<Vec<_>>().join(", ");
                    Fix::new("write the remaining fields with `_`", vec![Edit::replace(rest.span, list)])
                };
                let mut d = foreign::report(RowId::StructPatternRest, self.text, rest.span, vec![fix]);
                d.stage = stage;
                Err(self.diag(d))
            }
            // The fields left are visible here: a field not visible that the
            // pattern leaves out is the E0303 above (§15.1, §7, S-366).
            None if !missing.is_empty() => {
                let names = missing.iter().map(|f| format!("`{}`", f.name)).collect::<Vec<_>>().join(", ");
                let msg = format!("struct patterns name every field; missing {names} (use `_`, §7)");
                Err(self.diag(Diagnostic::new(stage, Code::E0410, span, msg).with_found(self.src(span))))
            }
            None => Ok(defs.len()),
        }
    }

    /// Whether the field `field` of the struct `d` is visible in this module
    /// (§15.1, S-35): its visibility (the struct's, or `priv`) from the
    /// module of the struct.
    pub(crate) fn field_visible(&self, d: DefId, field: &FieldDef) -> bool {
        self.a.modules.visible(field.vis, self.a.def(d).module, self.m)
    }

    /// The field `field` of the struct `d` written at `at` (read, written, in
    /// a struct literal or a pattern): an E0303, of the names stage, when it
    /// is not visible here (§15.1, S-35).
    pub(crate) fn field_reach(&mut self, d: DefId, field: &FieldDef, at: Span) -> R<()> {
        if self.field_visible(d, field) {
            return Ok(());
        }
        let def = self.a.def(d);
        let why = self.a.modules.hidden_why(field.vis, Some((Owner::Struct, def)), self.m);
        let msg = format!("the field `{}` of `{}` is not visible here: {why}", field.name, def.name);
        let d = Diagnostic::new(Stage::Names, Code::E0303, at, msg)
            .with_found(self.src(at))
            .with_note(field.span, "defined here");
        Err(self.diag(d))
    }

    /// The fields `written` of a struct literal or a struct pattern (`whole`)
    /// of the struct `d` with the fields `defs`, at `path`: an E0303 when one
    /// is not visible here, before the other errors of the literal or the
    /// pattern, which are of a later stage (§18.1). The first written field
    /// not visible is the E0303 of [`Self::written_reach`]; else one left out
    /// is an E0303 at the name of the struct (§15.1, §7, S-35, S-366): here
    /// the struct is made, and its fields read, by the functions of its
    /// module. A pattern with a rest leaves fields out freely, and has
    /// [`Self::written_reach`] alone; the `...` of a literal leaves out those
    /// with a default, visible or not (§15.1), which the note of the E0303
    /// shows when it would fill all that is left.
    pub(crate) fn whole_reach(
        &mut self,
        d: DefId,
        defs: &[FieldDef],
        written: &[&Ident],
        path: Span,
        whole: Whole,
    ) -> R<()> {
        self.written_reach(d, defs, written)?;
        let left_out = |f: &&FieldDef| !written.iter().any(|w| w.name == f.name);
        let unfilled = |f: &&FieldDef| !matches!(whole, Whole::Literal { filled: true }) || f.default.is_none();
        let hidden = defs.iter().filter(left_out).filter(unfilled).find(|f| !self.field_visible(d, f));
        let Some(f) = hidden else {
            return Ok(());
        };
        let def = self.a.def(d);
        let why = self.a.modules.hidden_why(f.vis, Some((Owner::Struct, def)), self.m);
        let (form, through) = match whole {
            Whole::Literal { filled: false } if defs.iter().filter(left_out).all(|f| f.default.is_some()) => {
                ("made by a struct literal", format!("the fields left out have defaults: {FILL_NOTE}"))
            }
            Whole::Literal { .. } => {
                ("made by a struct literal", format!("`{}` is made by a function of its module", def.name))
            }
            Whole::Pattern => {
                let through = "its fields are read through the functions of its module, or ignored by a last `_`";
                ("taken apart by a struct pattern", through.into())
            }
        };
        let msg = format!("`{}` is not {form} here, as its field `{}` is not visible: {why}", def.name, f.name);
        let note = format!("the field `{}`, not visible here: {through}", f.name);
        let diag =
            Diagnostic::new(Stage::Names, Code::E0303, path, msg).with_found(self.src(path)).with_note(f.span, note);
        Err(self.diag(diag))
    }

    /// The end of the check of a struct literal of `d` with the fields `defs`,
    /// at `path`, that wrote the fields `seen` and ends in `rest` or not
    /// (§4.4, S-697): `...` fills the fields left with their defaults and has
    /// something to fill, and a literal with no `...` names every field.
    pub(crate) fn literal_rest(
        &mut self,
        d: DefId,
        (defs, seen): (&[FieldDef], &[&str]),
        rest: Option<StructRest>,
        path: Span,
    ) -> R<()> {
        let shown = &self.a.def(d).name;
        let list = |left: &[&FieldDef]| left.iter().map(|f| format!("`{}`", f.name)).collect::<Vec<_>>().join(", ");
        let missing: Vec<&FieldDef> = defs.iter().filter(|f| !seen.contains(&f.name.as_str())).collect();
        let bare: Vec<&FieldDef> = missing.iter().copied().filter(|f| f.default.is_none()).collect();
        let e0410 = |at, msg| Diagnostic::new(Stage::Types, Code::E0410, at, msg).with_found(self.src(at));
        let diag = match rest {
            None if missing.is_empty() => return Ok(()),
            Some(_) if !missing.is_empty() && bare.is_empty() => return Ok(()),
            Some(rest) if missing.is_empty() => {
                let msg = format!("every field of `{shown}` is written: the `...` fills nothing");
                e0410(rest.span, msg).with_fix(rest_removal(rest))
            }
            Some(_) => {
                let names = list(&bare);
                e0410(path, format!("missing field(s) {names} of `{shown}`: they have no default to fill (§4.4)"))
            }
            None => {
                let names = list(&missing);
                let msg = format!("missing field(s) {names} of `{shown}`; struct literals name every field (§4.4)");
                match bare.is_empty() {
                    true => e0410(path, msg).with_note(missing[0].span, format!("these have defaults: {FILL_NOTE}")),
                    false => e0410(path, msg),
                }
            }
        };
        Err(self.diag(diag))
    }

    /// The first of the fields `written` of the struct `d` that is not visible
    /// here: the E0303 of [`Self::field_reach`].
    fn written_reach(&mut self, d: DefId, defs: &[FieldDef], written: &[&Ident]) -> R<()> {
        for w in written {
            if let Some(f) = defs.iter().find(|f| f.name == w.name && !self.field_visible(d, f)) {
                return self.field_reach(d, f, w.span);
            }
        }
        Ok(())
    }

    fn pattern_err(&mut self, stage: Stage, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(stage, code, span, msg).with_found(self.src(span)))
    }
}

/// What a note says of a literal that leaves out fields with defaults alone:
/// no candidate, as the writer may have meant to write them (§4.4).
const FILL_NOTE: &str = "a last `...` fills them (§4.4)";

/// The candidate that takes off a rest with no field left for it.
fn rest_removal(rest: StructRest) -> Fix {
    let mark = rest.mark.text();
    // A title is one line: the removal may hold newlines.
    let comma = if rest.removal.start < rest.span.start { ", " } else { "" };
    Fix::new(format!("remove `{comma}{mark}`"), vec![Edit::delete(rest.removal)])
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    use crate::tests::analyze;
    use crate::{Module, Package};

    /// The code, the text and the start of the one diagnostic of `src`.
    fn first(src: &str) -> (Code, String, usize) {
        let modules =
            vec![Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src))];
        let a = analyze(&Package::new("t", modules, vec![crate::tests::std_package()]));
        assert_eq!(a.diagnostics.len(), 1, "{:?}", a.diagnostics);
        let d = &a.diagnostics[0];
        let (from, to) = (d.span.start as usize, d.span.end as usize);
        (d.code, src[from..to].to_string(), from)
    }

    /// A `match` on `p` (or on `w`) with one arm, whose pattern binds no
    /// name: a binding not read is an E0309 (§5.1, S-129).
    fn arm(pattern: &str) -> String {
        format!(
            "pub struct P {{\n  x: I32,\n  y: I32,\n}}\n\npub struct W {{\n  p: P,\n  k: I32,\n}}\n\n\
             pub fn f(p: P, w: W) -> I32 {{\n  match {} {{\n    {pattern} => 1,\n  }}\n}}\n",
            if pattern.starts_with('W') { "w" } else { "p" }
        )
    }

    #[test]
    fn the_errors_are_in_the_order_of_reading() {
        let code_text = |p: &str| {
            let (c, t, _) = first(&arm(p));
            (c, t)
        };
        // A field's sub-pattern before the fields that are missing.
        assert_eq!(code_text("P { x: Nope }"), (Code::E0302, "Nope".into()));
        assert_eq!(code_text("P { x: \"s\" }").0, Code::E0401);
        // The fields as written: a sub-pattern before a later unknown field.
        assert_eq!(code_text("P { x: Some(_), w: _ }").0, Code::E0401);
        // An unknown field before a later sub-pattern (of the types stage: a
        // name not found is the names stage's, before them all, §18.1).
        assert_eq!(code_text("P { w: _, x: \"s\" }"), (Code::E0410, "w".into()));
        assert_eq!(code_text("P { w: _, x: Nope }"), (Code::E0302, "Nope".into()));
        // The missing fields last.
        assert_eq!(code_text("P { x: _ }").0, Code::E0410);
        // An inner `..` before the outer one.
        let src = arm("W { p: P { x: _, .. }, .. }");
        let (code, text, at) = first(&src);
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
        assert!(src[at..].starts_with(".. }, .."), "the inner `..` is reported first");
    }

    /// The title and the removed text of the candidate of the one diagnostic of `src`.
    fn removal(src: &str) -> (String, String) {
        let modules =
            vec![Module::new(vec!["main".into()], FileId(0), src.to_string(), onsa_syntax::parse(FileId(0), src))];
        let a = analyze(&Package::new("t", modules, vec![crate::tests::std_package()]));
        assert_eq!(a.diagnostics.len(), 1, "{:?}", a.diagnostics);
        let fix = &a.diagnostics[0].fixes[0];
        let s = fix.edits()[0].span;
        (fix.title().to_string(), src[s.start as usize..s.end as usize].to_string())
    }

    #[test]
    fn the_title_of_a_removal_is_one_line_whatever_is_removed() {
        // W3-21/b2: the title is fixed; the removal holds the blanks and newlines before the `..`.
        let cases = [
            ("P { x: _, y: _, .. }", "remove `, ..`", ", .."),
            ("P {\n      x: _,\n      y: _,\n      ..\n    }", "remove `, ..`", ",\n      .."),
            ("P {\n\t\tx: _,\n\t\ty: _,\n\t\t..\n    }", "remove `, ..`", ",\n\t\t.."),
            ("P { x: _, y: _,                                                  .. }", "remove `, ..`", ""),
            ("P {\n      x: _,\n      y: _, // the last,\n      ..\n    }", "remove `..`", ".."),
        ];
        for (pattern, title, removed) in cases {
            let (t, r) = removal(&arm(pattern));
            assert_eq!(t, title, "{pattern}");
            assert!(!t.contains('\n') && t.len() <= 60, "{pattern}: {t}");
            if !removed.is_empty() {
                assert_eq!(r, removed, "{pattern}");
            } else {
                assert!(r.starts_with(',') && r.ends_with(".."), "{pattern}: {r:?}");
            }
        }
    }

    #[test]
    fn a_last_underscore_with_nothing_left_goes_with_its_comma() {
        let cases = [
            ("P { x: _, y: _, _ }", "remove `, _`", ", _"),
            ("P {\n      x: _,\n      y: _,\n      _\n    }", "remove `, _`", ",\n      _"),
            // A comment that ends with `,` before the `_`: the `_` alone goes.
            ("P {\n      x: _,\n      y: _, // the last,\n      _\n    }", "remove `_`", "_"),
        ];
        for (pattern, title, removed) in cases {
            assert_eq!(first(&arm(pattern)).0, Code::E0410, "{pattern}");
            assert_eq!(removal(&arm(pattern)), (title.to_string(), removed.to_string()), "{pattern}");
        }
        assert_eq!(first(&arm("P { x: _, y: _, _ }")).1, "_");
        // A written field is checked first: the `_` is no error of its own.
        assert_eq!(first(&arm("P { x: _, x: _, y: _, _ }")).1, "x");
    }

    #[test]
    fn the_rest_is_e0020_last_and_its_candidate_reads_the_ast() {
        let (code, text, _) = first(&arm("P { x: _, .. }"));
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
        // A comment that ends with `,` before the `..` (W3-21/b): the `..` alone goes.
        let src = arm("P {\n      x: _,\n      y: _, // the last field,\n      ..\n    }");
        let (code, text, _) = first(&src);
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
    }
}
