//! The fields of a struct pattern against its declaration (spec §7, §4.4;
//! S-109, S-366): the one check of a struct pattern, for the bodies and the
//! flows. A pattern names every field once (E0410); the rest `..` of other
//! languages is E0020 here, where the fields are known, and its candidate
//! writes the remaining ones with `_`.
//!
//! The order of the errors is the order of reading: the fields as written,
//! each name checked and then its sub-pattern (through the caller), and the
//! fields that are missing (or the `..`) last. An inner pattern's error is
//! so reported before an outer one's `..`.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};
use onsa_syntax::ast::{Ident, PatId, Path, StructRest};
use onsa_syntax::foreign::{self, RowId};

use crate::body::{Checker, R, Stop};
use crate::def::{DefKind, Fields};
use crate::resolve::Entity;
use crate::ty::{Ty, TyId};

/// What the caller does with a written field: its pattern, the type it
/// matches and its index in the declaration. A field that a struct whose
/// unit failed in the syntax stage may have has the error type and no index
/// (S-260).
pub(crate) type SubPattern<'s, 'a> = &'s mut dyn FnMut(&mut Checker<'a>, PatId, TyId, Option<usize>) -> R<()>;

/// A struct pattern as written: `path { fields, rest }`.
pub(crate) struct Written<'p> {
    pub path: &'p Path,
    pub fields: &'p [(Ident, PatId)],
    pub rest: Option<StructRest>,
}

impl<'a> Checker<'a> {
    /// The struct pattern `written` of type `ty` at `span`:
    /// the struct is resolved and unified with `ty`, each written field is
    /// checked and given to `sub`, in the order written, and the number of
    /// the declared fields is returned. The diagnostics are of `stage`.
    pub(crate) fn struct_pattern(
        &mut self,
        stage: Stage,
        span: Span,
        ty: TyId,
        written: Written<'_>,
        sub: SubPattern<'_, 'a>,
    ) -> R<usize> {
        let Written { path, fields, rest } = written;
        let entity = match self.a.resolve_path(self.m, path) {
            Ok(en) => en,
            Err(err) => return Err(self.resolve_error(path, err)),
        };
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
        let named = self.a.types.intern(Ty::Named(d, args.clone()));
        self.unify_at(span, named, ty)?;
        // SPEC-GAP(S-260): as for the fields of a struct literal.
        let failed = self.a.partly_read(d);
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
            let ft = self.subst_pub(defs[i].ty, &args);
            sub(self, *fp, ft, Some(i))?;
        }
        if failed {
            return Ok(defs.len());
        }
        let missing: Vec<&crate::def::FieldDef> = defs.iter().filter(|f| !seen.contains(&f.name.as_str())).collect();
        // A field has the visibility of its struct, narrowed only by `priv`
        // (§15.1). The parser reads no `priv` yet, and `FieldDef::vis` is
        // the written one (none is `Private`), so every field is as visible
        // as the struct, which this pattern names: no field is hidden here
        // until the visibility of the fields is checked (reported by
        // W3-21/i; the patterns, the literals and the accesses alike).
        let hidden = false;
        match rest {
            // `..`: the remaining fields with `_`, in the order of the
            // declaration; none left, the `, ..` goes (§7, S-109).
            Some(rest) if !hidden => {
                let fix = if missing.is_empty() {
                    // A title is one line: the removal may hold newlines.
                    let title = if rest.removal.start < rest.span.start { "remove `, ..`" } else { "remove `..`" };
                    Fix::new(title, vec![Edit::delete(rest.removal)])
                } else {
                    let list = missing.iter().map(|f| format!("{}: _", f.name)).collect::<Vec<_>>().join(", ");
                    Fix::new("write the remaining fields with `_`", vec![Edit::replace(rest.span, list)])
                };
                let mut d = foreign::report(RowId::StructPatternRest, self.text, rest.span, vec![fix]);
                d.stage = stage;
                Err(self.diag(d))
            }
            _ if !missing.is_empty() => {
                let names = missing.iter().map(|f| format!("`{}`", f.name)).collect::<Vec<_>>().join(", ");
                let msg = format!("struct patterns name every field; missing {names} (use `_`, §7)");
                let mut d = Diagnostic::new(stage, Code::E0410, span, msg).with_found(self.src(span));
                if rest.is_some() {
                    // A field not visible here cannot be named (§15.1): no candidate.
                    d = d.with_rule("there is no `..`: a struct pattern names every field, the unused ones `_` (§7)");
                }
                Err(self.diag(d))
            }
            _ => Ok(defs.len()),
        }
    }

    fn pattern_err(&mut self, stage: Stage, code: Code, span: Span, msg: impl Into<String>) -> Stop {
        self.diag(Diagnostic::new(stage, code, span, msg).with_found(self.src(span)))
    }
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    use crate::{Module, Package, analyze};

    /// The code, the text and the start of the one diagnostic of `src`.
    fn first(src: &str) -> (Code, String, usize) {
        let modules = vec![Module {
            path: "main".into(),
            file: FileId(0),
            text: src.to_string(),
            parsed: onsa_syntax::parse(FileId(0), src),
        }];
        let a = analyze(&Package { name: "t".into(), modules, deps: Vec::new(), is_std: false });
        assert_eq!(a.diagnostics.len(), 1, "{:?}", a.diagnostics);
        let d = &a.diagnostics[0];
        let (from, to) = (d.span.start as usize, d.span.end as usize);
        (d.code, src[from..to].to_string(), from)
    }

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
        assert_eq!(code_text("P { x: Some(a), w: b }").0, Code::E0401);
        // An unknown field before a later sub-pattern.
        assert_eq!(code_text("P { w: b, x: Nope }"), (Code::E0410, "w".into()));
        // The missing fields last.
        assert_eq!(code_text("P { x: a }").0, Code::E0410);
        // An inner `..` before the outer one.
        let src = arm("W { p: P { x: a, .. }, .. }");
        let (code, text, at) = first(&src);
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
        assert!(src[at..].starts_with(".. }, .."), "the inner `..` is reported first");
    }

    /// The title and the removed text of the candidate of the one diagnostic of `src`.
    fn removal(src: &str) -> (String, String) {
        let modules = vec![Module {
            path: "main".into(),
            file: FileId(0),
            text: src.to_string(),
            parsed: onsa_syntax::parse(FileId(0), src),
        }];
        let a = analyze(&Package { name: "t".into(), modules, deps: Vec::new(), is_std: false });
        assert_eq!(a.diagnostics.len(), 1, "{:?}", a.diagnostics);
        let fix = &a.diagnostics[0].fixes[0];
        let s = fix.edits()[0].span;
        (fix.title().to_string(), src[s.start as usize..s.end as usize].to_string())
    }

    #[test]
    fn the_title_of_a_removal_is_one_line_whatever_is_removed() {
        // W3-21/b2: the title is fixed; the removal holds the blanks and newlines before the `..`.
        let cases = [
            ("P { x: a, y: b, .. }", "remove `, ..`", ", .."),
            ("P {\n      x: a,\n      y: b,\n      ..\n    }", "remove `, ..`", ",\n      .."),
            ("P {\n\t\tx: a,\n\t\ty: b,\n\t\t..\n    }", "remove `, ..`", ",\n\t\t.."),
            ("P { x: a, y: b,                                                  .. }", "remove `, ..`", ""),
            ("P {\n      x: a,\n      y: b, // the last,\n      ..\n    }", "remove `..`", ".."),
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
    fn the_rest_is_e0020_last_and_its_candidate_reads_the_ast() {
        let (code, text, _) = first(&arm("P { x: a, .. }"));
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
        // A comment that ends with `,` before the `..` (W3-21/b): the `..` alone goes.
        let src = arm("P {\n      x: a,\n      y: b, // the last field,\n      ..\n    }");
        let (code, text, _) = first(&src);
        assert_eq!((code, text.as_str()), (Code::E0020, ".."));
    }
}
