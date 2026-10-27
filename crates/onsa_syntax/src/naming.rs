//! Naming rules (spec §2.3), E0320 (S-01). Runs after parsing over the arenas:
//! every declared name is checked against the shape its kind requires.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};

use crate::ast::{Ast, ExprKind, GenericParam, Ident, ItemKind, Param, ParamName, PatKind, StmtKind};

/// The three shapes of names (§2.3, S-650): a core starting with a letter
/// and one optional trailing `_` (the spelling that avoids a reserved word,
/// S-243). A leading `_` is in no shape, nor is `__` (S-149: the C names
/// map `.` to `__`, §11.6). Every kind of name takes one.
#[derive(Clone, Copy)]
enum Shape {
    /// `snake_case`: values, functions, flows, modules, fields, parameters,
    /// effect-row variables; the core is `[a-z][a-z0-9_]*`.
    Snake,
    /// `UpperCamel`: types, traits, effects, variants, type parameters; the
    /// core is `[A-Z][A-Za-z0-9]*`.
    UpperCamel,
    /// `UPPER_SNAKE`: constants; the core is `[A-Z][A-Z0-9_]*`.
    UpperSnake,
}

/// The part of a name read where its spelling decides its kind (§2.3,
/// S-648): what follows a leading `_`, so `_x` is read as `x` and the naming
/// rule reports the `_` (E0320) as a name of the kind read. Only the kind
/// is read: the rules of `__` and of the trailing `_` are the declaration's
/// E0320 (a name used is read as written, §2.3).
fn spelled(name: &str) -> &str {
    name.trim_start_matches('_')
}

/// Whether `name` has a leading `_`, the part [`spelled`] skips.
fn has_leading_underscore(name: &str) -> bool {
    spelled(name).len() != name.len()
}

/// Whether a name read by its spelling is of a `snake_case` kind (§2.3): a
/// binding in a pattern (§7), an effect-row variable in `[...]` (§8.1).
// SPEC-GAP(S-656): a name with no letter after its leading `_` (`_0`, `__`)
// has no case to read; it is read as a name whose first letter is not lowercase
// (resolved in a pattern, a type parameter in `[...]`).
pub(crate) fn reads_lowercase(name: &str) -> bool {
    spelled(name).starts_with(|c: char| c.is_ascii_lowercase())
}

/// Whether a name read by its spelling is of an `UpperCamel` kind (§2.3): a
/// type whose `{` opens a struct pattern or literal (§4.4), an effect after
/// `with` (S-421).
pub(crate) fn reads_uppercase(name: &str) -> bool {
    spelled(name).starts_with(|c: char| c.is_ascii_uppercase())
}

/// Whether a name read by its spelling is a constant's (`UPPER_SNAKE`,
/// §2.3, §7): the last name of a path after `-` or on the right of `@`
/// (S-319, S-352), and FAUST's `x@N`. A name of both `UpperCamel` and
/// `UPPER_SNAKE` (`A`, `OK`) is a constant's here (S-375).
pub(crate) fn reads_constant(name: &str) -> bool {
    let s = spelled(name);
    s.starts_with(|c: char| c.is_ascii_uppercase())
        && s.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}

impl Shape {
    fn matches(self, s: &str) -> bool {
        if s.contains("__") {
            return false;
        }
        let core = s.strip_suffix('_').unwrap_or(s);
        let mut rest = core.chars();
        let Some(first) = rest.next() else { return false };
        match self {
            Shape::Snake => {
                first.is_ascii_lowercase() && rest.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
            }
            Shape::UpperCamel => first.is_ascii_uppercase() && rest.all(|c| c.is_ascii_alphanumeric()),
            Shape::UpperSnake => {
                first.is_ascii_uppercase() && rest.all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            }
        }
    }

    fn describe(self) -> &'static str {
        match self {
            Shape::Snake => "snake_case",
            Shape::UpperCamel => "UpperCamel",
            Shape::UpperSnake => "UPPER_SNAKE",
        }
    }

    /// Best-effort conversion for the fix: the words of the name in the
    /// shape (the boundaries of [`split_words`] are not in the spec, S-651).
    fn convert(self, s: &str) -> String {
        let words = split_words(s);
        match self {
            Shape::Snake => words.join("_"),
            Shape::UpperCamel => words.iter().map(|w| capitalized(w)).collect(),
            Shape::UpperSnake => words.iter().map(|w| w.to_ascii_uppercase()).collect::<Vec<_>>().join("_"),
        }
    }

    /// The candidate of the E0320 of `name` (§2.3, §18.1): the name by the
    /// rule, with a `_` at its end when that is a reserved word (`match_`,
    /// S-243). None when it is not of the shape (`_0` gives no identifier,
    /// S-651) or is the name itself (R-260, R-262).
    fn candidate(self, name: &str) -> Option<String> {
        let mut to = self.convert(name);
        if crate::token::TokenKind::keyword(&to).is_some() {
            to.push('_');
        }
        (self.matches(&to) && to != name).then_some(to)
    }
}

fn capitalized(w: &str) -> String {
    let mut c = w.chars();
    c.next().map(|f| f.to_ascii_uppercase().to_string() + c.as_str()).unwrap_or_default()
}

/// Whether `name` is a module name (§2.3): a `snake_case` identifier, so of
/// ASCII letters, digits and `_`, starting with a letter (not `_` alone, no
/// digit first, S-325; no leading `_`, S-650) and without `__`. A keyword is
/// one (`match.onsa`).
pub fn is_module_name(name: &str) -> bool {
    Shape::Snake.matches(name)
}

/// What part of a module path a name is (§2.3, S-300, S-313).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathPart {
    /// The name of a file, without `.onsa`.
    File,
    Directory,
}

/// The E0320 of a file name or a directory name of a module path that is not
/// a module name ([`is_module_name`]), at `span` (the head of a file, §2.3):
/// no candidate, since a rename of a file is not an edit of a text (§18.1);
/// a note shows the rule. The span is empty, so there is no `found`: the
/// message names the name.
pub fn path_name_error(span: Span, part: PathPart, name: &str) -> Option<Diagnostic> {
    if is_module_name(name) {
        return None;
    }
    let what = match part {
        PathPart::File => "file",
        PathPart::Directory => "directory",
    };
    let d = Diagnostic::new(
        Stage::Names,
        Code::E0320,
        span,
        format!("the {what} name `{name}` is not a module name, which is snake_case (§2.3)"),
    )
    .with_rule(format!(
        "rename the {what} so that its name{} is snake_case: lowercase ASCII letters, digits and `_`, \
         starting with a letter, and without two `_` in a row",
        if part == PathPart::File { " before `.onsa`" } else { "" }
    ));
    Some(d)
}

/// `fooBar`, `FooBar`, `foo_bar`, `FOO_BAR` -> `["foo", "bar"]`
fn split_words(s: &str) -> Vec<String> {
    let mut words: Vec<String> = Vec::new();
    let mut cur = String::new();
    let chars: Vec<char> = s.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if c == '_' {
            if !cur.is_empty() {
                words.push(std::mem::take(&mut cur));
            }
            continue;
        }
        let boundary = c.is_ascii_uppercase()
            && !cur.is_empty()
            && (chars[i - 1].is_ascii_lowercase()
                || chars[i - 1].is_ascii_digit()
                || chars.get(i + 1).is_some_and(|n| n.is_ascii_lowercase()));
        if boundary {
            words.push(std::mem::take(&mut cur));
        }
        cur.push(c.to_ascii_lowercase());
    }
    if !cur.is_empty() {
        words.push(cur);
    }
    words
}

pub(crate) fn check(ast: &Ast, diagnostics: &mut Vec<Diagnostic>) {
    let mut out = Vec::new();
    let mut check = |ident: &Ident, shape: Shape, what: &str| {
        if ident.name == "_" || shape.matches(&ident.name) {
            return;
        }
        let mut d = Diagnostic::new(
            Stage::Names,
            Code::E0320,
            ident.span,
            format!("{what} names are {} (§2.3)", shape.describe()),
        )
        .with_found(ident.name.clone());
        // S-82 (W4-04): the candidate also renames every use in the package.
        if let Some(to) = shape.candidate(&ident.name) {
            // `_type`: the leading `_` avoided a reserved word (§2.3, S-648).
            if has_leading_underscore(&ident.name) && to.ends_with('_') {
                d = d.with_rule("a name that is a reserved word takes a `_` at its end, not at its head");
            }
            d = d.with_fix(Fix::replace("rename by the naming rule", ident.span, to));
        }
        out.push(d);
    };
    let params = |params: &[Param], check: &mut dyn FnMut(&Ident, Shape, &str)| {
        for p in params {
            if let ParamName::Ident(id) = &p.name {
                check(id, Shape::Snake, "parameter");
            }
        }
    };
    let generics = |gs: &[GenericParam], check: &mut dyn FnMut(&Ident, Shape, &str)| {
        for g in gs {
            match g {
                GenericParam::Type { name, .. } => check(name, Shape::UpperCamel, "type parameter"),
                GenericParam::Const { name, .. } => check(name, Shape::UpperSnake, "const parameter"),
                GenericParam::Effect { name } => check(name, Shape::Snake, "effect-row variable"),
            }
        }
    };
    for item in &ast.items {
        let mut kind = &item.kind;
        if let ItemKind::Target(inner) = kind {
            kind = inner;
        }
        match kind {
            ItemKind::Fn(f) => {
                check(&f.name, Shape::Snake, "function");
                generics(&f.generics, &mut check);
                params(&f.params, &mut check);
            }
            ItemKind::Flow(f) => {
                check(&f.name, Shape::Snake, "flow");
                params(&f.params, &mut check);
            }
            ItemKind::Struct(s) => {
                check(&s.name, Shape::UpperCamel, "type");
                generics(&s.generics, &mut check);
                for f in &s.fields {
                    check(&f.name, Shape::Snake, "field");
                }
            }
            ItemKind::Enum(e) => {
                check(&e.name, Shape::UpperCamel, "type");
                generics(&e.generics, &mut check);
                for v in &e.variants {
                    check(&v.name, Shape::UpperCamel, "variant");
                }
            }
            ItemKind::TypeAlias { name, .. } | ItemKind::OpaqueType { name } => check(name, Shape::UpperCamel, "type"),
            ItemKind::Trait(t) => {
                check(&t.name, Shape::UpperCamel, "trait");
                generics(&t.generics, &mut check);
            }
            ItemKind::Impl(i) => generics(&i.generics, &mut check),
            ItemKind::Effect(e) => check(&e.name, Shape::UpperCamel, "effect"),
            ItemKind::Handler(h) => {
                check(&h.name, Shape::Snake, "handler");
                params(&h.params, &mut check);
            }
            ItemKind::Const(c) => check(&c.name, Shape::UpperSnake, "constant"),
            ItemKind::Use(_) | ItemKind::Extern(_) | ItemKind::Target(_) | ItemKind::Test { .. } => {}
        }
    }
    for stmt in &ast.stmts {
        if let StmtKind::Var { name, .. } = &stmt.kind {
            check(name, Shape::Snake, "variable");
        }
    }
    for expr in &ast.exprs {
        match &expr.kind {
            ExprKind::Closure { params: ps, .. } => params(ps, &mut check),
            ExprKind::Par { var, .. } => check(var, Shape::Snake, "variable"),
            _ => {}
        }
    }
    for pat in &ast.pats {
        if let PatKind::Bind(id) = &pat.kind {
            check(id, Shape::Snake, "variable");
        }
    }
    // A binding with a leading `_` may mean a value that is not used: that is
    // `_` alone, the candidate of its E0309 after this one (§2.3, §5.1, S-726).
    let marked: std::collections::HashSet<Span> = (ast.pats.iter())
        .filter_map(|p| match &p.kind {
            PatKind::Bind(id) if has_leading_underscore(&id.name) => Some(id.span),
            _ => None,
        })
        .collect();
    for d in out.iter_mut().filter(|d| marked.contains(&d.span)) {
        d.notes.push(onsa_diag::Note::rule("a value that is not used is bound to `_` alone, with no name"));
    }
    diagnostics.extend(out);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shapes() {
        // §2.3, S-650: a core starting with a letter and one trailing `_`.
        for ok in ["wrap01", "e", "eff_row", "match_", "g_", "item_key"] {
            assert!(Shape::Snake.matches(ok), "{ok}");
        }
        for bad in ["_unused", "_", "wrapAll", "2x", "", "Wrap", "a__b", "g__"] {
            assert!(!Shape::Snake.matches(bad), "{bad}");
        }
        for ok in ["Buf", "F32", "T", "IO", "ItemKey", "T2D", "Self_", "Point_"] {
            assert!(Shape::UpperCamel.matches(ok), "{ok}");
        }
        for bad in ["my_type", "_Point", "Item_Key", "Point__", "_0", ""] {
            assert!(!Shape::UpperCamel.matches(bad), "{bad}");
        }
        for ok in ["MAX_VOICES", "PI", "MAX_", "A", "OK"] {
            assert!(Shape::UpperSnake.matches(ok), "{ok}");
        }
        for bad in ["MaxVoices", "_MAX", "_1", "", "A__B", "MAX__"] {
            assert!(!Shape::UpperSnake.matches(bad), "{bad}");
        }
    }

    #[test]
    fn the_kind_by_the_spelling_skips_a_leading_underscore() {
        // §2.3, S-648: `[_e]` is an effect-row variable, `_x` binds, `_T {`
        // is a struct; S-375: `OK` is a constant's.
        assert!(reads_lowercase("_e") && reads_lowercase("x") && !reads_lowercase("_T"));
        assert!(reads_uppercase("_P") && reads_uppercase("Point") && !reads_uppercase("_h"));
        assert!(reads_constant("_MAX") && reads_constant("OK") && reads_constant("N") && !reads_constant("Max"));
        // Only the kind is read: `MAX__` and `MAX_` are constants' (their
        // E0320 is at the declaration).
        assert!(reads_constant("MAX__") && reads_constant("MAX_") && reads_constant("_A__B"));
        assert!(reads_lowercase("x__") && reads_uppercase("P__"));
        assert!(!reads_lowercase("_0") && !reads_uppercase("_0"));
    }

    #[test]
    fn conversions() {
        assert_eq!(Shape::Snake.convert("wrapAll"), "wrap_all");
        assert_eq!(Shape::Snake.convert("MaxVoices"), "max_voices");
        assert_eq!(Shape::UpperCamel.convert("my_type"), "MyType");
        assert_eq!(Shape::UpperCamel.convert("HTTPServer"), "HttpServer");
        assert_eq!(Shape::UpperSnake.convert("maxVoices"), "MAX_VOICES");
    }

    #[test]
    fn declarations() {
        let src =
            "fn Foo() {}\nstruct point { X: F32 }\nconst max: U32 = 1\nfn ok(badParam: I32) { var BadName = 1\n}\n";
        let parsed = crate::parse(onsa_diag::FileId(0), src);
        let codes: Vec<_> = parsed.diagnostics.iter().map(|d| (d.code, d.found.clone().unwrap())).collect();
        // Every one: the choice of one per unit is the driver's (S-59).
        assert_eq!(
            codes,
            vec![
                (Code::E0320, "Foo".to_string()),
                (Code::E0320, "point".to_string()),
                (Code::E0320, "X".to_string()),
                (Code::E0320, "max".to_string()),
                (Code::E0320, "badParam".to_string()),
                (Code::E0320, "BadName".to_string()),
            ]
        );
        let fixes: Vec<_> = parsed.diagnostics.iter().map(|d| d.fixes[0].edits()[0].replace.clone()).collect();
        assert_eq!(fixes, vec!["foo", "Point", "x", "MAX", "bad_param", "bad_name"]);
    }

    /// The E0320s of `src` as (found, candidates, notes without a span).
    fn e0320s(src: &str) -> Vec<(String, Vec<String>, usize)> {
        let parsed = crate::parse(onsa_diag::FileId(0), src);
        parsed
            .diagnostics
            .iter()
            .filter(|d| d.code == Code::E0320)
            .map(|d| {
                let fixes = d.fixes.iter().map(|f| f.edits()[0].replace.clone()).collect();
                (d.found.clone().unwrap(), fixes, d.notes.iter().filter(|n| n.span.is_none()).count())
            })
            .collect()
    }

    #[test]
    fn type_parameters_and_effect_row_variables_take_the_shapes_of_their_kinds() {
        // S-642: no one-word rule; R-46: `Item_Key` is no `UpperCamel`.
        let src = "pub struct S[ItemKey] { a: ItemKey }\nfn f[T, IO, T_, T2D, Item_Key, item_key, itemKey, inout_](x: T) -> T { x }\n";
        let want = vec![
            ("Item_Key".to_string(), vec!["ItemKey".to_string()], 0),
            ("itemKey".into(), vec!["item_key".into()], 0),
        ];
        assert_eq!(e0320s(src), want);
    }

    #[test]
    fn a_leading_underscore_is_reported_as_the_kind_read() {
        // §2.3, S-648, R-168, R-240: `[_e]` is an effect-row variable, `_x`
        // binds; `_type` takes `type_` and a note.
        let src = "fn _g[_T, _e](_p: I32) { let _x = 1\nlet _type = 2\n}\nstruct _P {}\nconst _MAX: I32 = 1\n";
        let got: Vec<_> = e0320s(src).into_iter().map(|(f, c, n)| (f, c.join(","), n)).collect();
        let want: Vec<(String, String, usize)> = [
            ("_g", "g", 0),
            ("_T", "T", 0),
            ("_e", "e", 0),
            ("_p", "p", 0),
            ("_P", "P", 0),
            ("_MAX", "MAX", 0),
            // A binding's note says that a value not used is `_` alone (S-726).
            ("_x", "x", 1),
            ("_type", "type_", 2),
        ]
        .iter()
        .map(|&(f, c, n)| (f.to_string(), c.to_string(), n))
        .collect();
        assert_eq!(got, want);
    }

    #[test]
    fn a_candidate_is_an_identifier_of_the_shape_other_than_the_name() {
        // §2.3, §18.1, R-260, R-262: every candidate is of the shape, has no
        // `__`, is no reserved word and is not the name; `_0`, `__` and `_1`
        // have none. And a sample of each shape that has a candidate gets one.
        let samples = [
            "_0",
            "_1",
            "__",
            "_",
            "_x",
            "_type",
            "Self",
            "self",
            "fooBar",
            "FooBar",
            "foo_bar",
            "FOO_BAR",
            "Match",
            "match",
            "T",
            "t",
            "IO",
            "io",
            "Item_Key",
            "x_",
            "X_",
            "_X_",
            "a2b",
            "A2B",
            "HTTPServer",
            "e",
            "Point_",
            "a__b",
            "A__B",
        ];
        for shape in [Shape::Snake, Shape::UpperCamel, Shape::UpperSnake] {
            for name in samples {
                let Some(to) = shape.candidate(name) else {
                    let none = ["_0", "_1", "__", "_"].contains(&name) || shape.matches(name);
                    assert!(none, "{} `{name}` has no candidate", shape.describe());
                    continue;
                };
                assert!(shape.matches(&to) && !to.contains("__") && to != name, "`{name}` -> `{to}`");
                assert!(crate::token::TokenKind::keyword(&to).is_none(), "`{name}` -> `{to}`");
            }
        }
        // S-149: `__` takes the name by the rule.
        assert_eq!(Shape::Snake.candidate("a__b").as_deref(), Some("a_b"));
        assert_eq!(Shape::UpperSnake.candidate("A__B").as_deref(), Some("A_B"));
        assert_eq!(Shape::Snake.candidate("g__").as_deref(), Some("g"));
        let src = "struct _0 {}\nenum C { _0 }\nconst _1: I32 = 1\n";
        assert!(e0320s(src).iter().all(|(_, c, _)| c.is_empty()), "{:?}", e0320s(src));
    }

    #[test]
    fn module_names_are_snake_case_identifiers() {
        // §2.3, S-300, S-325, S-650: keywords are names; `_`, a leading `_`,
        // a digit first, ASCII only.
        for ok in ["main", "dsp2", "match", "test", "a_b", "util_"] {
            assert!(is_module_name(ok), "{ok}");
        }
        for bad in ["", "_", "_util", "My-File", "a.b", "a b", "a__b", "2x", "caf\u{e9}", ".hid", "Mod"] {
            assert!(!is_module_name(bad), "{bad}");
        }
        let d = path_name_error(Span::empty(onsa_diag::FileId(0), 0), PathPart::Directory, "My-Dir").unwrap();
        assert_eq!((d.code, d.found.as_deref(), d.fixes.len()), (Code::E0320, None, 0));
        assert!(d.message.contains("`My-Dir`"), "{}", d.message);
        assert!(d.notes.iter().any(|n| n.span.is_none()));
    }

    #[test]
    fn a_name_by_the_rule_that_is_a_keyword_takes_an_underscore() {
        // §2.3, R-211: `match_`, and the reserved words too.
        let src = "pub fn Match() {}\nfn Clock() {}\nfn When() {}\nstruct S { Ser: I32 }\nconst true_: I32 = 1\n";
        let parsed = crate::parse(onsa_diag::FileId(0), src);
        let fixes: Vec<_> = parsed.diagnostics.iter().map(|d| d.fixes[0].edits()[0].replace.clone()).collect();
        assert_eq!(fixes, vec!["match_", "clock_", "when_", "ser_", "TRUE"]);
    }
}
