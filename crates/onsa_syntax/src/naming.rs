//! Naming rules (spec §2.3), E0320 (S-01). Runs after parsing over the arenas:
//! every declared name is checked against the shape its kind requires.

use onsa_diag::{Code, Diagnostic, Fix, Span, Stage};

use crate::ast::{Ast, ExprKind, GenericParam, Ident, ItemKind, Param, ParamName, PatKind, StmtKind};

#[derive(Clone, Copy)]
enum Shape {
    /// `snake_case`: values, functions, flows, modules, fields, parameters.
    Snake,
    /// `UpperCamel`: types, traits, effects, variants.
    UpperCamel,
    /// One `UpperCamel` word: type parameters.
    // SPEC-GAP(S-642): a capital after a lowercase letter starts a second
    // word (`ItemKey`); a run of capitals (`IO`, `IOKey`) and a digit
    // (`T2`) do not. A name of more than one word has no candidate.
    UpperCamelWord,
    /// `UPPER_SNAKE`: constants.
    UpperSnake,
    /// One `snake_case` word: effect-row variables.
    SnakeWord,
}

/// Whether `name` has the shape of a constant (`UPPER_SNAKE`, §2.3): the
/// last name of a path that names a constant by its spelling alone (§7: a
/// `-` before it, the right side of `@`; S-319, S-352).
// SPEC-GAP(S-375): a name of one letter or of capitals only (`Mode.A`,
// `Status.OK`) has the shape of a variant too; it is read as a constant.
pub(crate) fn is_constant_name(name: &str) -> bool {
    Shape::UpperSnake.matches(name)
}

/// Whether a name in a pattern binds (§7, §2.3): one whose first letter is
/// lowercase does (a `snake_case` name; the naming rule checks the rest);
/// others are resolved.
pub(crate) fn is_binding_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_lowercase())
}

/// Whether a path whose last name is `name` names a type, whose `{` opens a
/// struct pattern or literal (§4.4: an `UpperCamel` name).
pub(crate) fn is_type_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_uppercase())
}

impl Shape {
    fn matches(self, s: &str) -> bool {
        let mut chars = s.chars();
        let Some(first) = chars.next() else { return false };
        match self {
            Shape::Snake => {
                (first.is_ascii_lowercase() || first == '_')
                    && s.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
            }
            Shape::SnakeWord => {
                first.is_ascii_lowercase() && s.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
            }
            Shape::UpperCamel => first.is_ascii_uppercase() && s.chars().all(|c| c.is_ascii_alphanumeric()),
            Shape::UpperCamelWord => {
                let b = s.as_bytes();
                Shape::UpperCamel.matches(s)
                    && !b.windows(2).any(|w| w[0].is_ascii_lowercase() && w[1].is_ascii_uppercase())
            }
            Shape::UpperSnake => {
                first.is_ascii_uppercase()
                    && s.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            }
        }
    }

    fn describe(self) -> &'static str {
        match self {
            Shape::Snake => "snake_case",
            Shape::SnakeWord => "one snake_case word",
            Shape::UpperCamel => "UpperCamel",
            Shape::UpperCamelWord => "one UpperCamel word",
            Shape::UpperSnake => "UPPER_SNAKE",
        }
    }

    /// Best-effort conversion for the fix.
    fn convert(self, s: &str) -> String {
        let words = split_words(s);
        match self {
            Shape::Snake => words.join("_"),
            Shape::SnakeWord => words.concat(),
            Shape::UpperCamel => words.iter().map(|w| capitalized(w)).collect(),
            // More than one word has no one-word name: the name stays, and
            // the caller makes no candidate of it.
            Shape::UpperCamelWord => match words.as_slice() {
                [w] => capitalized(w),
                _ => s.to_string(),
            },
            Shape::UpperSnake => words.iter().map(|w| w.to_ascii_uppercase()).collect::<Vec<_>>().join("_"),
        }
    }
}

fn capitalized(w: &str) -> String {
    let mut c = w.chars();
    c.next().map(|f| f.to_ascii_uppercase().to_string() + c.as_str()).unwrap_or_default()
}

/// Whether `name` is a module name (§2.3): a `snake_case` identifier, so
/// not `_` alone, without `__`, and of ASCII letters, digits and `_` that
/// does not start with a digit (S-325). A keyword is one (`match.onsa`).
pub fn is_module_name(name: &str) -> bool {
    Shape::Snake.matches(name) && name != "_" && !name.contains("__")
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
         not starting with a digit, not `_` alone, and without two `_` in a row",
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
        let mut to = shape.convert(&ident.name);
        // A name by the rule that is a keyword or a reserved word (`match`,
        // `clock`) takes a `_` at its end (§2.3, R-211).
        if crate::token::TokenKind::keyword(&to).is_some() {
            to.push('_');
        }
        // S-82 (W4-04): the candidate also renames every use in the package.
        let d = Diagnostic::new(
            Stage::Names,
            Code::E0320,
            ident.span,
            format!("{what} names are {} (§2.3)", shape.describe()),
        )
        .with_found(ident.name.clone());
        // A candidate that is still not of the shape is none (§18.1, S-642:
        // `ItemKey` has no one-word name).
        let shaped = !matches!(shape, Shape::UpperCamelWord) || shape.matches(&to);
        out.push(if shaped { d.with_fix(Fix::replace("rename by the naming rule", ident.span, to)) } else { d });
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
                GenericParam::Type { name, .. } => check(name, Shape::UpperCamelWord, "type parameter"),
                GenericParam::Const { name, .. } => check(name, Shape::UpperSnake, "const parameter"),
                GenericParam::Effect { name } => check(name, Shape::SnakeWord, "effect-row variable"),
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
    diagnostics.extend(out);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shapes() {
        assert!(Shape::Snake.matches("wrap01"));
        assert!(Shape::Snake.matches("_unused"));
        assert!(!Shape::Snake.matches("wrapAll"));
        assert!(Shape::UpperCamel.matches("Buf"));
        assert!(Shape::UpperCamel.matches("F32"));
        assert!(!Shape::UpperCamel.matches("my_type"));
        assert!(Shape::UpperSnake.matches("MAX_VOICES"));
        assert!(Shape::UpperSnake.matches("PI"));
        assert!(!Shape::UpperSnake.matches("MaxVoices"));
        assert!(Shape::SnakeWord.matches("e"));
        assert!(!Shape::SnakeWord.matches("eff_row"));
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

    #[test]
    fn a_type_parameter_is_one_upper_camel_word() {
        // R-46: `ItemKey` is two words; the candidate is one.
        assert!(Shape::UpperCamelWord.matches("T"));
        assert!(Shape::UpperCamelWord.matches("Item2"));
        assert!(Shape::UpperCamelWord.matches("IO"));
        assert!(Shape::UpperCamelWord.matches("IOKey"));
        assert!(!Shape::UpperCamelWord.matches("ItemKey"));
        assert!(!Shape::UpperCamelWord.matches("Item_Key"));
        let src = "pub struct S[ItemKey] { a: ItemKey }\nfn f[T, IO, T_](x: T) -> T { x }\n";
        let parsed = crate::parse(onsa_diag::FileId(0), src);
        let got: Vec<_> = parsed
            .diagnostics
            .iter()
            .map(|d| (d.found.clone().unwrap(), d.fixes.iter().map(|f| f.edits()[0].replace.clone()).collect()))
            .collect();
        let want: Vec<(String, Vec<String>)> = vec![("ItemKey".into(), vec![]), ("T_".into(), vec!["T".into()])];
        assert_eq!(got, want);
    }

    #[test]
    fn module_names_are_snake_case_identifiers() {
        // §2.3, S-300, S-325: keywords are names; `_`, a digit first, ASCII only.
        for ok in ["main", "dsp2", "_util", "match", "test", "a_b"] {
            assert!(is_module_name(ok), "{ok}");
        }
        for bad in ["", "_", "My-File", "a.b", "a b", "a__b", "2x", "caf\u{e9}", ".hid", "Mod"] {
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
