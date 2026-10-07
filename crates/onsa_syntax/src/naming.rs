//! Naming rules (spec §2.3), E0320 (S-01). Runs after parsing over the arenas:
//! every declared name is checked against the shape its kind requires.

use onsa_diag::{Code, Diagnostic, Fix, Stage};

use crate::ast::{Ast, ExprKind, GenericParam, Ident, ItemKind, Param, ParamName, PatKind, StmtKind, StructKind};

#[derive(Clone, Copy)]
enum Shape {
    /// `snake_case`: values, functions, flows, modules, fields, parameters.
    Snake,
    /// `UpperCamel`: types, traits, effects, variants, type parameters.
    UpperCamel,
    /// `UPPER_SNAKE`: constants.
    UpperSnake,
    /// One `snake_case` word: effect-row variables.
    SnakeWord,
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
            Shape::UpperSnake => "UPPER_SNAKE",
        }
    }

    /// Best-effort conversion for the fix.
    fn convert(self, s: &str) -> String {
        let words = split_words(s);
        match self {
            Shape::Snake => words.join("_"),
            Shape::SnakeWord => words.concat(),
            Shape::UpperCamel => words
                .iter()
                .map(|w| {
                    let mut c = w.chars();
                    c.next().map(|f| f.to_ascii_uppercase().to_string() + c.as_str()).unwrap_or_default()
                })
                .collect(),
            Shape::UpperSnake => words.iter().map(|w| w.to_ascii_uppercase()).collect::<Vec<_>>().join("_"),
        }
    }
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
        let to = shape.convert(&ident.name);
        // S-82 (W4-04): the candidate also renames every use in the package.
        let d = Diagnostic::new(
            Stage::Names,
            Code::E0320,
            ident.span,
            format!("{what} names are {} (§2.3)", shape.describe()),
        )
        .with_found(ident.name.clone())
        .with_fix(Fix::replace("rename by the naming rule", ident.span, to));
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
                if let StructKind::Named(fields) = &s.kind {
                    for f in fields {
                        check(&f.name, Shape::Snake, "field");
                    }
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
        // P-01: first per item; `struct point { X }` reports `point` only, `ok` reports the parameter only.
        // (`let BadName = 1` is a path pattern, not a binding; sema reports it.)
        assert_eq!(
            codes,
            vec![
                (Code::E0320, "Foo".to_string()),
                (Code::E0320, "point".to_string()),
                (Code::E0320, "max".to_string()),
                (Code::E0320, "badParam".to_string()),
            ]
        );
        let fixes: Vec<_> = parsed.diagnostics.iter().map(|d| d.fixes[0].edits()[0].replace.clone()).collect();
        assert_eq!(fixes, vec!["foo", "Point", "MAX", "bad_param"]);
    }
}
