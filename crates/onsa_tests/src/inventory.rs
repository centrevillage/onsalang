//! What the compiler holds, listed for the gate's static checks (W1-02):
//! the registry of diagnostic codes, and the names the embedded std declares.
//! Each list is read from the compiler's own structures, so the gate's Python
//! never parses Rust or Onsa source to find them.

use onsa_diag::{Code, FileId};
use onsa_syntax::ast::{ItemKind, StructKind};

/// Every registered code with what the registry holds (R-87 (3)):
/// `[{"code": "E0001", "category": "syntax", "stages": ["syntax"], "fix": "optional",
/// "note": "optional", "title": "..."}, ...]`.
pub fn codes() -> serde_json::Value {
    Code::ALL
        .iter()
        .map(|c| {
            serde_json::json!({
                "code": c.as_str(),
                "category": format!("{:?}", c.category()).to_lowercase(),
                "stages": c.stages().iter().map(|s| s.name()).collect::<Vec<_>>(),
                "fix": match c.fix_rule() { onsa_diag::FixRule::Required => "required", onsa_diag::FixRule::Optional => "optional" },
                "note": match c.note_rule() { onsa_diag::NoteRule::Rule => "rule", onsa_diag::NoteRule::Optional => "optional" },
                "title": c.title(),
            })
        })
        .collect()
}

/// The names the embedded std declares, sorted and without duplicates: the
/// package name `std`, the segments of its module paths, and every declared
/// item, member (of `impl`, `trait`, `effect`, `handler`, `extern`), enum
/// variant and struct field. Fails when a std module does not parse.
pub fn std_names() -> Result<Vec<String>, String> {
    let mut names = vec![onsa_driver::STD_PACKAGE.to_string()];
    for (path, text) in onsa_driver::std_modules() {
        names.extend(path.split('.').map(str::to_string));
        let parsed = onsa_syntax::parse(FileId(0), text);
        if !parsed.diagnostics.is_empty() {
            return Err(format!("std.{path} does not parse: {}", parsed.diagnostics[0].message));
        }
        for item in &parsed.ast.items {
            item_names(&item.kind, &mut names);
        }
    }
    names.sort();
    names.dedup();
    Ok(names)
}

/// The names of the builtin methods, associated constants and associated
/// functions, from the one table of sema that holds them (until W5-02 moves
/// them into std declarations).
pub fn builtin_member_names() -> Vec<String> {
    onsa_sema::builtin_member_names()
}

/// The names one item declares. Members are items of their own in the arena,
/// so they are reached by the caller's loop.
fn item_names(kind: &ItemKind, out: &mut Vec<String>) {
    match kind {
        ItemKind::Fn(f) => out.push(f.name.name.clone()),
        ItemKind::Flow(f) => out.push(f.name.name.clone()),
        ItemKind::Struct(s) => {
            out.push(s.name.name.clone());
            if let StructKind::Named(fields) = &s.kind {
                out.extend(fields.iter().map(|f| f.name.name.clone()));
            }
        }
        ItemKind::Enum(e) => {
            out.push(e.name.name.clone());
            out.extend(e.variants.iter().map(|v| v.name.name.clone()));
        }
        ItemKind::TypeAlias { name, .. } | ItemKind::OpaqueType { name } => out.push(name.name.clone()),
        ItemKind::Trait(t) => out.push(t.name.name.clone()),
        ItemKind::Effect(e) => out.push(e.name.name.clone()),
        ItemKind::Handler(h) => out.push(h.name.name.clone()),
        ItemKind::Const(c) => out.push(c.name.name.clone()),
        ItemKind::Target(inner) => item_names(inner, out),
        ItemKind::Impl(_) | ItemKind::Use(_) | ItemKind::Extern(_) | ItemKind::Test { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_list_the_registry() {
        let v = codes();
        let list = v.as_array().unwrap();
        assert_eq!(list.len(), Code::ALL.len());
        assert_eq!(list[0]["code"], "E0001");
        assert_eq!(list[0]["category"], "syntax");
        assert!(list.iter().any(|c| c["code"] == "E1104" && c["category"] == "manifest"));
        assert!(list.iter().any(|c| c["code"] == "E0020" && c["fix"] == "required" && c["note"] == "rule"));
        assert!(!list.iter().any(|c| c["code"] == "E0814"), "E0814 is retired (S-147)");
    }

    #[test]
    fn std_names_are_declared_names() {
        let names = std_names().unwrap();
        for n in ["std", "math", "gen", "sqrt", "db_to_amp", "Gen", "seed", "from_fn", "assert_near"] {
            assert!(names.iter().any(|x| x == n), "{n} not in {names:?}");
        }
        // parameters and type parameters are not declarations of std
        for n in ["T", "x", "lo", "cases"] {
            assert!(!names.iter().any(|x| x == n), "{n} in {names:?}");
        }
        let mut sorted = names.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(names, sorted);
    }
}
