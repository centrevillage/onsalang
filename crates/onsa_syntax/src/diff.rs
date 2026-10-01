//! `onsa diff --ast` (spec §18.2, T1-10): structural comparison of two files.
//! Items are matched by kind and name; comments and whitespace are ignored
//! because the comparison is on the AST dump.

use std::collections::HashMap;

use onsa_diag::Span;

use crate::ast::{Ast, Block, ExprKind, ItemId, ItemKind};
use crate::dump::{dump_item, dump_stmt, dump_type};
use crate::parser::Parsed;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Change {
    Added,
    Removed,
    Changed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItemDiff {
    pub change: Change,
    /// `fn wrap01`, `impl Show for Point`, `use std.math`, ...
    pub key: String,
    /// The item in the old file (for `Removed` and `Changed`).
    pub old: Option<Span>,
    /// The item in the new file (for `Added` and `Changed`).
    pub new: Option<Span>,
    /// For `Changed`: where the first difference is (in the new file when the
    /// change is inside the body, otherwise the item start).
    pub first: Option<Span>,
}

/// Human-readable key of an item (kind + name). Duplicates get `#n`.
fn key(ast: &Ast, id: ItemId) -> String {
    fn raw(ast: &Ast, kind: &ItemKind) -> String {
        match kind {
            ItemKind::Fn(f) => format!("fn {}", f.name.name),
            ItemKind::Flow(f) => format!("flow {}", f.name.name),
            ItemKind::Struct(s) => format!("struct {}", s.name.name),
            ItemKind::Enum(e) => format!("enum {}", e.name.name),
            ItemKind::TypeAlias { name, .. } | ItemKind::OpaqueType { name } => format!("type {}", name.name),
            ItemKind::Trait(t) => format!("trait {}", t.name.name),
            ItemKind::Impl(i) => match &i.trait_ {
                Some(t) => {
                    let names: Vec<&str> = t.segments.iter().map(|s| s.name.as_str()).collect();
                    format!("impl {} for {}", names.join("."), dump_type(ast, i.self_ty))
                }
                None => format!("impl {}", dump_type(ast, i.self_ty)),
            },
            ItemKind::Effect(e) => format!("effect {}", e.name.name),
            ItemKind::Handler(h) => format!("handler {}", h.name.name),
            ItemKind::Const(c) => format!("const {}", c.name.name),
            ItemKind::Use(u) => {
                let names: Vec<&str> = u.path.segments.iter().map(|s| s.name.as_str()).collect();
                format!("use {}", names.join("."))
            }
            ItemKind::Extern(e) => {
                let lib: String = e
                    .lib
                    .segments
                    .iter()
                    .map(|s| match s {
                        crate::ast::StrSeg::Text(t) => t.clone(),
                        crate::ast::StrSeg::Interp(_) => String::new(),
                    })
                    .collect();
                format!("extern lib {lib}")
            }
            ItemKind::Target(inner) => format!("target {}", raw(ast, inner)),
            ItemKind::Test { name, .. } => {
                let text: String = name
                    .segments
                    .iter()
                    .map(|s| match s {
                        crate::ast::StrSeg::Text(t) => t.clone(),
                        crate::ast::StrSeg::Interp(_) => String::new(),
                    })
                    .collect();
                format!("test \"{text}\"")
            }
        }
    }
    raw(ast, &ast.item(id).kind)
}

fn keyed(ast: &Ast) -> Vec<(String, ItemId)> {
    let mut seen: HashMap<String, usize> = HashMap::new();
    ast.root
        .iter()
        .map(|&id| {
            let k = key(ast, id);
            let n = seen.entry(k.clone()).or_insert(0);
            *n += 1;
            (if *n == 1 { k } else { format!("{k} #{n}") }, id)
        })
        .collect()
}

fn body(ast: &Ast, id: ItemId) -> Option<&Block> {
    let expr = match &ast.item(id).kind {
        ItemKind::Fn(f) => f.body?,
        ItemKind::Flow(f) => f.body,
        ItemKind::Test { body, .. } => *body,
        _ => return None,
    };
    match &ast.expr(expr).kind {
        ExprKind::Block(b) => Some(b),
        _ => None,
    }
}

/// First statement (or tail) of the new body whose dump differs from the old one.
fn first_difference(old: &Ast, old_id: ItemId, new: &Ast, new_id: ItemId) -> Option<Span> {
    let (ob, nb) = (body(old, old_id)?, body(new, new_id)?);
    for (i, &ns) in nb.stmts.iter().enumerate() {
        match ob.stmts.get(i) {
            Some(&os) if dump_stmt(old, os) == dump_stmt(new, ns) => continue,
            _ => return Some(new.stmt(ns).span),
        }
    }
    if ob.stmts.len() > nb.stmts.len() {
        // Statements were removed: point at the end of the new body.
        return nb.tail.map(|t| new.expr(t).span).or_else(|| nb.stmts.last().map(|&s| new.stmt(s).span));
    }
    match (ob.tail, nb.tail) {
        (Some(ot), Some(nt)) if crate::dump::dump_expr(old, ot) == crate::dump::dump_expr(new, nt) => None,
        (_, Some(nt)) => Some(new.expr(nt).span),
        _ => None,
    }
}

/// Compare two parsed files. Items keep the new file's order; removed items
/// come last.
pub fn diff(old: &Parsed, new: &Parsed) -> Vec<ItemDiff> {
    let old_items = keyed(&old.ast);
    let new_items = keyed(&new.ast);
    let old_map: HashMap<&str, ItemId> = old_items.iter().map(|(k, id)| (k.as_str(), *id)).collect();
    let new_map: HashMap<&str, ItemId> = new_items.iter().map(|(k, id)| (k.as_str(), *id)).collect();
    let mut out = Vec::new();
    for (k, nid) in &new_items {
        let new_span = new.ast.item(*nid).span;
        match old_map.get(k.as_str()) {
            None => out.push(ItemDiff {
                change: Change::Added,
                key: k.clone(),
                old: None,
                new: Some(new_span),
                first: None,
            }),
            Some(&oid) => {
                if dump_item(&old.ast, oid) != dump_item(&new.ast, *nid) {
                    let first = first_difference(&old.ast, oid, &new.ast, *nid).unwrap_or(new_span);
                    out.push(ItemDiff {
                        change: Change::Changed,
                        key: k.clone(),
                        old: Some(old.ast.item(oid).span),
                        new: Some(new_span),
                        first: Some(first),
                    });
                }
            }
        }
    }
    for (k, oid) in &old_items {
        if !new_map.contains_key(k.as_str()) {
            out.push(ItemDiff {
                change: Change::Removed,
                key: k.clone(),
                old: Some(old.ast.item(*oid).span),
                new: None,
                first: None,
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use onsa_diag::FileId;

    fn d(a: &str, b: &str) -> Vec<(Change, String)> {
        let (pa, pb) = (crate::parse(FileId(0), a), crate::parse(FileId(1), b));
        diff(&pa, &pb).into_iter().map(|x| (x.change, x.key)).collect()
    }

    #[test]
    fn whitespace_and_comments_are_ignored() {
        assert!(d("fn f(x: F32) -> F32 { x }\n", "// c\nfn f(x: F32)   -> F32 {\n  x // v\n}\n").is_empty());
    }

    #[test]
    fn added_removed_changed() {
        let old = "fn f() -> I32 { 1 }\nstruct A { x: F32 }\nconst N: U32 = 1\n";
        let new = "fn f() -> I32 { 2 }\nconst N: U32 = 1\nimpl A { fn g(self) {} }\n";
        assert_eq!(
            d(old, new),
            vec![
                (Change::Changed, "fn f".into()),
                (Change::Added, "impl A".into()),
                (Change::Removed, "struct A".into()),
            ]
        );
    }

    #[test]
    fn first_difference_points_at_the_changed_statement() {
        let old = "fn f() -> I32 {\n  let a = 1\n  let b = 2\n  a\n}\n";
        let new = "fn f() -> I32 {\n  let a = 1\n  let b = 3\n  a\n}\n";
        let (pa, pb) = (crate::parse(FileId(0), old), crate::parse(FileId(1), new));
        let out = diff(&pa, &pb);
        let first = out[0].first.unwrap();
        assert_eq!(&new[first.start as usize..first.end as usize], "let b = 3");
    }

    #[test]
    fn duplicate_keys_are_numbered() {
        let old = "impl A { fn f(self) {} }\nimpl A { fn g(self) {} }\n";
        let new = "impl A { fn f(self) {} }\nimpl A { fn h(self) {} }\n";
        assert_eq!(d(old, new), vec![(Change::Changed, "impl A #2".into())]);
    }
}
