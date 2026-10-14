//! `onsa diff --ast` (spec §18.2, T1-10) and the check of `onsa fmt` before
//! it writes ([`same_program`]): the one comparison of two files of
//! `docs/onsa-tools.md` §3.5. Both compare the dumps of the items, with the
//! text of their doc comments, after the rewrites of §3.3 on both trees
//! ([`crate::fmt::rewrites`]). `diff --ast` matches the items by kind and
//! name and ignores the comments and the whitespace; the check also wants the
//! items in the same order and the same comments in the same order.

use std::collections::HashMap;
use std::fmt;

use onsa_diag::Span;

use crate::ast::{Ast, Block, ExprKind, ItemId, ItemKind};
use crate::dump::{dump_item, dump_stmt, dump_type};
use crate::lexer::comment_text;
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

/// A file as the comparison reads it: its AST after the rewrites of §3.3,
/// its source and its items by key.
struct Side<'a> {
    ast: Ast,
    text: &'a str,
    items: Vec<(String, ItemId)>,
}

impl<'a> Side<'a> {
    /// `parsed` has no diagnostic of the syntax stage (`normalize`).
    fn new(parsed: &Parsed, text: &'a str) -> Side<'a> {
        let ast = crate::fmt::rewrites::normalize(parsed);
        let items = keyed(&ast);
        Side { ast, text, items }
    }

    fn dump(&self, id: ItemId) -> String {
        dump_item(&self.ast, self.text, id)
    }
}

/// Compare two parsed files (`old_text` and `new_text` are their sources),
/// without a diagnostic of the syntax stage (one is an internal error,
/// [`crate::fmt::rewrites::normalize`]). Items keep the new file's order;
/// removed items come last.
pub fn diff(old: &Parsed, old_text: &str, new: &Parsed, new_text: &str) -> Vec<ItemDiff> {
    let (old, new) = (Side::new(old, old_text), Side::new(new, new_text));
    let (old_items, new_items) = (&old.items, &new.items);
    let old_map: HashMap<&str, ItemId> = old_items.iter().map(|(k, id)| (k.as_str(), *id)).collect();
    let new_map: HashMap<&str, ItemId> = new_items.iter().map(|(k, id)| (k.as_str(), *id)).collect();
    let mut out = Vec::new();
    for (k, nid) in new_items {
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
                if old.dump(oid) != new.dump(*nid) {
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
    for (k, oid) in old_items {
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

/// Where the new file first stops being the program of the old one
/// ([`same_program`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Difference {
    pub place: Place,
    /// The position in the old file: the first statement that differs in
    /// the body of the item, else the item; the comment; the end of the file
    /// for what the new file has more; the start of the file for
    /// [`Place::Unparsed`].
    pub at: Span,
}

/// What differs ([`Difference`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Place {
    /// The item of the old file (its key) and the item at its place in the
    /// new file differ, or the new file has no item there.
    Item(String),
    /// The new file has an item more (its key), after those of the old one.
    ExtraItem(String),
    /// The `n`-th comment of the old file (from 1, every comment, `///` and
    /// `//!` too) and the `n`-th of the new file differ, or the new file has
    /// fewer comments.
    Comment(usize),
    /// The new file has a comment more, its `n`-th.
    ExtraComment(usize),
    /// The new file has a diagnostic of the syntax stage (what it says): the
    /// check of `onsa fmt` (`crate::fmt::verify`) sees it before it compares.
    Unparsed(String),
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Place::Item(k) => write!(f, "the item `{k}` differs"),
            Place::ExtraItem(k) => write!(f, "the output has an item more, `{k}`"),
            Place::Comment(n) => write!(f, "comment {n} of the file differs or is missing"),
            Place::ExtraComment(n) => write!(f, "the output has a comment more (comment {n})"),
            Place::Unparsed(what) => write!(f, "the output does not parse ({what})"),
        }
    }
}

/// Whether `new` (`new_text`) is the program of `old` (`old_text`), the
/// check of `onsa fmt` before it writes (`docs/onsa-tools.md` §3.5): the
/// items in the same order, each with the same dump as [`diff`] compares (the
/// rewrites of §3.3 applied, numbers by value, the text of the doc comments),
/// then the text of every comment, in order, without the blanks at the end of
/// the line. `None` if it is; else the first difference. Neither file has a
/// diagnostic of the syntax stage (one is an internal error, as for [`diff`]):
/// `crate::fmt::verify` looks at the output's first.
pub fn same_program(old: &Parsed, old_text: &str, new: &Parsed, new_text: &str) -> Option<Difference> {
    let eof = old.cst.tokens().last().expect("a file ends with its Eof token").span;
    let (o, n) = (Side::new(old, old_text), Side::new(new, new_text));
    for i in 0..o.items.len().max(n.items.len()) {
        let (place, at) = match (o.items.get(i), n.items.get(i)) {
            (Some((ok, oid)), Some((nk, nid))) if ok == nk && o.dump(*oid) == n.dump(*nid) => continue,
            (Some((ok, oid)), next) => {
                let same_key = next.filter(|(nk, _)| nk == ok);
                let inner = same_key.and_then(|(_, nid)| first_difference(&n.ast, *nid, &o.ast, *oid));
                (Place::Item(ok.clone()), inner.unwrap_or(o.ast.item(*oid).span))
            }
            (None, Some((nk, _))) => (Place::ExtraItem(nk.clone()), eof),
            (None, None) => unreachable!("within the longer list"),
        };
        return Some(Difference { place, at });
    }
    let comments = |p: &Parsed, text: &'_ str| -> Vec<(Span, String)> {
        let tokens = p.cst.tokens().iter().filter(|t| t.kind.is_comment());
        tokens.map(|t| (t.span, comment_text(text, t.span).to_string())).collect()
    };
    let (oc, nc) = (comments(old, old_text), comments(new, new_text));
    for i in 0..oc.len().max(nc.len()) {
        let (place, at) = match (oc.get(i), nc.get(i)) {
            (Some(a), Some(b)) if a.1 == b.1 => continue,
            (Some(a), _) => (Place::Comment(i + 1), a.0),
            (None, _) => (Place::ExtraComment(i + 1), eof),
        };
        return Some(Difference { place, at });
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use onsa_diag::FileId;

    fn d(a: &str, b: &str) -> Vec<(Change, String)> {
        let (pa, pb) = (crate::parse(FileId(0), a), crate::parse(FileId(1), b));
        diff(&pa, a, &pb, b).into_iter().map(|x| (x.change, x.key)).collect()
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
        let out = diff(&pa, old, &pb, new);
        let first = out[0].first.unwrap();
        assert_eq!(&new[first.start as usize..first.end as usize], "let b = 3");
    }

    #[test]
    fn numbers_compare_by_value() {
        // `docs/onsa-tools.md` §3.5: the spelling of a number is no difference.
        let old = "fn f() -> F64 {\n  let a = 0xff + 1_000\n  1.0e3 + 1E3\n}\n";
        let new = "fn f() -> F64 {\n  let a = 0xFF + 1000\n  1000.0 + 1e3\n}\n";
        assert!(d(old, new).is_empty());
        let old = "fn f(x: F64) -> I32 {\n  match x {\n    -1_0 => 1,\n    _ => 0,\n  }\n}\n";
        assert!(d(old, &old.replace("-1_0", "-10")).is_empty());
        // Two floats an `f64` cannot tell apart are two values.
        assert_eq!(d("fn f() -> F64 { 1.0 }\n", "fn f() -> F64 { 1.00000000000000000001 }\n").len(), 1);
    }

    #[test]
    fn duplicate_keys_are_numbered() {
        let old = "impl A { fn f(self) {} }\nimpl A { fn g(self) {} }\n";
        let new = "impl A { fn f(self) {} }\nimpl A { fn h(self) {} }\n";
        assert_eq!(d(old, new), vec![(Change::Changed, "impl A #2".into())]);
    }

    /// [`same_program`] of two sources: the place and the old text at the
    /// position (to the end of its line).
    fn same(a: &str, b: &str) -> Option<(Place, String)> {
        let (pa, pb) = (crate::parse(FileId(0), a), crate::parse(FileId(1), b));
        assert!(pa.diagnostics.is_empty() && pb.diagnostics.is_empty(), "{:?} {:?}", pa.diagnostics, pb.diagnostics);
        let d = same_program(&pa, a, &pb, b)?;
        assert_eq!(d.at.file, FileId(0));
        let rest = &a[d.at.start as usize..];
        Some((d.place, rest.lines().next().unwrap_or("").to_string()))
    }

    #[test]
    fn same_program_sees_every_comment_in_order() {
        let a = "fn f() {\n  let x = 1 // one\n  // two\n}\n";
        let at = |n: usize, text: &str| Some((Place::Comment(n), text.to_string()));
        // Another text, two comments swapped, a comment lost, a comment twice.
        assert_eq!(same(a, &a.replace("// two", "// twa")), at(2, "// two"));
        assert_eq!(same(a, "fn f() {\n  let x = 1 // two\n  // one\n}\n"), at(1, "// one"));
        assert_eq!(same(a, "fn f() {\n  let x = 1 // one\n}\n"), at(2, "// two"));
        assert_eq!(same(a, "fn f() {\n  let x = 1 // one\n  // one\n  // two\n}\n"), at(2, "// two"));
        // A comment more at the end: the end of the old file.
        let d = same(a, &format!("{a}// three\n")).unwrap();
        assert_eq!(d, (Place::ExtraComment(3), String::new()));
        // The `//!` of the module is a comment too.
        assert_eq!(same("//! m\nfn f() {}\n", "//! n\nfn f() {}\n"), Some((Place::Comment(1), "//! m".into())));
    }

    #[test]
    fn same_program_reads_the_text_of_the_doc_comments_and_their_declaration() {
        let item = |k: &str, text: &str| Some((Place::Item(k.into()), text.to_string()));
        let a = "/// adds\nfn f() {}\nfn g() {}\n";
        let first = same(a, &a.replace("adds", "add"));
        assert!(matches!(&first, Some((Place::Item(k), _)) if k == "fn f"), "{first:?}");
        // The same comments in the same order, on the next declaration.
        assert_eq!(same(a, "fn f() {}\n/// adds\nfn g() {}\n").map(|d| d.0), Some(Place::Item("fn f".into())));
        let s = "struct S {\n  /// d\n  a: I32,\n  b: I32,\n}\n";
        assert_eq!(
            same(s, "struct S {\n  a: I32,\n  /// d\n  b: I32,\n}\n").map(|d| d.0),
            Some(Place::Item("struct S".into()))
        );
        // A statement lost: the position is the statement in the old file.
        let b = "fn f() {\n  let a = 1\n  let b = 2\n}\n";
        assert_eq!(same(b, "fn f() {\n  let a = 1\n}\n"), item("fn f", "let b = 2"));
        // An item more in the new file.
        assert_eq!(same(b, &format!("{b}fn g() {{}}\n")).map(|d| d.0), Some(Place::ExtraItem("fn g".into())));
    }

    #[test]
    fn same_program_ignores_what_fmt_may_change() {
        // The last `return` of a function (§3.3), the spelling of a number,
        // the blanks at the end of a comment, spaces, line breaks and `,`.
        assert_eq!(same("fn f() -> I32 {\n  return 1\n}\n", "fn f() -> I32 {\n  1\n}\n"), None);
        assert_eq!(same("fn f() -> I32 { 0x1f + 1_000 }\n", "fn f() -> I32 { 31 + 1000 }\n"), None);
        assert_eq!(same("/// d \t\nfn f() {} // c\t \n", "/// d\nfn f() {} // c\n"), None);
        assert_eq!(same("fn f( a:I32 ,b:I32 ){ g(a,\n b,) }\n", "fn f(a: I32, b: I32) { g(a, b) }\n"), None);
        // Only that `return`: one in a branch, and one without a value, stay.
        let early = "fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n";
        assert!(same(early, &early.replace("return 1", "1")).is_some());
        assert!(same("fn f() {\n  return\n}\n", "fn f() {\n}\n").is_some());
    }

    /// W3-11/b2 A: the comparison takes trees without a syntax error; one
    /// with an error is an internal error at the entry, before a rewrite.
    #[test]
    fn a_tree_with_a_syntax_error_is_refused_at_the_entry() {
        let caught = std::panic::catch_unwind(|| d("fn f() -> I32 {\n  return 1\n", "fn f() -> I32 {\n  1\n}\n"));
        let payload = caught.expect_err("an internal error");
        let bug = payload.downcast_ref::<onsa_diag::internal::InternalBug>().expect("a bug of the compiler");
        assert!(bug.message.contains("a tree with a syntax error"), "{}", bug.message);
    }

    /// W3-11/b 2: the value after a dead `return` is compared (the rewrite
    /// takes it for no `return`, it does not overwrite it), and two
    /// `return`s at the end keep the first.
    #[test]
    fn the_value_after_a_dead_return_is_compared() {
        let (a, b) = ("fn f() -> I32 {\n  return 1\n  2\n}\n", "fn f() -> I32 {\n  return 1\n  3\n}\n");
        assert_eq!(same(a, b), Some((Place::Item("fn f".into()), "2".into())));
        assert_eq!(d(a, b), vec![(Change::Changed, "fn f".into())]);
        let two = "fn f() -> I32 {\n  return 1\n  return 2\n}\n";
        assert_eq!(same(two, "fn f() -> I32 {\n  return 1\n  2\n}\n"), None);
        assert_eq!(same(two, "fn f() -> I32 {\n  1\n}\n").map(|d| d.0), Some(Place::Item("fn f".into())));
    }
}
