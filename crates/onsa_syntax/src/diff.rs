//! `onsa diff --ast` (spec §18.2, T1-10) and the check of `onsa fmt` before
//! it writes ([`same_program`]): the one comparison of two files of
//! `spec/tools.md` §3.5. Both compare the dumps of the items after the
//! rewrites of §3.3 on both trees ([`crate::fmt::rewrites`]): the structure
//! alone, without the comments (S-534: the AST has no doc comments either,
//! D-02). `diff --ast` matches the items by kind and name; the check also
//! wants the items in the same order, the doc comments on the same
//! declarations ([`crate::docs::documented`]) and every comment (`///` and
//! `//!` too) in the same order.

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

/// The members of an item that holds some: the functions and constants of
/// an `impl`, a trait, a handler or an `extern` block, the operations of an
/// effect, through a `target`.
fn members(kind: &ItemKind) -> Option<&[ItemId]> {
    match kind {
        ItemKind::Impl(i) => Some(&i.items),
        ItemKind::Trait(t) => Some(&t.items),
        ItemKind::Handler(h) => Some(&h.items),
        ItemKind::Effect(e) => Some(&e.ops),
        ItemKind::Extern(e) => Some(&e.items),
        ItemKind::Target(inner) => members(inner),
        _ => None,
    }
}

fn body<'a>(ast: &'a Ast, kind: &ItemKind) -> Option<&'a Block> {
    let expr = match kind {
        ItemKind::Fn(f) => f.body?,
        ItemKind::Flow(f) => f.body,
        ItemKind::Test { body, .. } => *body,
        ItemKind::Target(inner) => return body(ast, inner),
        _ => return None,
    };
    match &ast.expr(expr).kind {
        ExprKind::Block(b) => Some(b),
        _ => None,
    }
}

/// Where the item `new_id` of `new` first differs from `old_id` of `old`:
/// the first member whose dump differs, and in it (or in the item) the
/// first statement (or the value) of the body whose dump differs. `None`
/// when no member or statement does (the head of the item differs).
fn first_difference(old: &Side, old_id: ItemId, new: &Side, new_id: ItemId) -> Option<Span> {
    let (ok, nk) = (&old.ast.item(old_id).kind, &new.ast.item(new_id).kind);
    if let (Some(om), Some(nm)) = (members(ok), members(nk)) {
        for (i, &n) in nm.iter().enumerate() {
            match om.get(i) {
                Some(&o) if old.dump(o) == new.dump(n) => continue,
                Some(&o) => return first_difference(old, o, new, n).or(Some(new.ast.item(n).span)),
                None => return Some(new.ast.item(n).span),
            }
        }
        // Members were removed: the last member of the new item.
        return nm.last().filter(|_| om.len() > nm.len()).map(|&n| new.ast.item(n).span);
    }
    let (old, new) = (&old.ast, &new.ast);
    let (ob, nb) = (body(old, ok)?, body(new, nk)?);
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
/// its tree and its items by key.
struct Side<'a> {
    ast: Ast,
    parsed: &'a Parsed,
    items: Vec<(String, ItemId)>,
}

impl<'a> Side<'a> {
    /// `parsed` has no diagnostic of the syntax stage (`normalize`).
    fn new(parsed: &'a Parsed) -> Side<'a> {
        let ast = crate::fmt::rewrites::normalize(parsed);
        let items = keyed(&ast);
        Side { ast, parsed, items }
    }

    fn dump(&self, id: ItemId) -> String {
        dump_item(&self.ast, id)
    }

    /// The declaration that each doc comment of the item `id` and of the
    /// declarations in it documents ([`crate::docs::documented`]): their
    /// texts are compared with the other comments ([`same_program`]).
    fn docs(&self, id: ItemId) -> Vec<usize> {
        let docs = crate::docs::documented(&self.parsed.cst, self.parsed.map.items[id.index()]);
        docs.into_iter().map(|(d, _)| d).collect()
    }
}

/// Compare two parsed files without a diagnostic of the syntax stage (one is
/// an internal error, [`crate::fmt::rewrites::normalize`]): their structure
/// alone, not their comments (S-534). Items keep the new file's order;
/// removed items come last.
pub fn diff(old: &Parsed, new: &Parsed) -> Vec<ItemDiff> {
    let (old, new) = (Side::new(old), Side::new(new));
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
                    let first = first_difference(&old, oid, &new, *nid).unwrap_or(new_span);
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
/// check of `onsa fmt` before it writes (`spec/tools.md` §3.5): the
/// items in the same order, each with the same dump as [`diff`] compares (the
/// rewrites of §3.3 applied, numbers by value) and its doc comments on the
/// same declarations ([`Side::docs`]), then the text of every comment (`///`
/// and `//!` too), in order, without the blanks at the end of the line. `None` if it is; else
/// the first difference. Neither file has a
/// diagnostic of the syntax stage (one is an internal error, as for [`diff`]):
/// `crate::fmt::verify` looks at the output's first.
pub fn same_program(old: &Parsed, old_text: &str, new: &Parsed, new_text: &str) -> Option<Difference> {
    let eof = old.cst.tokens().last().expect("a file ends with its Eof token").span;
    let (o, n) = (Side::new(old), Side::new(new));
    for i in 0..o.items.len().max(n.items.len()) {
        let (place, at) = match (o.items.get(i), n.items.get(i)) {
            (Some((ok, oid)), Some((nk, nid)))
                if ok == nk && o.dump(*oid) == n.dump(*nid) && o.docs(*oid) == n.docs(*nid) =>
            {
                continue;
            }
            (Some((ok, oid)), next) => {
                let same_key = next.filter(|(nk, _)| nk == ok);
                let inner = same_key.and_then(|(_, nid)| first_difference(&n, *nid, &o, *oid));
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
    fn numbers_compare_by_value() {
        // `spec/tools.md` §3.5: the spelling of a number is no difference.
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
        // S-534, D-02: the dump of the AST has no doc comment; their texts are
        // compared with the other comments, a `///` of a member too.
        let a = "/// adds\nfn f() {}\nfn g() {}\n";
        assert_eq!(same(a, &a.replace("adds", "add")), Some((Place::Comment(1), "/// adds".into())));
        let m = "impl S {\n  fn f(self) {} // c\n  /// g\n  fn g(self) {}\n}\n";
        assert_eq!(same(m, &m.replace("/// g", "/// h")), Some((Place::Comment(2), "/// g".into())));
        // A doc comment lost is a declaration without its doc comment.
        assert_eq!(same(m, &m.replace("  /// g\n", "")), item("impl S", "impl S {"));
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
        // Every `return e` in the tail position (§6.1: the branches at the
        // end too) goes; an early `return` and one without a value (S-547) stay.
        let branches = "fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  } else {\n    return 2\n  }\n}\n";
        assert_eq!(same(branches, &branches.replace("return ", "")), None);
        assert_eq!(same("fn f(move a: B) -> B {\n  return move a\n}\n", "fn f(move a: B) -> B {\n  move a\n}\n"), None);
        // The returned `move` is no rewrite (W3-12): it stays and is compared.
        assert!(same("fn f(move a: B) -> B {\n  move a\n}\n", "fn f(move a: B) -> B {\n  a\n}\n").is_some());
        let early = "fn f(c: Bool) -> I32 {\n  if c {\n    return 1\n  }\n  2\n}\n";
        assert!(same(early, &early.replace("return 1", "1")).is_some());
        assert!(same("fn f() {\n  return\n}\n", "fn f() {\n}\n").is_some());
    }

    /// S-534 (a3): `diff --ast` compares the structure alone, not the doc
    /// comments (`///` and `//!`, their texts and their declarations) nor the
    /// ordinary comments; a parenthesis of the same group is a difference
    /// (S-534 (b1)).
    #[test]
    fn diff_ast_compares_the_structure_alone() {
        let a = "//! m\n/// adds\nfn f() {}\nstruct S {\n  /// x\n  a: I32,\n  b: I32,\n}\n";
        for b in [
            a.replace("/// adds", "/// add"),
            a.replace("//! m", "//! n"),
            a.replace("/// adds\n", ""),
            a.replace("  /// x\n  a: I32,\n  b: I32,", "  a: I32,\n  /// x\n  b: I32,"),
            a.replace("fn f() {}", "fn f() {} // c"),
        ] {
            assert!(d(a, &b).is_empty(), "{b}");
        }
        let p = "fn f(a: I32, b: I32, c: I32) -> I32 {\n  (a + b) + c\n}\n";
        assert_eq!(d(p, &p.replace("(a + b) + c", "a + b + c")), vec![(Change::Changed, "fn f".into())]);
    }

    /// W3-12/b 1: §8.1 and §11.4 put a `uses` and a clock after the result of
    /// a function on that function, so the dump writes a function type there
    /// between `<` and `>`: `fn() -> I32 uses {} uses {Alloc}` and `fn() ->
    /// I32 uses {Alloc}` as the result are two programs.
    #[test]
    fn the_uses_after_a_function_type_in_the_result_is_told_apart() {
        let differ = |a: &str, b: &str| !d(a, b).is_empty();
        assert!(differ("fn f() -> fn() uses {} uses {Alloc} {}\n", "fn f() -> fn() uses {Alloc} {}\n"));
        assert!(differ("type M = fn() -> fn() -> I32 uses {Alloc}\n", "type M = fn() -> (fn() -> I32) uses {Alloc}\n"));
        assert!(differ("fn f() -> fn() -> I32 uses {} uses {A} {}\n", "fn f() -> fn() -> I32 uses {A} {}\n"));
        assert!(!differ("fn f() -> fn() uses {Alloc} {}\n", "fn f()  ->  fn()  uses {Alloc} {}\n"));
    }

    /// S-56: the first difference goes down to the first member that differs
    /// of an item that holds some, and into the body of that member; the
    /// key of the item stays the one of the item.
    #[test]
    fn the_first_difference_goes_down_to_a_member_and_its_body() {
        let item = |text: &str| Some((Place::Item("impl S".into()), text.to_string()));
        let a = "impl S {\n  fn f(self) -> I32 { 1 }\n  fn g(self) -> I32 {\n    let x = 1\n    x\n  }\n}\n";
        assert_eq!(same(a, &a.replace("let x = 1", "let x = 2")), item("let x = 1"));
        assert_eq!(same(a, &a.replace("fn g(self) -> I32", "fn g(self) -> I64")), item("fn g(self) -> I32 {"));
        assert_eq!(same(a, &a.replace("impl S", "impl[T] S")).map(|d| d.0), Some(Place::Item("impl S".into())));
        let e = "effect Beep {\n  fn beep() -> I32\n  fn bop() -> I32\n}\n";
        let got = same(e, &e.replace("bop() -> I32", "bop() -> I64"));
        assert_eq!(got, Some((Place::Item("effect Beep".into()), "fn bop() -> I32".into())));
        let h = "handler quiet: Beep {\n  fn beep(level: I32) -> I32 {\n    let a = level\n    a\n  }\n}\n";
        let got = same(h, &h.replace("let a = level", "let a = 0"));
        assert_eq!(got, Some((Place::Item("handler quiet".into()), "let a = level".into())));
        // `diff --ast` points into the new file.
        let (pa, pb) = (crate::parse(FileId(0), a), crate::parse(FileId(1), &a.replace("let x = 1", "let x = 3")));
        let b = a.replace("let x = 1", "let x = 3");
        let first = diff(&pa, &pb)[0].first.unwrap();
        assert_eq!(&b[first.start as usize..first.end as usize], "let x = 3");
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
