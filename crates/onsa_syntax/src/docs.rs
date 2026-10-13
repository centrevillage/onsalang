//! The doc comments that document nothing (§2.1, S-51): E0004, found once
//! on the CST after the parser, which alone decides where a doc comment is
//! attached (`Parser::attach_docs`, the `Docs` and `ModuleDocs` nodes; D-15).
//!
//! - A `///` documents the declaration its `Docs` node is in: an item but
//!   `use` and `test`, a member of an `impl` or a `trait`, a field, a
//!   variant, an input of a flow. Anywhere else (before a statement, a
//!   parameter of a function, a `use`, the end of the file, ...) it is
//!   E0004, with the candidate `//`.
//! - A `//!` documents the module at the head of the file (`ModuleDocs`).
//!   Anywhere else it is E0004, with the candidate `///` where a `///`
//!   documents a declaration.
//!
//! One diagnostic for a run of doc comments of one kind with nothing but
//! blank lines and plain comments between them (one error, the lines meant
//! for one declaration), with one candidate that edits each line.

// A run of doc comments that document nothing is one E0004, with one candidate (S-442).
// SPEC-GAP(S-432): a `///` after the attributes of a declaration is in no `Docs`: E0004.
// SPEC-GAP(S-433): a `///` before an element of a variant is in no `Docs`: E0004 (there is no tuple struct, S-39).
// SPEC-GAP(S-444): a `///` after code on its line is in no `Docs` (`Parser::starts_its_line`): E0004.
// SPEC-GAP(S-434): a `//!` after the `///` of the first item is not at the head of the file: E0004.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::cst::{Cst, NodeId, NodeKind, TokenIdx};
use crate::token::TokenKind;

/// Where a doc comment is (from the node that holds it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    /// At the head of the file: a `//!` documents the module.
    Head,
    /// In the `Docs` of a declaration that takes a doc comment.
    Documents,
    /// Anywhere else: in no `Docs`, or in the `Docs` of a declaration that
    /// takes none.
    Nothing,
    /// In a node a syntax error stopped the parser in, or in the tokens its
    /// recovery skipped: where the parser read no element, it attached no
    /// doc comment, and the syntax error is the unit's (a missing `,` before
    /// the next element and its `///`, §2.5, S-236).
    Unread,
}

/// The E0004 of the doc comments of `cst` (the source is `text`), added to
/// `out`.
pub(crate) fn check(cst: &Cst, text: &str, out: &mut Vec<Diagnostic>) {
    // The runs: (kind, place, first token, last token).
    let mut run: Option<(TokenKind, Place, usize, usize)> = None;
    let tokens = cst.tokens();
    for (i, t) in tokens.iter().enumerate() {
        if t.kind.is_doc() {
            let place = place(cst, cst.token_parent(TokenIdx(i as u32)));
            match &mut run {
                Some((kind, p, _, last)) if *kind == t.kind && *p == place => *last = i,
                _ => {
                    if let Some(r) = run.take() {
                        report(cst, text, r, out);
                    }
                    run = Some((t.kind, place, i, i));
                }
            }
        } else if !(matches!(t.kind, TokenKind::Whitespace | TokenKind::Newline | TokenKind::Comment)) {
            if let Some(r) = run.take() {
                report(cst, text, r, out);
            }
        }
    }
    if let Some(r) = run.take() {
        report(cst, text, r, out);
    }
}

/// The place of a doc comment held by the node `n`.
fn place(cst: &Cst, n: NodeId) -> Place {
    match cst.kind(n) {
        NodeKind::ModuleDocs => Place::Head,
        NodeKind::Docs if documents(cst, n) => Place::Documents,
        NodeKind::Error => Place::Unread,
        _ if !cst.is_complete(n) => Place::Unread,
        _ => Place::Nothing,
    }
}

/// Whether the declaration of the `Docs` node `docs` takes a doc comment
/// (§2.1): not a `use` or a `test`, nor a member of an `effect`, a
/// `handler` or an `extern` (S-431: §2.1 names the members of an `impl` and
/// a `trait` only).
fn documents(cst: &Cst, docs: NodeId) -> bool {
    let Some(owner) = cst.parent(docs) else { return false };
    match cst.kind(owner) {
        NodeKind::Field | NodeKind::Variant | NodeKind::Param => true,
        NodeKind::Item => {
            let declaration = cst
                .child_nodes(owner)
                .find(|&c| !matches!(cst.kind(c), NodeKind::Docs | NodeKind::Attr | NodeKind::Vis | NodeKind::Error));
            if declaration.is_some_and(|d| matches!(cst.kind(d), NodeKind::Use | NodeKind::Test)) {
                return false;
            }
            // SPEC-GAP(S-431): a member of an `effect`, a `handler` or an
            // `extern` takes no doc comment (§2.1 lists those of `impl` and
            // `trait`).
            let list = cst.parent(owner).filter(|&l| cst.kind(l) == NodeKind::ItemList);
            let around = list.and_then(|l| cst.parent(l)).map(|a| cst.kind(a));
            !matches!(around, Some(NodeKind::Effect | NodeKind::Handler | NodeKind::Extern))
        }
        _ => false,
    }
}

/// The E0004 of the run `(kind, place, first, last)`, when it documents
/// nothing.
fn report(
    cst: &Cst,
    text: &str,
    (kind, place, first, last): (TokenKind, Place, usize, usize),
    out: &mut Vec<Diagnostic>,
) {
    let tokens = &cst.tokens()[first..=last];
    let lines = tokens.iter().filter(|t| t.kind == kind);
    let span = Span::new(tokens[0].span.file, tokens[0].span.start, tokens[tokens.len() - 1].span.end);
    let replaced = |prefix: &str| {
        lines
            .clone()
            .map(|t| {
                Edit::replace(t.span, format!("{prefix}{}", &text[t.span.start as usize + 3..t.span.end as usize]))
            })
            .collect()
    };
    let d = match (kind, place) {
        (TokenKind::DocComment, Place::Documents) | (TokenKind::ModuleDoc, Place::Head) | (_, Place::Unread) => return,
        (TokenKind::DocComment, _) => Diagnostic::new(
            Stage::Syntax,
            Code::E0004,
            span,
            "this doc comment documents no declaration; `///` goes right before an item, a member, a field, a variant or an input of a flow (§2.1)",
        )
        .with_fix(Fix::new("make it a plain comment `//`", replaced("//"))),
        (_, Place::Documents) => Diagnostic::new(
            Stage::Syntax,
            Code::E0004,
            span,
            "`//!` documents the module only at the head of the file; the declaration after it takes `///` (§2.1)",
        )
        .with_fix(Fix::new("make it a doc comment `///`", replaced("///"))),
        // `///` would document nothing here either, so no candidate (S-430;
        // §18.1: a candidate leaves no error of its stage).
        _ => Diagnostic::new(
            Stage::Syntax,
            Code::E0004,
            span,
            "`//!` documents the module only at the head of the file, before the first item (§2.1)",
        ),
    };
    out.push(d);
}

#[cfg(test)]
mod tests {
    use onsa_diag::{Code, FileId};

    fn parse(src: &str) -> crate::Parsed {
        crate::parse(FileId(0), src)
    }

    /// The E0004 of `src`: their texts, and the text after their candidate (if any).
    fn e0004(src: &str) -> Vec<(String, Option<String>)> {
        let p = parse(src);
        p.diagnostics
            .iter()
            .filter(|d| d.code == Code::E0004)
            .map(|d| {
                let fixed = d.fixes.first().map(|f| {
                    let mut out = src.to_string();
                    let mut edits = f.edits().to_vec();
                    edits.sort_by_key(|e| std::cmp::Reverse(e.span.start));
                    for e in edits {
                        out.replace_range(e.span.start as usize..e.span.end as usize, &e.replace);
                    }
                    out
                });
                (src[d.span.start as usize..d.span.end as usize].to_string(), fixed)
            })
            .collect()
    }

    #[test]
    fn a_doc_comment_documents_a_field_a_variant_and_an_input_of_a_flow() {
        let src = "//! m\n//! n\n\n/// s\nstruct S {\n  /// a\n  a: I32,\n  b: I32,\n}\n\
                   enum E {\n  /// A\n  A,\n}\n\
                   flow f(\n  /// x\n  x: F32 at sample,\n) -> F32 at sample {\n  x\n}\n";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let text = |s: &onsa_diag::Span| &src[s.start as usize..s.end as usize];
        assert_eq!(p.ast.module_doc.iter().map(text).collect::<Vec<_>>(), ["//! m", "//! n"]);
        use crate::ast::ItemKind;
        let items: Vec<&crate::ast::Item> = p.ast.root.iter().map(|&i| p.ast.item(i)).collect();
        assert_eq!(items[0].doc.iter().map(text).collect::<Vec<_>>(), ["/// s"]);
        let ItemKind::Struct(s) = &items[0].kind else { panic!("{:?}", items[0].kind) };
        let fields = &s.fields;
        assert_eq!(fields[0].doc.iter().map(text).collect::<Vec<_>>(), ["/// a"]);
        assert!(fields[1].doc.is_empty());
        let ItemKind::Enum(e) = &items[1].kind else { panic!("{:?}", items[1].kind) };
        assert_eq!(e.variants[0].doc.iter().map(text).collect::<Vec<_>>(), ["/// A"]);
        let ItemKind::Flow(f) = &items[2].kind else { panic!("{:?}", items[2].kind) };
        assert_eq!(f.params[0].doc.iter().map(text).collect::<Vec<_>>(), ["/// x"]);
    }

    #[test]
    fn a_doc_comment_that_documents_nothing_is_e0004() {
        let plain = |src: &str, doc: &str| (doc.to_string(), Some(src.replacen(doc, &doc.replacen("///", "//", 1), 1)));
        for (src, doc) in [
            ("fn f() {\n  /// s\n  1\n}\n", "/// s"),
            ("fn f(\n  /// x\n  x: I32,\n) {\n}\n", "/// x"),
            ("/// u\nuse std.math\n", "/// u"),
            ("/// t\ntest \"a\" {\n  assert true\n}\n", "/// t"),
            ("fn f() {\n}\n/// end", "/// end"),
            ("struct S {\n  a: I32,\n  /// none\n}\n", "/// none"),
            // SPEC-GAP(S-444): after code on its line.
            ("const A: I32 = 1 /// doc\nfn f() {\n}\n", "/// doc"),
            ("struct S {\n  a: I32, /// a\n  b: I32,\n}\n", "/// a"),
            // SPEC-GAP(S-432): after the attributes.
            ("@repr(c)\n/// d\nstruct S {\n  a: I32,\n}\n", "/// d"),
            // SPEC-GAP(S-433): an element of a variant (there is no tuple struct, S-39).
            ("enum E {\n  V(\n    /// x\n    F32\n  ),\n}\n", "/// x"),
            // SPEC-GAP(S-431): a member of an `extern` or a `handler`.
            ("extern \"C\" lib \"m\" {\n  /// sin\n  fn sin(x: F64) -> F64\n}\n", "/// sin"),
            ("handler h: E {\n  /// op\n  fn op() -> I32 { 1 }\n}\n", "/// op"),
        ] {
            assert_eq!(e0004(src), vec![plain(src, doc)], "{src}");
        }
        // A member of an `impl` and a `trait` takes one.
        assert!(e0004("impl S {\n  /// m\n  fn m() {}\n}\ntrait T {\n  /// n\n  fn n()\n}\n").is_empty());
    }

    #[test]
    fn the_doc_comments_after_a_missing_comma_are_not_e0004() {
        // W3-04/b 1: the parser stopped in the list; its E0002 is the unit's,
        // and its candidate `,` lets the next element take them.
        for src in [
            "struct S {\n  a: I32\n  /// d\n  b: I32,\n}\n",
            "struct S {\n  a: I32\n  /// d\n  /// e\n  b: I32,\n}\n",
            "enum E {\n  A\n  /// d\n  B,\n}\n",
            "flow f(\n  x: F32 at sample\n  /// d\n  y: F32 at sample,\n) -> F32 at sample {\n  x\n}\n",
        ] {
            let p = parse(src);
            let codes: Vec<Code> = p.diagnostics.iter().map(|d| d.code).collect();
            assert_eq!(codes, [Code::E0002], "{src}");
        }
        // A list read whole keeps its E0004.
        assert_eq!(e0004("struct S {\n  a: I32,\n  /// none\n}\n").len(), 1);
    }

    #[test]
    fn a_doc_comment_in_a_list_that_hugs_its_opener_documents_its_element() {
        let src = "struct S { a: I32,\n           /// d\n           b: I32 }\n";
        let p = parse(src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let crate::ast::ItemKind::Struct(s) = &p.ast.item(p.ast.root[0]).kind else { panic!("not a struct") };
        let fields = &s.fields;
        assert_eq!(fields[1].doc.len(), 1);
        // fmt keeps it on its own line (W3-04/b 2), also after a comment that
        // the element before holds (W3-04/b 6).
        assert_eq!(crate::format(&p, src).as_deref(), Some(src));
        let src = "struct S { f1: Buf[\n// k\nI32\n],\n/// d2\nf2: I32,\n}\n";
        let out = crate::format(&parse(src), src).unwrap();
        assert_eq!(out, "struct S { f1: Buf[I32], // k\n           /// d2\n           f2: I32 }\n");
        assert!(parse(&out).diagnostics.is_empty());
    }

    #[test]
    fn one_e0004_for_a_run_of_doc_comments() {
        let src = "fn f() {\n}\n/// one\n// plain\n/// two\n";
        let want =
            ("/// one\n// plain\n/// two".to_string(), Some("fn f() {\n}\n// one\n// plain\n// two\n".to_string()));
        assert_eq!(e0004(src), vec![want]);
    }

    #[test]
    fn a_module_doc_after_the_head_is_e0004() {
        // `///` where a declaration follows to take it.
        let src = "fn f() {\n}\n//! a\n//! b\nfn g() {\n}\n";
        let want = ("//! a\n//! b".to_string(), Some("fn f() {\n}\n/// a\n/// b\nfn g() {\n}\n".to_string()));
        assert_eq!(e0004(src), vec![want]);
        // SPEC-GAP(S-434): after the `///` of the first item.
        let want = ("//! b".to_string(), Some("/// a\n/// b\nfn f() {\n}\n".to_string()));
        assert_eq!(e0004("/// a\n//! b\nfn f() {\n}\n"), vec![want]);
        // Nothing to document: no candidate (S-430).
        assert_eq!(e0004("fn f() {\n}\n//! late\n"), vec![("//! late".to_string(), None)]);
        assert_eq!(e0004("fn f() {\n  //! in\n  1\n}\n"), vec![("//! in".to_string(), None)]);
    }

    #[test]
    fn a_doc_comment_after_an_error_in_a_list_attaches_to_nothing_before_it() {
        // The doc comments are taken before an element, never after one
        // (W3-01/b M-1): after a failed field, the unit has its error first,
        // and the next item keeps its own.
        let p = parse("struct S {\n  a: ,\n  /// b\n  b: I32,\n}\n/// g\nfn g() {\n}\n");
        let g = p.ast.root.iter().map(|&i| p.ast.item(i)).find(|i| i.failed.is_none()).unwrap();
        assert_eq!(g.doc.len(), 1);
        assert_eq!(p.diagnostics[0].code, Code::E0002);
    }
}
