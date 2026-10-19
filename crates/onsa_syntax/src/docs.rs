//! The doc comments that document nothing (§2.1, S-51): E0004, found once
//! on the CST after the parser, which alone decides where a doc comment is
//! attached (`Parser::attach_docs`, the `Docs` and `ModuleDocs` nodes; D-15).
//!
//! - A `///` documents the declaration its `Docs` node is in, from the
//!   closed list of §2.1 (S-431): an item but `use` and `test`, a member
//!   of an `impl`, a `trait`, an `effect`, a `handler` (also one of a
//!   `handle` expression) or an `extern`, a field, a variant, an input of a
//!   flow.
//! - A `///` between the attributes of such a declaration and the
//!   declaration (S-432) is E0004, with the candidate that moves its lines,
//!   each a line of its own, before the first attribute (after the `///`
//!   there); the plain comments and blank lines stay. When the attribute
//!   follows code on its line, a line break goes before the moved lines.
//! - Anywhere else (before a statement, a parameter of a function, a `use`,
//!   the end of the file, ...) a `///` is E0004, with the candidate `//`.
//! - A `//!` documents the module at the head of the file (`ModuleDocs`).
//!   Anywhere else it is E0004, with the candidate `///` where a `///`
//!   documents a declaration.
//!
//! One diagnostic for a run of doc comments of one kind with nothing but
//! blank lines and plain comments between them (one error, the lines meant
//! for one declaration), with one candidate that edits each line.
//!
//! The AST holds no doc comment (D-02): [`doc_comments`] and [`documented`]
//! read them where the parser attached them, on the CST.

// A run of doc comments that document nothing is one E0004, with one candidate (S-442).
// SPEC-GAP(S-433): a `///` before an element of a variant is in no `Docs`: E0004 (there is no tuple struct, S-39).
// SPEC-GAP(S-444): a `///` after code on its line is in no `Docs` (`Parser::starts_its_line`): E0004.
// SPEC-GAP(S-434): a `//!` after the `///` of the first item is not at the head of the file: E0004.

use onsa_diag::{Code, Diagnostic, Edit, Fix, Span, Stage};

use crate::cst::{Cst, Elem, NodeId, NodeKind, TokenIdx};
use crate::lexer::line_head;
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
        } else if !t.kind.is_between_docs() {
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
        NodeKind::Docs if cst.parent(n).is_some_and(|owner| takes_doc(cst, owner)) => Place::Documents,
        NodeKind::Error => Place::Unread,
        _ if !cst.is_complete(n) => Place::Unread,
        _ => Place::Nothing,
    }
}

/// Whether a declaration whose node is `kind` takes a doc comment (§2.1,
/// S-431): every declaration but a `use` and a `test`, at the top level or
/// a member of any body. With [`elements_take_docs`] and [`in_a_heading`],
/// the one judgment of what a `///` documents: this module, the parser
/// (which attaches the doc comments) and the candidates for `/** */`
/// (`foreign::comments`) read it.
pub(crate) fn declaration_takes_doc(kind: NodeKind) -> bool {
    !matches!(kind, NodeKind::Use | NodeKind::Test)
}

/// Whether the elements of the list `list` in the node `around` take doc
/// comments (§2.1): the fields, the variants, and the inputs of a flow (not
/// the parameters of a function, a closure or a handler).
pub(crate) fn elements_take_docs(list: NodeKind, around: NodeKind) -> bool {
    match list {
        NodeKind::FieldList | NodeKind::VariantList => true,
        NodeKind::ParamList => around == NodeKind::Flow,
        _ => false,
    }
}

/// Whether a `///` in a node of `kind`, past where it starts, is between
/// the attributes of a declaration and the declaration, where it documents
/// nothing (S-432): an `Item` and a `Param` start at their attributes and
/// hold their doc comments in `Docs`, before them.
pub(crate) fn in_a_heading(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::Item | NodeKind::Param)
}

/// Whether a node of `kind` is a declaration that can hold a `Docs` node:
/// an item, a field, a variant or a parameter. The nodes [`takes_doc`]
/// judges and [`documented`] numbers.
fn may_take_doc(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::Item | NodeKind::Field | NodeKind::Variant | NodeKind::Param)
}

/// Whether the declaration of the node `owner` takes a doc comment (§2.1).
fn takes_doc(cst: &Cst, owner: NodeId) -> bool {
    let around = |n: NodeId| cst.parent(n).map(|p| cst.kind(p));
    match cst.kind(owner) {
        kind if !may_take_doc(kind) => false,
        NodeKind::Item => crate::units::declaration(cst, owner).is_none_or(|d| declaration_takes_doc(cst.kind(d))),
        // A field, a variant or a parameter: an element of a list.
        _ => cst.parent(owner).is_some_and(|list| around(list).is_some_and(|a| elements_take_docs(cst.kind(list), a))),
    }
}

/// The doc comments of the declaration of the node `n` (an `Item`, a
/// `Field`, a `Variant` or a `Param`: the `///` of its `Docs`), or of the
/// module when `n` is the root (the `//!` of its `ModuleDocs`), in order.
pub(crate) fn doc_comments(cst: &Cst, n: NodeId) -> Vec<TokenIdx> {
    let (holder, kind) = match n == cst.root() {
        true => (NodeKind::ModuleDocs, TokenKind::ModuleDoc),
        false => (NodeKind::Docs, TokenKind::DocComment),
    };
    let holders = cst.child_nodes(n).filter(|&c| cst.kind(c) == holder);
    let tokens = holders.flat_map(|c| cst.children(c)).filter_map(|e| match *e {
        Elem::Token(t) if cst.token(t).kind == kind => Some(t),
        _ => None,
    });
    tokens.collect()
}

/// The doc comments of the declarations in the node `n` and below, in the
/// order of the source, each with the declaration it documents: its number
/// among the declarations there (the nodes of [`may_take_doc`], in the order
/// of the source). The check of `onsa fmt` compares them (a doc comment that
/// moves to another declaration documents another one, `spec/tools.md`
/// §3.5).
pub(crate) fn documented(cst: &Cst, n: NodeId) -> Vec<(usize, TokenIdx)> {
    let (mut out, mut stack, mut number) = (Vec::new(), vec![n], 0);
    while let Some(d) = stack.pop() {
        if may_take_doc(cst.kind(d)) {
            out.extend(doc_comments(cst, d).into_iter().map(|t| (number, t)));
            number += 1;
        }
        let at = stack.len();
        stack.extend(cst.child_nodes(d));
        stack[at..].reverse();
    }
    out
}

/// The edits that move the run of `///` from `first` to `last` before the
/// first attribute of the declaration (S-432), when the run stands between
/// its attributes and it, each line of the run a line of its own: the lines
/// (with their indentation and line break) go to the head of the line of
/// the first attribute, after the `///` there. When the attribute follows
/// code on its line, a line break goes before the lines, and the attribute
/// starts the next line. The plain comments and blank lines stay.
/// The lines move as they are written (the decision inserts the same lines):
/// their indentation and the spelling of their line breaks are kept, and
/// the line break added before an attribute that follows code takes the
/// indentation of the first line.
fn before_the_attributes(cst: &Cst, text: &str, first: usize, last: usize) -> Option<Vec<Edit>> {
    let tokens = cst.tokens();
    let owner = cst.token_parent(TokenIdx(first as u32));
    if !in_a_heading(cst.kind(owner)) || !takes_doc(cst, owner) {
        return None;
    }
    // The first attribute, after the `Docs`. The run stands before what
    // follows the attributes (`inout` of an input, the declaration); its
    // lines are tokens of the owner, as nothing but trivia is between them.
    let attr =
        cst.child_nodes(owner).find(|&c| cst.kind(c) != NodeKind::Docs).filter(|&a| cst.kind(a) == NodeKind::Attr)?;
    let at = cst.significant_tokens(attr)?.0.index();
    let after = cst.children(owner).iter().find_map(|e| match *e {
        Elem::Node(n) if !matches!(cst.kind(n), NodeKind::Docs | NodeKind::Attr) => {
            cst.significant_tokens(n).map(|t| t.0.index())
        }
        Elem::Token(t) if !tokens[t.index()].kind.is_trivia() => Some(t.index()),
        _ => None,
    });
    if after.is_some_and(|a| a < first) {
        return None;
    }
    let file = tokens[first].span.file;
    let (mut moved, mut edits) = (String::new(), Vec::new());
    for k in (first..=last).filter(|&k| tokens[k].kind == TokenKind::DocComment) {
        let head = line_head(text, tokens[k].span.start)?;
        let newline = tokens.get(k + 1).filter(|t| t.kind == TokenKind::Newline)?;
        moved.push_str(&text[head as usize..newline.span.end as usize]);
        edits.push(Edit::delete(Span::new(file, head, newline.span.end)));
    }
    edits.push(match line_head(text, tokens[at].span.start) {
        Some(head) => Edit::insert(file, head, moved),
        None => {
            let line_break = &text[tokens[first + 1].span.start as usize..tokens[first + 1].span.end as usize];
            let indent = &text[line_head(text, tokens[first].span.start)? as usize..tokens[first].span.start as usize];
            let from = if tokens[at - 1].kind == TokenKind::Whitespace { at - 1 } else { at };
            let gap = Span::new(file, tokens[from].span.start, tokens[at].span.start);
            Edit::replace(gap, format!("{line_break}{moved}{indent}"))
        }
    });
    Some(edits)
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
        (TokenKind::DocComment, _) => match before_the_attributes(cst, text, first, last) {
            Some(edits) => Diagnostic::new(
                Stage::Syntax,
                Code::E0004,
                span,
                "this doc comment stands after an attribute; the doc comment goes before the attributes of the declaration (§2.1)",
            )
            .with_fix(Fix::new("move it before the attributes", edits)),
            None => Diagnostic::new(
                Stage::Syntax,
                Code::E0004,
                span,
                "this doc comment documents no declaration; `///` goes right before an item, a member, a field, a variant or an input of a flow (§2.1)",
            )
            .with_fix(Fix::new("make it a plain comment `//`", replaced("//"))),
        },
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

    use crate::cst::NodeKind;

    fn parse(src: &str) -> crate::Parsed {
        crate::parse(FileId(0), src)
    }

    /// The texts of the doc comments ([`super::doc_comments`]) of each node of `kind` of `p` (the
    /// tree of `src`), the nodes in the order of the walk of the tree.
    fn docs_of(p: &crate::Parsed, src: &str, kind: NodeKind) -> Vec<Vec<String>> {
        let nodes = crate::fmt::rewrites::all_nodes(&p.cst).into_iter().filter(|&n| p.cst.kind(n) == kind);
        let text = |t| {
            let s = p.cst.token(t).span;
            src[s.start as usize..s.end as usize].to_string()
        };
        nodes.map(|n| super::doc_comments(&p.cst, n).into_iter().map(text).collect()).collect()
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
        // Read on the CST, where the parser attached them (D-02: the AST has none).
        let root = super::doc_comments(&p.cst, p.cst.root());
        let module: Vec<&str> =
            root.iter().map(|&t| p.cst.token(t).span).map(|s| &src[s.start as usize..s.end as usize]).collect();
        assert_eq!(module, ["//! m", "//! n"]);
        let none = Vec::<String>::new;
        assert_eq!(docs_of(&p, src, NodeKind::Item), [vec!["/// s".to_string()], none(), none()]);
        assert_eq!(docs_of(&p, src, NodeKind::Field), [vec!["/// a".to_string()], none()]);
        assert_eq!(docs_of(&p, src, NodeKind::Variant), [vec!["/// A".to_string()]]);
        assert_eq!(docs_of(&p, src, NodeKind::Param), [vec!["/// x".to_string()]]);
        // With the declaration each documents, by its number in the item (the struct, `a`, `b`).
        let item = p.map.items[p.ast.root[0].index()];
        let numbers: Vec<usize> = super::documented(&p.cst, item).into_iter().map(|(d, _)| d).collect();
        assert_eq!(numbers, [0, 1]);
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
            // SPEC-GAP(S-433): an element of a variant (there is no tuple struct, S-39).
            ("enum E {\n  V(\n    /// x\n    F32\n  ),\n}\n", "/// x"),
            // A `use` takes none, so neither does a `///` after its attribute.
            ("@fp(relaxed)\n/// u\nuse std.math\n", "/// u"),
            // S-444: after an attribute on its line.
            ("@fp(relaxed) /// d\nfn f() {\n}\n", "/// d"),
        ] {
            assert_eq!(e0004(src), vec![plain(src, doc)], "{src}");
        }
        // A member of an `impl`, a `trait`, an `effect`, a `handler` (also
        // one of a `handle` expression) and an `extern` takes one (S-431).
        for src in [
            "impl S {\n  /// m\n  fn m() {}\n}\ntrait T {\n  /// n\n  fn n()\n}\n",
            "effect E {\n  /// op\n  fn op() -> I32\n}\n",
            "handler h: E {\n  /// op\n  fn op() -> I32 { 1 }\n}\n",
            "fn f() -> I32 {\n  handle { 1 } with E {\n    /// op\n    fn op() -> I32 { 1 }\n  }\n}\n",
            "extern \"C\" lib \"m\" {\n  /// sin\n  fn sin(x: F64) -> F64\n  /// raw\n  type Raw\n}\n",
        ] {
            assert!(e0004(src).is_empty(), "{src}");
        }
    }

    #[test]
    fn a_doc_comment_after_the_attributes_moves_before_them() {
        // S-432: one E0004 for the run, and one candidate that moves its
        // lines to the head of the line of the first attribute.
        for (src, doc, fixed) in [
            ("@repr(c)\n/// d\nstruct S {\n  a: I32,\n}\n", "/// d", "/// d\n@repr(c)\nstruct S {\n  a: I32,\n}\n"),
            (
                "/// a\n// c\n@fp(relaxed)\n/// b\n\n/// c\n@fp(relaxed)\nfn f() {\n}\n",
                "/// b\n\n/// c",
                "/// a\n// c\n/// b\n/// c\n@fp(relaxed)\n\n@fp(relaxed)\nfn f() {\n}\n",
            ),
            // The attribute follows code on its line.
            (
                "flow g(x: F32 at sample, @param(min: 0.0)\n  /// l\n  l: F32 at block,\n) -> F32 at sample {\n  x\n}\n",
                "/// l",
                "flow g(x: F32 at sample,\n  /// l\n  @param(min: 0.0)\n  l: F32 at block,\n) -> F32 at sample {\n  x\n}\n",
            ),
            // The texts are compared exactly (the cases of `tests/spec/` do
            // not compare the width of the white space): the lines go to the
            // head of the line of the attribute, before its indentation, as
            // they are written.
            (
                "impl S {\n    @fp(relaxed)\n    /// d\n    fn m() {}\n}\n",
                "/// d",
                "impl S {\n    /// d\n    @fp(relaxed)\n    fn m() {}\n}\n",
            ),
            (
                "impl S {\n    @fp(relaxed)\n/// d\n    fn m() {}\n}\n",
                "/// d",
                "impl S {\n/// d\n    @fp(relaxed)\n    fn m() {}\n}\n",
            ),
            // A file of CRLF keeps them, at the head of a line and where a
            // line break is added.
            ("@fp(relaxed)\r\n/// d\r\nfn f() {\r\n}\r\n", "/// d", "/// d\r\n@fp(relaxed)\r\nfn f() {\r\n}\r\n"),
            (
                "flow g(x: F32 at sample, @param(min: 0.0)\r\n  /// l\r\n  l: F32 at block,\r\n) -> F32 at sample {\r\n  x\r\n}\r\n",
                "/// l",
                "flow g(x: F32 at sample,\r\n  /// l\r\n  @param(min: 0.0)\r\n  l: F32 at block,\r\n) -> F32 at sample {\r\n  x\r\n}\r\n",
            ),
        ] {
            assert_eq!(e0004(src), vec![(doc.to_string(), Some(fixed.to_string()))], "{src}");
            assert!(e0004(fixed).is_empty(), "{fixed}");
        }
        // A parameter of a function takes none, and a `///` after the
        // `inout` of an input is past its attributes, in the declaration:
        // the candidate is `//`.
        for src in [
            "fn f(@fp(relaxed)\n  /// x\n  x: I32) {\n}\n",
            "flow g(\n  @param(min: 0.0)\n  inout\n  /// x\n  x: F32 at block,\n) -> F32 at block {\n  x\n}\n",
        ] {
            assert_eq!(e0004(src), vec![("/// x".to_string(), Some(src.replace("/// x", "// x")))], "{src}");
        }
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
        assert_eq!(docs_of(&p, src, NodeKind::Field), [vec![], vec!["/// d".to_string()]]);
        // fmt keeps it on its own line (W3-04/b 2), also after a comment that
        // the element before holds (W3-04/b 6).
        assert_eq!(crate::format(&p, src).as_deref(), Ok(src));
        let src = "struct S { f1: Buf[\n// k\nI32\n],\n/// d2\nf2: I32,\n}\n";
        let out = crate::format(&parse(src), src).unwrap();
        // The block form of `Buf[` stays, with `// k` on its line (§3.2, S-498, S-510, §3.4).
        assert_eq!(out, "struct S { f1: Buf[\n  // k\n  I32,\n],\n           /// d2\n           f2: I32 }\n");
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
        let g = p.ast.root.iter().find(|&&i| p.ast.item(i).failed.is_none()).unwrap();
        assert_eq!(super::doc_comments(&p.cst, p.map.items[g.index()]).len(), 1);
        assert_eq!(p.diagnostics[0].code, Code::E0002);
    }
}
