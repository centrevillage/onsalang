//! Tests of the CST (R-86, W3-01): the round trip, the invariants, where the
//! trivia go, the positions, the height the parser counts.

use std::path::{Path as FsPath, PathBuf};

use onsa_diag::{FileId, Span};

use crate::ast::*;
use crate::cst::{Cst, Elem, NodeId, NodeKind};
use crate::token::TokenKind;

fn parse(src: &str) -> crate::Parsed {
    crate::parse(FileId(0), src)
}

fn root_dir() -> PathBuf {
    FsPath::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Every `.onsa` file under `tests/`, `std/` and `examples/`, sorted.
fn repo_files() -> Vec<(String, String)> {
    fn walk(dir: &FsPath, root: &FsPath, out: &mut Vec<(String, String)>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        let mut paths: Vec<PathBuf> = entries.map(|e| e.unwrap().path()).collect();
        paths.sort();
        for p in paths {
            if p.is_dir() {
                walk(&p, root, out);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                let rel = p.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
                if let Ok(text) = std::fs::read_to_string(&p) {
                    out.push((rel, text));
                }
            }
        }
    }
    let root = root_dir();
    let mut out = Vec::new();
    for d in ["tests", "std", "examples"] {
        walk(&root.join(d), &root, &mut out);
    }
    out
}

/// The files on which the lexer panics today (R-01, W3-04): a multibyte
/// character right after `{` in an interpolation.
const LEXER_PANICS: &[&str] =
    &["tests/review-phase1/parent/r1.onsa", "tests/review-phase1/syntax/interp_utf8.onsa", "tests/fuzz/b60c431d.onsa"];

fn try_parse(src: &str) -> Option<crate::Parsed> {
    std::panic::catch_unwind(|| parse(src)).ok()
}

/// The text of the tree is the source, and the tree is valid.
fn assert_round_trip(src: &str) {
    let p = parse(src);
    assert_eq!(p.cst.text(src), src, "the CST does not give the source back");
    p.cst.validate(src).unwrap();
}

// ---------------------------------------------------------------- the round trip

#[test]
fn round_trip_of_every_repository_file() {
    let files = repo_files();
    assert!(files.len() > 400, "only {} files found", files.len());
    let mut ran = 0;
    for (name, text) in &files {
        match try_parse(text) {
            Some(p) => {
                assert_eq!(p.cst.text(text), *text, "{name}: the CST does not give the source back");
                p.cst.validate(text).unwrap_or_else(|e| panic!("{name}: {e:?}"));
                check_spans(&p, name);
                ran += 1;
            }
            None => assert!(LEXER_PANICS.contains(&name.as_str()), "{name}: the parser panics"),
        }
    }
    assert!(ran > 400);
}

#[test]
fn round_trip_of_trivia_at_the_edges_of_a_file() {
    // The inputs of W3-01/t that a case file cannot start with.
    for src in [
        "",
        "\nconst LIMIT: U32 = 16\n",
        "\n\n\n// comment\nconst LIMIT: U32 = 16\n",
        "   const LIMIT: U32 = 16\n",
        "\tconst LIMIT: U32 = 16\n",
        " \n\t\n  \t \nconst LIMIT: U32 = 16\n",
        "\r\n\r\nconst LIMIT: U32 = 16\r\n",
        "  // c\nconst LIMIT: U32 = 16\n",
        "const A: U32 = 1\r\nfn f() -> U32 {\r\n  A\r\n}\r\n",
        "\n",
        " \t  \n",
        "\r\n",
        " ",
        "\t",
        "// only a comment",
        "/// only a doc comment",
        "\rconst LIMIT: U32 = 16\n",
        "\r",
        "const A: U32 = 1",
        "fn f() {\n  let a = 1 +\n\n    // c\n    2\n}\n",
        "fn f() {   }   \n   \n",
        "/* block */ const A: U32 = 1 /* x */\n",
    ] {
        assert_round_trip(src);
    }
}

#[test]
fn round_trip_of_sources_with_errors() {
    for src in [
        "fn f(",
        "fn f() {\n  let = 1\n  let x = 2\n}\nfn g() {}\n",
        "fn f() {}\n)\n",
        "fn f() {} junk here\nfn g() {}\n",
        "struct A { x: }\nenum B { C { x: U32 } }\n",
        "$ fn f() {}\n",
        "fn f() {\n  let s = \"abc\n}\n",
        "impl A for B[T] {}\n",
        "fn f() { par i in 3 { } }\n",
        "fn f() { g(&mut x, &y) }\n",
        "fn f() {\n  x.\n}\n",
        "@a\n@b(\nfn f() {}\n",
        "/// d\n;\nfn f() {}\n",
        "fn f() {\n  if a { 1 }\n  else { 2 }\n}\n",
        "use a::b.{c, d}\nuse a.*\n",
        "trait T {\n  fn f()\n  fn g() {\n}\n",
        "fn f() { let x = 99999999999999999999 }\n",
        "fn f() { t.99999999999 }\n",
        "fn f() {\n  match x { Point { .. } => 1 }\n}\n",
        "}}}\n{{{\n",
    ] {
        assert_round_trip(src);
    }
}

// ---------------------------------------------------------------- the shape of the tree

fn kinds_of(cst: &Cst, n: NodeId) -> Vec<String> {
    cst.children(n)
        .iter()
        .map(|e| match *e {
            Elem::Node(c) => format!("{}{}", cst.kind(c).name(), if cst.is_complete(c) { "" } else { "!" }),
            Elem::Token(t) => format!("{:?}", cst.token(t).kind),
        })
        .collect()
}

fn find(cst: &Cst, kind: NodeKind) -> Vec<NodeId> {
    let mut out = Vec::new();
    let mut stack = vec![cst.root()];
    while let Some(n) = stack.pop() {
        if cst.kind(n) == kind {
            out.push(n);
        }
        stack.extend(cst.child_nodes(n));
    }
    out.sort();
    out
}

#[test]
fn trivia_between_items_belong_to_the_file_and_doc_comments_to_the_item() {
    let src = "// c\n\n/// a\n\n// b\n/// d\nfn f() {}\n\nconst A: U32 = 1\n";
    let p = parse(src);
    let root = p.cst.root();
    assert_eq!(
        kinds_of(&p.cst, root),
        ["Comment", "Newline", "Newline", "Item", "Newline", "Newline", "Item", "Newline", "Eof"]
    );
    let item = find(&p.cst, NodeKind::Item)[0];
    assert_eq!(kinds_of(&p.cst, item), ["Docs", "Newline", "Fn"]);
    let docs = find(&p.cst, NodeKind::Docs)[0];
    assert_eq!(kinds_of(&p.cst, docs), ["DocComment", "Newline", "Newline", "Comment", "Newline", "DocComment"]);
    // The AST span of the item starts at `fn`; its doc lines are the two `///`.
    let ast_item = p.ast.item(p.ast.root[0]);
    assert_eq!(&src[ast_item.span.start as usize..ast_item.span.end as usize], "fn f() {}");
    assert_eq!(ast_item.doc.len(), 2);
}

#[test]
fn statement_newlines_are_children_of_the_block_and_continuations_are_inside() {
    let src = "fn f() {\n  let a = x +\n    y\n  a\n}\n";
    let p = parse(src);
    let block = find(&p.cst, NodeKind::Block)[0];
    assert_eq!(
        kinds_of(&p.cst, block),
        ["LBrace", "Newline", "Whitespace", "LetStmt", "Newline", "Whitespace", "ExprStmt", "Newline", "RBrace"]
    );
    let bin = find(&p.cst, NodeKind::BinaryExpr)[0];
    assert_eq!(kinds_of(&p.cst, bin), ["PathExpr", "Whitespace", "Plus", "Newline", "Whitespace", "PathExpr"]);
}

#[test]
fn trailing_trivia_leave_the_node() {
    let src = "fn f() {\n  g(1, // one\n    2)\n}\n";
    let p = parse(src);
    let args = find(&p.cst, NodeKind::ArgList)[0];
    assert_eq!(
        kinds_of(&p.cst, args),
        ["LParen", "Arg", "Comma", "Whitespace", "Comment", "Newline", "Whitespace", "Arg", "RParen"]
    );
}

#[test]
fn an_error_leaves_incomplete_nodes_and_an_error_node() {
    let src = "fn a() {\n  let = 1\n  x\n}\nfn b() {}\n";
    let p = parse(src);
    let root = p.cst.root();
    assert_eq!(kinds_of(&p.cst, root), ["Item!", "Newline", "Item", "Newline", "Eof"]);
    // The nodes the parser was in are closed as incomplete; the tokens from
    // the error to the next item are the `Error` node, the last child of the item.
    let item = p.cst.child_nodes(root).next().unwrap();
    assert_eq!(kinds_of(&p.cst, item), ["Fn!", "Whitespace", "Error"]);
    let f = p.cst.child_nodes(item).next().unwrap();
    assert_eq!(kinds_of(&p.cst, f), ["KwFn", "Whitespace", "Name", "ParamList", "Whitespace", "Block!"]);
    let block = find(&p.cst, NodeKind::Block)[0];
    assert_eq!(kinds_of(&p.cst, block), ["LBrace", "Newline", "Whitespace", "LetStmt!"]);
    let err = find(&p.cst, NodeKind::Error)[0];
    let s = p.cst.span(err);
    assert_eq!(&src[s.start as usize..s.end as usize], "= 1\n  x\n}");
    // Only `b` is in the AST (W3-01 D10: no AST for an item that failed).
    assert_eq!(p.ast.root.len(), 1);
    assert_eq!(p.ast.items.len(), 1);
    assert_eq!(p.ast.exprs.len(), 1);
}

#[test]
fn junk_after_an_item_is_an_error_node_of_the_file() {
    let src = "fn f() {} junk\nfn g() {}\n";
    let p = parse(src);
    assert_eq!(kinds_of(&p.cst, p.cst.root()), ["Item", "Whitespace", "Error", "Newline", "Item", "Newline", "Eof"]);
    assert_eq!(p.ast.root.len(), 2);
}

#[test]
fn the_tree_view_shows_every_token() {
    let src = "fn f() {}\n";
    let tree = parse(src).cst.tree(src);
    assert_eq!(
        tree,
        "SourceFile@0..10\n  Item@0..9\n    Fn@0..9\n      KwFn@0..2 \"fn\"\n      Whitespace@2..3 \" \"\n      \
         Name@3..4\n        Ident@3..4 \"f\"\n      ParamList@4..6\n        LParen@4..5 \"(\"\n        RParen@5..6 \")\"\n      \
         Whitespace@6..7 \" \"\n      Block@7..9\n        LBrace@7..8 \"{\"\n        RBrace@8..9 \"}\"\n  \
         Newline@9..10 \"\\n\"\n  Eof@10..10 \"\"\n"
    );
}

#[test]
fn validate_finds_a_broken_tree() {
    let src = "fn f() {}\n";
    let p = parse(src);
    // A source longer than the tokens.
    assert!(p.cst.validate("fn f() {}\nx").is_err());
    assert!(p.cst.validate(src).is_ok());
}

// ---------------------------------------------------------------- positions

/// Every AST node has the span of the CST node it was made from, except the
/// three kept from the parser before the CST (lower.rs, `SPAN-QUIRK`).
fn check_spans(p: &crate::Parsed, name: &str) {
    let cst = &p.cst;
    let (ast, map) = (&p.ast, &p.map);
    assert_eq!(map.items.len(), ast.items.len());
    assert_eq!(map.exprs.len(), ast.exprs.len());
    assert_eq!(map.stmts.len(), ast.stmts.len());
    assert_eq!(map.types.len(), ast.types.len());
    assert_eq!(map.pats.len(), ast.pats.len());
    for (i, item) in ast.items.iter().enumerate() {
        assert_eq!(cst.span(map.items[i]), item.span, "{name}: item {i}");
    }
    for (i, e) in ast.exprs.iter().enumerate() {
        let n = map.exprs[i];
        let quirk = matches!(cst.kind(n), NodeKind::LoopStmt | NodeKind::ConstArg);
        if quirk {
            let s = cst.span(n);
            assert!(s.start <= e.span.start && e.span.end <= s.end, "{name}: expr {i}");
        } else {
            assert_eq!(cst.span(n), e.span, "{name}: expr {i} ({:?})", cst.kind(n));
        }
    }
    for (i, s) in ast.stmts.iter().enumerate() {
        assert_eq!(cst.span(map.stmts[i]), s.span, "{name}: stmt {i}");
    }
    for (i, t) in ast.types.iter().enumerate() {
        assert_eq!(cst.span(map.types[i]), t.span, "{name}: type {i}");
    }
    for (i, q) in ast.pats.iter().enumerate() {
        assert_eq!(cst.span(map.pats[i]), q.span, "{name}: pat {i}");
    }
}

#[test]
fn spans_come_from_the_cst() {
    for src in [
        "fn f() {\n  loop { }\n}\n",
        "fn f(r: Ring[F32, -4]) {}\n",
        "#[derive(PartialEq)]\nstruct A { }\n",
        "fn f() { g(&mut x) + &y }\n",
    ] {
        check_spans(&parse(src), src);
    }
    // The quirks themselves.
    let src = "#[derive(PartialEq)]\nstruct A { }\n";
    let p = parse(src);
    let a = &p.ast.item(p.ast.root[0]).attrs[0];
    assert_eq!(&src[a.span.start as usize..a.span.end as usize], "#[derive(PartialEq)");
}

#[test]
fn covering_node_and_tokens_in() {
    let src = "fn f(x: F32) -> F32 {\n  g(x, 1)\n}\n";
    let p = parse(src);
    let cst = &p.cst;
    // The parameter `x: F32` (an AST `Param`, not an arena node).
    let ItemKind::Fn(f) = &p.ast.item(p.ast.root[0]).kind else { unreachable!() };
    let param_span = f.params[0].span;
    assert_eq!(cst.kind(cst.covering_node(param_span)), NodeKind::Param);
    // A name inside the parameter: the innermost node holding it is its
    // `Name`; outward come the `Param`, the `ParamList`, the `Fn`, ...
    let x = Span::new(FileId(0), 5, 6);
    let kinds: Vec<NodeKind> = cst.covering_nodes(x).map(|n| cst.kind(n)).collect();
    use NodeKind as K;
    assert_eq!(kinds, [K::Name, K::Param, K::ParamList, K::Fn, K::Item, K::SourceFile]);
    assert_eq!(cst.kind(cst.covering_node(x)), NodeKind::Name);
    assert_eq!(cst.covering_node_of(x, NodeKind::Param).map(|n| cst.kind(n)), Some(NodeKind::Param));
    // The argument `1` and the whole call.
    let one = Span::new(FileId(0), src.find("1)").unwrap() as u32, src.find("1)").unwrap() as u32 + 1);
    assert_eq!(cst.kind(cst.covering_node(one)), NodeKind::Literal);
    let call_at = src.find("g(").unwrap() as u32;
    let call = Span::new(FileId(0), call_at, call_at + 7);
    assert_eq!(cst.kind(cst.covering_node(call)), NodeKind::CallExpr);
    // Tokens: `g(x, 1)` holds 7 tokens with the space.
    let r = cst.tokens_in(call);
    let kinds: Vec<TokenKind> = r.map(|i| cst.tokens()[i].kind).collect();
    use TokenKind::*;
    assert_eq!(kinds, [Ident, LParen, Ident, Comma, Whitespace, Int, RParen]);
    // An empty span between two tokens holds none.
    let empty = Span::new(FileId(0), call_at + 2, call_at + 2);
    assert!(cst.tokens_in(empty).is_empty());
    // The AST map points at the node of the call expression.
    let call_expr = p.ast.exprs.iter().position(|e| matches!(e.kind, ExprKind::Call { .. })).unwrap();
    assert_eq!(cst.kind(p.map.exprs[call_expr]), NodeKind::CallExpr);
}

/// The doc comments of an item that follows a syntax error (W3-01/b M-1:
/// the parser takes them for the next item; they stay in its `Docs`).
const DOCS_AFTER_ERRORS: &[(&str, &[&[&str]])] = &[
    ("fn f(\n/// doc for g\nfn g() -> I32 { 1 }\n", &[&["/// doc for g"]]),
    ("fn pre(\n/// d\nfn f() {}\nfn post", &[&["/// d"]]),
    ("fn pre() {}\n/// d\nfn f(\n/// I32) {}\nfn post() {}\n", &[&[], &["/// I32) {}"]]),
    (
        "fn broken(\n/// doc for next\nfn ok() {}\n\nfn g() {\n  let x = (1,\n  l}t x = (1,\n/// stray doc\nfn h() {}\n",
        &[&["/// doc for next"], &["/// stray doc"]],
    ),
    ("struct A { x:\n}\n/// a\n\n// c\n/// b\nconst X: U32 = 1\n", &[&["/// a", "/// b"]]),
    ("impl A {\n  fn f(\n}\n/// d\n@x\nfn g() {}\n", &[&["/// d"]]),
];

#[test]
fn doc_comments_after_a_failed_item_belong_to_the_next_item() {
    for (src, want) in DOCS_AFTER_ERRORS {
        let p = parse(src);
        let got: Vec<Vec<&str>> = p
            .ast
            .root
            .iter()
            .map(|&i| p.ast.item(i).doc.iter().map(|d| &src[d.start as usize..d.end as usize]).collect())
            .collect();
        let want: Vec<Vec<&str>> = want.iter().map(|d| d.to_vec()).collect();
        assert_eq!(got, want, "{src:?}");
        // Every doc comment the AST holds is in the `Docs` node of a complete item.
        for docs in find(&p.cst, NodeKind::Docs) {
            let item = p.cst.parent(docs).unwrap();
            assert_eq!(p.cst.kind(item), NodeKind::Item);
        }
        for &i in &p.ast.root {
            for d in &p.ast.item(i).doc {
                let t = p.cst.token_at(d.start);
                assert_eq!(p.cst.kind(p.cst.token_parent(t)), NodeKind::Docs, "{src:?}");
            }
        }
        assert_round_trip(src);
    }
}

/// The height the parser counts ([`crate::parser`], one function) and the
/// height of the tree, both by `Cst::height` and by the indentation of
/// `dump --cst --tree`.
fn heights(src: &str) -> (u32, u32, u32) {
    let lexed = crate::lex(FileId(0), src);
    let counted = crate::parser::Parser::new(FileId(0), src, lexed.tokens, lexed.diagnostics).parse_file().height;
    let p = parse(src);
    let tree = p.cst.height(p.cst.root());
    let indent = p
        .cst
        .tree(src)
        .lines()
        .filter(|l| !l.contains('"'))
        .map(|l| (l.len() - l.trim_start().len()) as u32 / 2 + 1)
        .max()
        .unwrap();
    (counted, tree, indent)
}

#[test]
fn the_parser_counts_the_height_of_the_tree() {
    // A thread with a large stack: the parser and the lowering recurse on
    // nested parentheses and `else if` (the limit of S-183 is W3-14's).
    let run = || {
        let n = 300;
        let body = |e: &str| format!("fn f() {{\n  {e}\n}}\n");
        let cases = [
            body(&format!("{}1{}", "(".repeat(n), ")".repeat(n))),
            body(&format!("a{}", ".b".repeat(n))),
            body(&format!("f{}", "()".repeat(n))),
            body(&format!("a{}", "[0]".repeat(n))),
            body(&format!("x{}", " as A".repeat(n))),
            body(&format!("1{}", " + 1".repeat(n))),
            body(&format!("if a {{ 1 }}{} else {{ 2 }}", " else if a { 1 }".repeat(n - 1))),
            body(&format!("{}x", "-".repeat(n))),
            "fn f(\n".to_string(),
            "fn f() { a.b.c(d[0] as I32 + 1) }\nstruct S { x: Ring[F32, -4] }\n".to_string(),
        ];
        for (k, src) in cases.iter().enumerate() {
            let (counted, tree, indent) = heights(src);
            assert_eq!((counted, counted), (tree, indent), "case {k}");
            if k < 5 || k == 6 || k == 7 {
                assert!(counted >= n as u32, "case {k}: height {counted}");
            }
        }
    };
    std::thread::Builder::new().stack_size(512 << 20).spawn(run).unwrap().join().unwrap();
}

#[test]
fn names_are_nodes_and_foreign_forms_have_their_own_shape() {
    let src = "impl A {\n  fn f(mut self, _: I32) { }\n}\nproc g(x: Sig[F32]) -> Sig[F32] { x }\n\
               fn h() {\n  let mut v = 1\n}\n#[derive(Eq)]\nstruct S { }\n";
    let p = parse(src);
    let param = find(&p.cst, NodeKind::Param)[0];
    assert_eq!(kinds_of(&p.cst, param), ["Ident", "Whitespace", "Name"]);
    assert_eq!(find(&p.cst, NodeKind::HashAttr).len(), 1);
    let ItemKind::Impl(i) = &p.ast.item(p.ast.root[0]).kind else { unreachable!() };
    let ItemKind::Fn(f) = &p.ast.item(i.items[0]).kind else { unreachable!() };
    assert!(matches!(f.params[0].name, ParamName::SelfParam(_)) && f.params[0].mode == Mode::Inout);
    assert!(matches!(f.params[1].name, ParamName::Wild(_)) && f.params[1].mode == Mode::Borrow);
    let ItemKind::Flow(g) = &p.ast.item(p.ast.root[1]).kind else { unreachable!() };
    assert_eq!(g.name.name, "g");
    let ItemKind::Fn(h) = &p.ast.item(p.ast.root[2]).kind else { unreachable!() };
    let ExprKind::Block(b) = &p.ast.expr(h.body.unwrap()).kind else { unreachable!() };
    let StmtKind::Var { name, .. } = &p.ast.stmt(b.stmts[0]).kind else { unreachable!() };
    assert_eq!(name.name, "v");
}

#[test]
fn tokens_in_the_span_of_the_root_reach_eof() {
    let src = "\n// c\nfn f() {}\n";
    let p = parse(src);
    let r = p.cst.tokens_in(p.cst.span(p.cst.root()));
    assert_eq!(p.cst.tokens()[r.start].kind, TokenKind::KwFn);
    assert_eq!(r.end, p.cst.tokens().len());
    assert_eq!(p.cst.tokens()[r.end - 1].kind, TokenKind::Eof);
}

#[test]
fn a_broken_tree_names_where() {
    let p = parse("fn f() {}\n");
    let e = p.cst.validate("fn f() {}\nxyz").unwrap_err();
    assert_eq!((e.span.start, e.span.end), (10, 13), "{e:?}");
}
