//! The grammar of a constant expression read two ways (§4.5): the syntax
//! stage's on the CST (`foreign::square::constant`, whether a list written
//! `name[A, B]` reads as type arguments) and `onsa_sema`'s on the AST
//! ([`Ast::const_form`], the nodes outside it are E0417). Each expression is
//! the length of `type A = [F32; <e>]`.

use onsa_diag::FileId;

use crate::ast::{Ast, ExprId, ItemKind, TypeKind};
use crate::constexpr::ConstForm;

/// Whether `e` and every node under it is of the grammar on the AST.
fn in_form(ast: &Ast, e: ExprId) -> bool {
    match ast.const_form(e) {
        ConstForm::Chain(_) | ConstForm::Lit(_) | ConstForm::Error => true,
        ConstForm::Paren(x) | ConstForm::Neg(x) => in_form(ast, x),
        ConstForm::Arith(l, r) => in_form(ast, l) && in_form(ast, r),
        ConstForm::Outside => false,
    }
}

/// The two readings of `e` as the length of an array type: (CST, AST).
fn readings(e: &str) -> (bool, bool) {
    let text = format!("type A = [F32; {e}]\n");
    let parsed = crate::parse(FileId(0), &text);
    let ast = &parsed.ast;
    let [item] = ast.root[..] else { panic!("{e}: {} items, {:?}", ast.root.len(), parsed.diagnostics) };
    let ItemKind::TypeAlias { ty, .. } = &ast.item(item).kind else { panic!("{e}: no alias") };
    let TypeKind::Array { len, .. } = &ast.ty(*ty).kind else { panic!("{e}: no array type") };
    let node = parsed.map.exprs[len.index()];
    (crate::foreign::constant(&parsed.cst, node, false), in_form(ast, *len))
}

/// The expressions both readings take or both refuse.
const SAME: &[(&str, bool)] = &[
    ("4", true),
    ("N", true),
    ("a.b.C", true),
    ("N + 1", true),
    ("N - 1", true),
    ("N * 2", true),
    ("N / 2", true),
    ("N % 2", true),
    ("-N", true),
    ("-1", true),
    ("-(N + 1)", true),
    ("(N)", true),
    ("((N) + 1) * 2", true),
    ("Rg::[F32, 4].CAP", true),
    ("Rg[F32, 4].CAP", true),
    ("Rg::[F32, 4].CAP + N", true),
    ("(K).x", false),
    ("f().x", false),
    ("f()", false),
    ("N.f()", false),
    ("t.0", false),
    ("(1, 2)", false),
    ("[1, 2]", false),
    ("[0; 2]", false),
    ("_", false),
    ("!N", false),
    ("(N < 1)", false),
    ("(N == 1)", false),
    ("(N && M)", false),
    ("N +% 1", false),
    ("N +| 1", false),
    ("N & 1", false),
    ("N << 1", false),
    ("N as U32", false),
    ("{ N }", false),
    ("if c { 1 } else { 2 }", false),
    ("match n { _ => 1 }", false),
    ("(fn() { 1 })", false),
    ("N + f()", false),
    ("-(f())", false),
    ("N * (N < 1)", false),
];

/// The expressions of the grammar on the AST that the syntax stage does
/// not take, each an error of `onsa_sema` other than the E0417 of a form
/// outside the grammar:
/// - a literal not an integer is of the grammar, of another type than
///   `U32` (§4.5: E0401, S-968);
/// - a chain that ends at its type arguments names a type, no constant
///   (E0308 of the kind of the name, §15.1).
const APART: &[&str] = &["1.5", "true", "\"s\"", "'c'", "N + 1.5", "Rg::[F32]", "Rg::[F32, 4]"];

#[test]
fn the_syntax_and_the_ast_read_the_grammar_of_a_constant_expression_the_same() {
    for &(e, want) in SAME {
        assert_eq!(readings(e), (want, want), "{e}: (CST, AST)");
    }
    for &e in APART {
        assert_eq!(readings(e), (false, true), "{e}: (CST, AST)");
    }
}
