use onsa_diag::FileId;
use onsa_syntax::ast::StmtKind;

use super::each_bind;

/// The names [`each_bind`] gives of the pattern of the one `let` of `src`.
fn names(src: &str, into_or: bool) -> Vec<String> {
    let parsed = onsa_syntax::parse(FileId(0), src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ast = &parsed.ast;
    let pat = ast.stmts.iter().find_map(|s| match s.kind {
        StmtKind::Let { pat, .. } => Some(pat),
        _ => None,
    });
    let mut out = Vec::new();
    each_bind(ast, pat.expect("a `let`"), into_or, &mut |_, name| out.push(name.name.clone()));
    out
}

#[test]
fn each_bind_gives_the_leaves_in_the_order_written_and_the_branches_of_an_or_when_asked() {
    let src = "fn f(x: I32) -> I32 {\n  let (a, P { l: b, r: _ }, S(c, 1), (d | (e, Q.R)), (g | h)) = x\n  0\n}\n";
    assert_eq!(names(src, true), ["a", "b", "c", "d", "e", "g", "h"]);
    assert_eq!(names(src, false), ["a", "b", "c"]);
    assert_eq!(names("fn f(x: I32) -> I32 {\n  let (_, -1) = x\n  0\n}\n", true), Vec::<String>::new());
}
