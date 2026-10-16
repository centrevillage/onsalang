//! The `init` of a built-in delay written as a literal equal to the default
//! value (spec §11.4, S-539 (c3a)): the documents write the omitted form, and
//! the gate (`tools/default_inits.py`, through `onsa_cases --default-inits`)
//! finds the written one. Every judgment is read from its one place (D-15):
//! the calls and their arguments from the parser's tree, the names of the
//! delays and the position of `init` from `onsa_sema::flow_names::Delay`,
//! the parentheses and a negative literal from [`Ast::without_parens`] and
//! [`Ast::negated_literal`], the value of a number from the lexer's
//! (`Lit::Int`) and [`onsa_syntax::float_value`], the line from
//! [`onsa_diag::SourceFile::line_col`].
//!
//! The tree has no item that has a syntax error (the parser drops it), so
//! the calls are also counted on the tokens, and the gate fails a source
//! whose tokens show more calls than its tree ([`Found::lexed`]).

use onsa_diag::SourceMap;
use onsa_sema::flow_names::Delay;
use onsa_syntax::FloatWidth;
use onsa_syntax::ast::{Ast, CallKind, ExprId, ExprKind, Lit};
use onsa_syntax::token::{Token, TokenKind};

/// A delay call whose `init` equals the default value.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Hit {
    /// The 1-based line of the call.
    pub line: u32,
    /// The name of the delay (`prev`).
    pub call: &'static str,
    /// The text of the `init` argument.
    pub init: String,
}

/// The delay calls of one source.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize)]
pub struct Found {
    /// The calls of a built-in delay in the tree, with `init` or without.
    pub calls: usize,
    /// The calls of a built-in delay on the tokens: the name of a delay, not
    /// after a `.` (a path, which the tree does not count either), then `~`
    /// and `(`, with any spaces and line breaks between (also the spaced
    /// `prev ~(` of §2.6). More than [`Found::calls`] means calls the tree
    /// does not hold (an item with a syntax error).
    pub lexed: usize,
    /// Whether the lexer or the parser reports a diagnostic of the syntax stage.
    pub syntax_errors: bool,
    pub hits: Vec<Hit>,
}

/// The delay calls of `text` and those whose `init` equals the default. Only
/// the items the tree holds are read: an item with a syntax error has no
/// tree, and its calls are only in [`Found::lexed`].
pub fn find(text: &str) -> Found {
    let mut map = SourceMap::default();
    let file = map.add("source", text);
    let parsed = onsa_syntax::parse(file, text);
    let ast = &parsed.ast;
    let mut found = Found {
        lexed: lexed_calls(text, &onsa_syntax::lexer::lex(file, text).tokens),
        syntax_errors: parsed.syntax_errors(),
        ..Found::default()
    };
    for e in &ast.exprs {
        let ExprKind::Call { callee, kind: CallKind::Flow, args } = &e.kind else { continue };
        let ExprKind::Path(p) = &ast.expr(*callee).kind else { continue };
        let [name] = p.segments.as_slice() else { continue };
        let Some(delay) = Delay::named(&name.name) else { continue };
        found.calls += 1;
        let Some(init) = args.get(delay.init_index()) else { continue };
        if args.len() == delay.init_index() + 1 && equals_default(ast, init.expr) {
            let line = map.file(file).line_col(e.span.start).line;
            let s = ast.expr(init.expr).span;
            let init = text[s.start as usize..s.end as usize].to_string();
            found.hits.push(Hit { line, call: delay.name(), init });
        }
    }
    found
}

/// The delay calls on the tokens ([`Found::lexed`]). A comment and a string
/// are one token each, so a call written in them is not counted.
fn lexed_calls(text: &str, tokens: &[Token]) -> usize {
    let code: Vec<&Token> = tokens.iter().filter(|t| t.kind.is_code()).collect();
    let is = |i: usize, k: TokenKind| code.get(i).is_some_and(|t| t.kind == k);
    (0..code.len())
        .filter(|&i| {
            let t = code[i];
            t.kind == TokenKind::Ident
                && Delay::named(&text[t.span.start as usize..t.span.end as usize]).is_some()
                && !(i > 0 && is(i - 1, TokenKind::Dot))
                && is(i + 1, TokenKind::Tilde)
                && is(i + 2, TokenKind::LParen)
        })
        .count()
}

/// Whether `e` is a literal whose value is the default of its type (§11.4:
/// 0, `+0.0`, `false`), through parentheses. A negative literal (`-0`) is
/// its value: the integer 0, but the float `-0.0`, which is not the default.
fn equals_default(ast: &Ast, e: ExprId) -> bool {
    let e = ast.without_parens(e);
    if let Some(lit) = ast.negated_literal(e) {
        return matches!(ast.expr(lit).kind, ExprKind::Lit(Lit::Int { value: 0, .. }));
    }
    match &ast.expr(e).kind {
        ExprKind::Lit(Lit::Int { value, .. }) => *value == 0,
        ExprKind::Lit(Lit::Float { text }) => {
            onsa_syntax::float_value(text, FloatWidth::F64).is_ok_and(|v| v == 0.0 && v.is_sign_positive())
        }
        ExprKind::Lit(Lit::Bool(b)) => !b,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flow(body: &str) -> String {
        format!(
            "pub flow f(x: F32 at sample, n: I32 at sample, b: Bool at sample, s: F32 at init) -> F32 at sample {{\n{body}\n}}\n"
        )
    }

    fn inits(body: &str) -> Vec<String> {
        find(&flow(body)).hits.into_iter().map(|h| h.init).collect()
    }

    #[test]
    fn the_spellings_of_the_default_are_found() {
        for init in [
            "0", "0x0", "0X0_0", "0b0", "0__", "0.0", "00.00", "0e3", "0.0E-5", "0_0e3", "-0", "-(0)", "(0.0)",
            "((-0x0))", "false", "(false)",
        ] {
            assert_eq!(inits(&format!("  prev~(x, {init})")), [init], "{init}");
        }
        assert_eq!(inits("  delay~(x, 4, 0.0) + vdelay~(x, x, 8, 0.0)"), ["0.0", "0.0"]);
        // a spelling of §2.4 that is E0020 has no value (`00`, `0_0`, `017`), and is not one
        for init in ["00", "0_0", "0o0"] {
            assert!(inits(&format!("  prev~(x, {init})")).is_empty(), "{init}");
        }
        let f = find(&flow("  let y = prev~(x,\n    0.0)\n  y"));
        assert_eq!(f.hits, [Hit { line: 2, call: "prev", init: "0.0".into() }]);
        assert_eq!((f.calls, f.lexed, f.syntax_errors), (1, 1, false));
    }

    #[test]
    fn other_inits_and_the_omitted_form_are_not() {
        for init in
            ["-0.0", "-(0.0)", "-0e3", "1", "1.0", "0.5", "1e-50", "0x1", "true", "s", "-s", "0 + 0", "!true", "x"]
        {
            assert!(inits(&format!("  prev~(x, {init})")).is_empty(), "{init}");
        }
        let f = find(&flow("  prev~(x) + delay~(x, 4) + vdelay~(x, x, 8) + delay~(x, 0)"));
        assert_eq!((f.calls, f.hits.len()), (4, 0));
        // not a delay: a call of another name, a plain call, a path of two names
        let f = find(&flow("  other~(x, 0.0) + prev(x, 0.0) + m.prev~(x, 0.0)"));
        assert_eq!((f.calls, f.hits.len()), (0, 0));
    }

    #[test]
    fn the_tokens_count_the_calls_the_tree_does_not_hold() {
        // the item with a syntax error has no tree: its call is only on the tokens; the item after it is read
        let f = find(&format!("{}fn g() -> I32 {{ 1 + }}\n", flow("  let a = prev~(x, 0.0)\n  let b = )\n  a")));
        assert_eq!((f.calls, f.lexed, f.syntax_errors, f.hits.len()), (0, 1, true, 0));
        let f = find(&format!("fn g() -> I32 {{ 1 + }}\n{}", flow("  prev~(x, 0.0)")));
        assert_eq!((f.calls, f.lexed, f.syntax_errors, f.hits.len()), (1, 1, true, 1));
        // the spaced `~` (§2.6), with a line break between the name and the `~` too
        assert_eq!(find(&flow("  prev ~(x, 0.0)")).lexed, 1);
        assert_eq!(find(&flow("  prev\n  ~ (x, 0.0)")).lexed, 1);
    }

    #[test]
    fn the_tokens_count_what_the_tree_counts() {
        // not counted: a path, a plain call, a name without `~(`, a comment, a string
        let f = find(&flow(
            "  m.prev~(x) + std.delay~(x, 4) + prev(x) + other~(x) + vdelay~(x, x, 8) + delay~(x, 4) // prev~(x, 0.0)",
        ));
        assert_eq!((f.calls, f.lexed), (2, 2));
        assert_eq!(find("/* prev~(x, 0.0) */\nfn f() -> Str { \"prev~(x)\" }\n").lexed, 0);
    }
}
