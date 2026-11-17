//! Tests of what a value stands for at its position (`crate::sources`,
//! §5.2, §5.3; S-1113, S-1114, R-482): the leaves of an argument, by text.

use onsa_diag::FileId;
use onsa_syntax::ast::{ExprId, ExprKind, ItemKind, StmtKind};

use crate::modes::Proj;
use crate::sources::{Cx, Leaf, Open, What, leaves, written};
use crate::tests::{check, def};

const HEAD: &str = "pub struct O { l: Buf[F32], n: F32 }\n\
    pub struct Stereo { l: F32, r: F32 }\n\
    pub flow pair(l: F32 at sample, r: F32 at sample) -> Stereo at sample { Stereo { l: l, r: r } }\n\
    pub enum Tag { A, B }\n\
    pub fn mk() -> [F32; 4] { [0.0; 4] }\n\
    pub fn bs(s: Span[F32]) {}\n\
    pub fn bf(x: F32) {}\n\
    pub fn bo(x: Span[F32]) {}\n\
    pub fn pl(xs: [Span[F32]; 2]) {}\n\
    pub fn gi(i: pair.In) {}\n\
    pub fn go(o: pair.Out) {}\n\
    pub fn bt(t: Tag) {}\n";

/// The first argument of the call that ends the body of `f`, the last item of
/// `src` after [`HEAD`], with what `f` of `ast` and `a` are.
fn with_arg<T>(body: &str, read: impl FnOnce(Cx<'_>, ExprId, &dyn Fn(ExprId) -> String) -> T) -> T {
    let src = format!(
        "{HEAD}pub fn f(c: Bool, d: Bool, a: Span[F32], b: Span[F32], o: O, p: O, v: [F32; 4]) {{\n  {body}\n}}\n"
    );
    let parsed = onsa_syntax::parse(FileId(0), &src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ast = &parsed.ast;
    let ItemKind::Fn(f) = &ast.item(*ast.root.last().unwrap()).kind else { panic!("not a function") };
    let ExprKind::Block(b) = &ast.expr(f.body.unwrap()).kind else { panic!("no block") };
    let call = match b.tail {
        Some(t) => t,
        None => match &ast.stmt(*b.stmts.last().unwrap()).kind {
            StmtKind::Expr(e) => *e,
            _ => panic!("no call"),
        },
    };
    let ExprKind::Call { args, .. } = &ast.expr(call).kind else { panic!("no call: {body}") };
    let a = check(&src);
    assert!(a.diagnostics.is_empty(), "{body}: {:?}", a.diagnostics);
    let id = def(&a, "f");
    let cx = Cx::after_types(ast, &a.names[&id], &a.bodies[&id], &a);
    let text = |e: ExprId| {
        let s = ast.expr(e).span;
        src[s.start as usize..s.end as usize].to_string()
    };
    read(cx, args[0].expr, &text)
}

/// Each leaf as `<what> <text> | arg <text> | tail <text> | at <text>`, then the steps over and `viewed`.
fn leaves_of(body: &str) -> Vec<String> {
    with_arg(body, |cx, e, text| {
        let show = |l: &Leaf| {
            let (what, x) = match l.what {
                What::Place(x) => ("place", x),
                What::Value(x) => ("value", x),
                What::Unit(x) => ("unit", x),
                What::Exits => ("exits", l.at),
            };
            let over: String = l
                .over
                .iter()
                .map(|p| match p {
                    Proj::Field(n) => format!(".{n}"),
                    Proj::Elem(i) => format!(".{i}"),
                    Proj::Index => "[_]".into(),
                    Proj::Payload => "payload".into(),
                })
                .collect();
            let mut s = format!("{what} {} | arg {} | tail {} | at {}", text(x), text(l.arg), text(l.tail), text(l.at));
            if !over.is_empty() {
                s += &format!(" | over {over}");
            }
            if l.viewed {
                s += " | viewed";
            }
            s
        };
        leaves(cx, e, Open::Arg).iter().map(show).collect()
    })
}

#[test]
fn a_place_through_parentheses_is_its_own_leaf() {
    assert_eq!(leaves_of("bs((a))"), ["place a | arg (a) | tail (a) | at (a)"]);
    assert_eq!(leaves_of("bs(mk())"), ["value mk() | arg mk() | tail mk() | at mk()"]);
}

/// S-1113: the tails of an `if`, a `match` and a block, nested and in parentheses, an arm that exits giving none.
#[test]
fn the_tails_of_the_argument() {
    let b = "bs(if c { a } else { (b) })";
    assert_eq!(
        leaves_of(b),
        [
            "place a | arg if c { a } else { (b) } | tail a | at a",
            "place b | arg if c { a } else { (b) } | tail b | at b"
        ]
    );
    let m = "bs(match c { true => { if d { a } else { b } }, false => panic(\"x\") })";
    let arg = "match c { true => { if d { a } else { b } }, false => panic(\"x\") }";
    assert_eq!(
        leaves_of(m),
        [format!("place a | arg {arg} | tail a | at a"), format!("place b | arg {arg} | tail b | at b")]
    );
}

/// R-482: a partial view adds no step, of a view neither.
#[test]
fn a_partial_view_is_its_base() {
    let one = "bs(a.slice(0, 2))";
    assert_eq!(leaves_of(one), ["place a | arg a.slice(0, 2) | tail a.slice(0, 2) | at a.slice(0, 2) | viewed"]);
    let two = "bs(a.slice(0, 2).slice(0, 1))";
    let t = "a.slice(0, 2).slice(0, 1)";
    assert_eq!(leaves_of(two), [format!("place a | arg {t} | tail {t} | at {t} | viewed")]);
    // G4: a path over a view is a place of its base.
    let e = "bf(a.slice(0, 2)[0])";
    let t = "a.slice(0, 2)[0]";
    assert_eq!(leaves_of(e), [format!("place a | arg {t} | tail {t} | at {t} | over [_] | viewed")]);
    let v = "bs(mk().slice(0, 1))";
    assert_eq!(
        leaves_of(v),
        ["value mk() | arg mk().slice(0, 1) | tail mk().slice(0, 1) | at mk().slice(0, 1) | viewed"]
    );
}

/// S-1114: the tails of the base of a path and of a view, the steps over them innermost first.
#[test]
fn the_tails_of_a_base() {
    let t = "(if c { o } else { p }).l";
    let want = [
        format!("place o | arg {t} | tail {t} | at o | over .l"),
        format!("place p | arg {t} | tail {t} | at p | over .l"),
    ];
    assert_eq!(leaves_of(&format!("bo({t})")), want);
    let t = "({ v }).slice(0, 2)";
    assert_eq!(leaves_of(&format!("bs({t})")), [format!("place v | arg {t} | tail {t} | at v | viewed")]);
    let t = "(if c { o } else { p }).l.slice(0, 1)";
    assert_eq!(leaves_of(&format!("bs({t})"))[0], format!("place o | arg {t} | tail {t} | at o | over .l | viewed"));
}

/// S-196, §11.6: the elements of a planar literal and the fields of a generated one are arguments of their own;
/// a path over a generated literal is of the field it picks (S-1114).
#[test]
fn the_elements_of_a_literal_opened() {
    assert_eq!(leaves_of("pl([a, b])"), ["place a | arg a | tail a | at a", "place b | arg b | tail b | at b"]);
    let g = "gi(pair.In { l: a, r: mk() })";
    assert_eq!(leaves_of(g), ["place a | arg a | tail a | at a", "value mk() | arg mk() | tail mk() | at mk()"]);
    let t = "pair.In { l: a, r: b }.r";
    assert_eq!(leaves_of(&format!("bs({t})")), [format!("place b | arg b | tail {t} | at b")]);
    let t = "(if c { pair.In { l: a, r: b } } else { pair.In { l: b, r: a } })";
    assert_eq!(leaves_of(&format!("gi({t})")).len(), 4);
}

/// A chain of names is a value; a tail that diverges gives no leaf.
#[test]
fn a_name_and_a_divergence() {
    assert_eq!(leaves_of("bt(Tag.A)"), ["value Tag.A | arg Tag.A | tail Tag.A | at Tag.A"]);
    let e = "bf(if c { o.n } else { panic(\"x\") })";
    assert_eq!(leaves_of(e), ["place o.n | arg if c { o.n } else { panic(\"x\") } | tail o.n | at o.n"]);
}

/// What `inout` writes: places at the argument alone, a view's base, each element of a literal opened.
#[test]
fn the_places_written() {
    let w = |body: &str| {
        with_arg(body, |cx, e, text| written(cx, e).map(|xs| xs.into_iter().map(text).collect::<Vec<_>>()))
    };
    assert_eq!(w("bs(a.slice(0, 2).slice(1, 2))"), Some(vec!["a".to_string()]));
    assert_eq!(w("pl([a, (b)])"), Some(vec!["a".to_string(), "b".to_string()]));
    assert_eq!(w("bs(if c { a } else { b })"), None);
    assert_eq!(w("bs((if c { a } else { b }).slice(0, 1))"), None);
    assert_eq!(w("bs(pair.In { l: a, r: b }.r)"), None);
    assert_eq!(w("bs(mk().slice(0, 1))"), None);
    // A literal is opened at the argument alone: under a tail it is no place (an array literal
    // there too, once the types stage records it, W7-12 U2c2: the same test).
    assert_eq!(w("go((pair.Out { l: a, r: b }))"), Some(vec!["a".to_string(), "b".to_string()]));
    assert_eq!(w("go({ pair.Out { l: a, r: b } })"), None);
    assert_eq!(w("go(if c { pair.Out { l: a, r: b } } else { pair.Out { l: b, r: a } })"), None);
}
