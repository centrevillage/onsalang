//! The drop of the value of `e` of a `[e; N]` where the length is 0 or may be 0, against a model of the grid
//! (spec §2.4, §12.2, §8.1, §10 rule 1, §5.4; S-1045 (1), R-461; W6-04 U2/t).
//!
//! §2.4: "`[e; N]` ... `e` は値を置く位置で（§5.2）、長さが 0 でありうる（長さが 0 か、総称の定数のパラメータ）とき、置いた値は
//! どの要素にもならず、その場で破棄される、§12.2". §12.2: the drop of a Shared value, or of a value that holds one, needs
//! `Alloc`; "長さが 0 でありうる `[e; N]`（§2.4）の `e` の値の破棄。総称の長さは、1 以上でしか呼ばれなくても数える" needs it; the
//! drop of a static value and of a literal that needs no drop (§5.4) needs none. A function with no `uses {Alloc}` that needs it gets
//! an E0601 (§8.1), and so does an `rt fn` (§10 rule 1, S-77); the use is one for each range (S-1053), so a function gets one.
//!
//! The dup_release_model test cannot take this form: its twin program writes the same bodies with a `Buf`, which is not Dup, so
//! `[move s; 2]` is an E0416 there, and the hand-off of its model always moves or copies one value. The grid here is of its own.
//! It writes a function for each element, length, wrapper and kind of function, and the model says: a function needs `Alloc` when
//! the element needs a drop (a `Str`, an `Option[Str]`, a tuple that holds a `Str`: an owned parameter, a borrowed one that is
//! copied, a value that a call makes, a `let` of one) and some array of the function has a length that is 0 or may be 0 (the
//! literal 0, a constant of the value 0, the constant parameter `N`), and has none (`uses {Alloc}` is a function of its own kind).
//! The elements that need none are a `Copy` value, a static string, a literal of static values and Copy values and the binding of
//! one (§5.4). The wrappers are the array alone, an array of the arrays (`[[e; 2]; L]`, with the length of the outer one or
//! of the inner one `[[e; L]; 2]`, where the drop of the whole inner array counts for the outer length) and the array as the element of a tuple.
//! The bodies are kept in memory (`check_input_out`, no file written: `rules/common.md` 3.7). A function that gets a diagnostic other than
//! E0601 is a fault of the generator.
//!
//! A reading that counts the drop only where the length is written 0 gives a function with a generic length that the model says needs
//! `Alloc`, and a reading that counts nothing gives every function that needs it; so the failures name the length and the element.

use onsa_driver::PackageInput;

use crate::test_support::doc_of;
use crate::test_support::sweep::check_input_out;

const HEAD: &str = "pub rt fn mk(n: U32) -> Str { \"x\" }\n\nconst Z: U32 = 0\n\nconst W: U32 = 3\n";

/// An element: the parameters, the statements before the array, the text of `e`, its type, and whether its drop needs `Alloc`.
struct Elem {
    name: &'static str,
    params: &'static str,
    pre: &'static str,
    expr: &'static str,
    ty: &'static str,
    needs: bool,
}

const ELEMS: &[Elem] = &[
    Elem { name: "owned", params: "move s: Str", pre: "", expr: "s", ty: "Str", needs: true },
    Elem { name: "borrowed", params: "s: Str", pre: "", expr: "s", ty: "Str", needs: true },
    Elem { name: "made", params: "n: U32", pre: "", expr: "mk(n)", ty: "Str", needs: true },
    Elem { name: "letmade", params: "n: U32", pre: "let t = mk(n)", expr: "t", ty: "Str", needs: true },
    Elem { name: "option", params: "move o: Option[Str]", pre: "", expr: "o", ty: "Option[Str]", needs: true },
    Elem { name: "pair", params: "s: Str", pre: "", expr: "(\"g\", s)", ty: "(Str, Str)", needs: true },
    Elem { name: "copy", params: "v: F32", pre: "", expr: "v", ty: "F32", needs: false },
    Elem { name: "static", params: "n: U32", pre: "", expr: "\"a\"", ty: "Str", needs: false },
    Elem { name: "nodrop", params: "v: F32", pre: "", expr: "(\"g\", v)", ty: "(Str, F32)", needs: false },
    Elem { name: "letnodrop", params: "v: F32", pre: "let p = (\"g\", v)", expr: "p", ty: "(Str, F32)", needs: false },
];

/// A length: the text and whether it is 0 or may be 0 (a constant parameter).
const LENGTHS: &[(&str, bool)] = &[("0", true), ("1", false), ("2", false), ("Z", true), ("W", false), ("N", true)];

#[derive(Clone, Copy)]
enum Wrap {
    /// `[e; L]`
    Plain,
    /// `[[e; 2]; L]`: the length is of the outer array.
    Outer,
    /// `[[e; L]; 2]`: the length is of the inner array.
    Inner,
    /// `([e; L], 1)`: the array is the element of a tuple.
    Tuple,
}

const WRAPS: &[(Wrap, &str)] =
    &[(Wrap::Plain, "plain"), (Wrap::Outer, "outer"), (Wrap::Inner, "inner"), (Wrap::Tuple, "tuple")];

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Plain,
    Rt,
    Alloc,
}

struct Case {
    name: String,
    line: usize,
    drops: bool,
    text: String,
}

fn build(wrap: Wrap, wname: &str) -> (String, Vec<Case>) {
    let mut text = HEAD.to_string();
    let mut cases = Vec::new();
    for e in ELEMS {
        for (len, may0) in LENGTHS {
            for kind in [Kind::Plain, Kind::Rt, Kind::Alloc] {
                // The constant parameter is of the function; the length of a length that the wrapper does not write is 2.
                let generic = *len == "N";
                let (body, ret) = match wrap {
                    Wrap::Plain => (format!("[{}; {len}]", e.expr), format!("[{}; {len}]", e.ty)),
                    Wrap::Outer => (format!("[[{}; 2]; {len}]", e.expr), format!("[[{}; 2]; {len}]", e.ty)),
                    Wrap::Inner => (format!("[[{}; {len}]; 2]", e.expr), format!("[[{}; {len}]; 2]", e.ty)),
                    Wrap::Tuple => (format!("([{}; {len}], 1)", e.expr), format!("([{}; {len}], U32)", e.ty)),
                };
                let name = format!(
                    "{wname}_{}_{}_{}",
                    e.name,
                    len.to_lowercase(),
                    match kind {
                        Kind::Plain => "fn",
                        Kind::Rt => "rt",
                        Kind::Alloc => "alloc",
                    }
                );
                let head = format!(
                    "pub {}fn {name}{}({}) -> {ret}{}",
                    if kind == Kind::Rt { "rt " } else { "" },
                    if generic { "[const N: U32]" } else { "" },
                    e.params,
                    if kind == Kind::Alloc { " uses {Alloc}" } else { "" }
                );
                text += "\n";
                let line = text.lines().count() + 1;
                let body_text = if e.pre.is_empty() {
                    format!("{head} {{ {body} }}\n")
                } else {
                    format!("{head} {{\n  {}\n  {body}\n}}\n", e.pre)
                };
                text += &body_text;
                let drops = e.needs && *may0 && kind != Kind::Alloc;
                cases.push(Case { name, line, drops, text: body_text });
            }
        }
    }
    (text, cases)
}

#[test]
#[ignore = "W6-04 U2: a [e; N] of a value that needs a drop is not counted where the length is 0 or may be 0 (S-1045 (1))"]
fn a_repeat_of_a_value_that_needs_a_drop_is_dropped_where_the_length_is_or_may_be_0() {
    onsa_diag::stack::run(|| {
        let (mut functions, mut drops, mut clean) = (0, 0, 0);
        let mut failed: Vec<String> = Vec::new();
        let mut strays: Vec<String> = Vec::new();
        for (wrap, wname) in WRAPS {
            let (text, cases) = build(*wrap, wname);
            let out = check_input_out(&PackageInput::single_file("m.onsa", text));
            assert!(out.code == 0 || out.code == 1, "{wname}: exit {}: {}", out.code, out.stderr);
            let doc = doc_of(&out);
            let mut got: Vec<Vec<String>> = vec![Vec::new(); cases.len()];
            for d in doc["diagnostics"].as_array().expect("diagnostics") {
                let code = d["code"].as_str().expect("a code").to_string();
                let line = d["span"]["line"].as_u64().expect("a line") as usize;
                let message = d["message"].as_str().expect("a message").to_string();
                let idx = cases
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| c.line <= line)
                    .max_by_key(|(_, c)| c.line)
                    .map(|(i, _)| i);
                match idx {
                    Some(i) if code == "E0601" => got[i].push(code),
                    Some(i) => strays.push(format!("{wname}, `{}`: {code} {message}", cases[i].name)),
                    None => strays.push(format!("{wname}: {code} at line {line}: {message}")),
                }
            }
            for (c, g) in cases.iter().zip(&got) {
                functions += 1;
                if c.drops {
                    drops += 1;
                } else {
                    clean += 1;
                }
                let ok = if c.drops { g.len() == 1 } else { g.is_empty() };
                if !ok {
                    failed.push(format!(
                        "`{}`: the model says {}, the check says {g:?}\n{}",
                        c.name,
                        if c.drops { "an E0601 (a drop of the value of `e` needs `Alloc`)" } else { "no error" },
                        c.text
                    ));
                }
            }
        }
        eprintln!(
            "repeat_zero_model: {functions} functions; the model says drop in {drops}, none in {clean}; {} differ",
            failed.len()
        );
        assert!(strays.is_empty(), "the generator made functions with another diagnostic:\n{}", strays.join("\n"));
        let shown = failed.iter().take(3).cloned().collect::<Vec<_>>().join("\n");
        assert!(
            failed.is_empty(),
            "{} of {functions} functions differ from the model (the first 3):\n{shown}",
            failed.len()
        );
        assert!(functions >= 700, "only {functions} functions compared");
        assert!(
            drops * 5 >= functions && clean * 5 >= functions,
            "the answers are not mixed: drop {drops}, none {clean}"
        );
    });
}
