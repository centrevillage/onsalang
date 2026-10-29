//! R-273 (spec §11.6, §15.1): the items generated for a flow do not depend on the order in which the flow
//! and the types of its heading are declared. Each test writes a package twice, with the declarations in
//! the two orders, and compares what `onsa interface` prints for the flows (the sizes, the fields of `Out`,
//! the signatures of the generated functions) or what `onsa check --json` reports. The spec does not fix the
//! text of the output, so the check is that the two orders give the same text, and that the text has the
//! fields of the struct output (so that two equal but empty outputs do not pass).
//!
//! The cases with the same shapes and values are `tests/spec/flow/generated_order_*` and
//! `tests/spec/packages/generated_order_*`.

mod test_support;

use test_support::*;

/// The lines of the flow `name` in the output of `onsa interface`: from its `pub flow` line to the blank
/// line (or the end) that ends it.
fn flow_block(text: &str, name: &str) -> String {
    let start = format!("pub flow {name}(");
    let mut out = Vec::new();
    let mut inside = false;
    for l in text.lines() {
        if l.starts_with(&start) {
            inside = true;
        } else if inside && l.trim().is_empty() {
            break;
        }
        if inside {
            out.push(l);
        }
    }
    assert!(!out.is_empty(), "no flow {name} in the output of interface:\n{text}");
    out.join("\n")
}

fn interface(d: &Dir) -> String {
    let out = run(d.root(), &["interface", "."]);
    assert_eq!(out.code, 0, "interface failed:\n{}{}", out.stdout, out.stderr);
    out.stdout
}

/// A package `demo` with the files of `files`.
fn package(tag: &str, files: &[(&str, &str)]) -> Dir {
    let d = Dir::pkg(tag);
    for (f, t) in files {
        d.write(f, t);
    }
    d
}

const STRUCTS: &str = "\
pub struct Pair {
  l: F32,
  r: F32,
}

pub struct Wide {
  v: [F32; N],
  g: F32,
}

pub const N: U32 = 2

pub struct One {
  v: F32,
}
";

const FLOWS: &str = "\
pub flow tone(seed: F32 at init, gain: F32 at block) -> Pair at sample {
  Pair { l: gain + seed, r: gain - seed }
}

pub flow spread(k: F32 at block, x: F32 at sample) -> Wide at sample {
  Wide { v: [x * k, x + k], g: k }
}

pub flow mono(x: F32 at sample) -> One at sample {
  One { v: x }
}
";

/// Same module: the flow above the types and below them print the same flows.
#[test]
fn the_interface_of_a_struct_output_is_the_same_in_both_orders_of_one_module() {
    let types_first = package("order_same_a", &[("main.onsa", &format!("{STRUCTS}\n{FLOWS}"))]);
    let flow_first = package("order_same_b", &[("main.onsa", &format!("{FLOWS}\n{STRUCTS}"))]);
    let (a, b) = (interface(&types_first), interface(&flow_first));
    for name in ["tone", "spread", "mono"] {
        let (x, y) = (flow_block(&a, name), flow_block(&b, name));
        assert_eq!(x, y, "the flow {name} differs with the order:\n--- types first\n{x}\n--- flow first\n{y}");
    }
    // The fields of the output are in the printed flow (not an empty output in both).
    let tone = flow_block(&a, "tone");
    assert!(tone.contains("l:") && tone.contains("r:"), "the fields of Pair are not in the flow:\n{tone}");
    let spread = flow_block(&a, "spread");
    assert!(spread.contains("v:") && spread.contains("g:"), "the fields of Wide are not in the flow:\n{spread}");
}

/// The types are in other modules (an alias in one, the struct in another): the module of the flow is read
/// first or last.
#[test]
fn the_interface_is_the_same_when_the_types_are_in_other_modules_in_both_orders() {
    let second = "use third.{Pair}\n\npub type Stereo = Pair\n\npub struct Wide {\n  v: [F32; N],\n  g: F32,\n}\n\npub const N: U32 = 2\n";
    let flows = "pub flow tone(seed: F32 at init, gain: F32 at block) -> Stereo at sample {\n  Pair { l: gain + seed, r: gain - seed }\n}\n\npub flow spread(k: F32 at block, x: F32 at sample) -> Wide at sample {\n  Wide { v: [x * k, x + k], g: k }\n}\n";
    let pair = "pub struct Pair {\n  l: F32,\n  r: F32,\n}\n";
    // The flow in the module read first: `first` has the flow, `third` the struct.
    let flow_first = package(
        "order_mod_a",
        &[
            ("first.onsa", &format!("use second.{{Stereo, Wide}}\nuse third.{{Pair}}\n\n{flows}")),
            ("second.onsa", second),
            ("third.onsa", pair),
        ],
    );
    // The flow in the module read last: the same declarations with `first` and `third` exchanged.
    let types_first = package(
        "order_mod_b",
        &[
            ("first.onsa", pair),
            ("second.onsa", &second.replace("use third.{Pair}", "use first.{Pair}")),
            ("third.onsa", &format!("use first.{{Pair}}\nuse second.{{Stereo, Wide}}\n\n{flows}")),
        ],
    );
    let (a, b) = (interface(&flow_first), interface(&types_first));
    for name in ["tone", "spread"] {
        let (x, y) = (flow_block(&a, name), flow_block(&b, name));
        assert_eq!(
            x, y,
            "the flow {name} differs with the order of the modules:\n--- flow first\n{x}\n--- flow last\n{y}"
        );
    }
    let tone = flow_block(&a, "tone");
    assert!(tone.contains("l:") && tone.contains("r:"), "the fields of Pair are not in the flow:\n{tone}");
}

/// `g.Params` as the output type of `h`: `h` above `g` or below it.
#[test]
fn the_generated_params_of_another_flow_as_an_output_is_the_same_in_both_orders() {
    let g = "pub flow g(x: F32 at sample, k: F32 at block) -> F32 at sample {\n  x * k\n}\n";
    let h = "pub flow h(c: F32 at init, m: F32 at block, x: F32 at sample) -> g.Params at sample {\n  g.Params { k: x * m + c }\n}\n";
    let g_first = package("order_params_a", &[("main.onsa", &format!("{g}\n{h}"))]);
    let h_first = package("order_params_b", &[("main.onsa", &format!("{h}\n{g}"))]);
    let (a, b) = (interface(&g_first), interface(&h_first));
    for name in ["g", "h"] {
        let (x, y) = (flow_block(&a, name), flow_block(&b, name));
        assert_eq!(x, y, "the flow {name} differs with the order:\n--- g first\n{x}\n--- h first\n{y}");
    }
    let h_block = flow_block(&a, "h");
    assert!(h_block.contains("k:"), "the field of Params is not in the output of h:\n{h_block}");
}

/// The diagnostics of `onsa check --json` as (code, message) in the order printed.
fn diagnostics_of(d: &Dir) -> Vec<(String, String)> {
    let out = run(d.root(), &["check", "--json", "."]);
    let doc = doc_of(&out);
    diagnostics(&doc).iter().map(|x| (str_of(x, "code").to_string(), str_of(x, "message").to_string())).collect()
}

/// `g.Out` in the input of `h` is E0710 whichever flow is declared first: the types of the inputs of a flow
/// are places of a type, where a second-class type is not (§5.3, S-772).
#[test]
fn the_generated_out_of_another_flow_as_an_input_is_the_same_error_in_both_orders() {
    let st = "pub struct St {\n  a: F32,\n}\n";
    let g = "pub flow g(x: F32 at sample) -> St at sample {\n  St { a: x }\n}\n";
    let h = "pub flow h(x: g.Out at sample) -> F32 at sample {\n  0.0\n}\n";
    let g_first = package("order_out_a", &[("main.onsa", &format!("{st}\n{g}\n{h}"))]);
    let h_first = package("order_out_b", &[("main.onsa", &format!("{st}\n{h}\n{g}"))]);
    let (a, b) = (diagnostics_of(&g_first), diagnostics_of(&h_first));
    assert_eq!(a.iter().map(|x| x.0.as_str()).collect::<Vec<_>>(), ["E0710"], "{a:?}");
    assert_eq!(a, b, "the diagnostics differ with the order");
}

/// A nested array in the struct of the output is E0810 whichever of the flow and the struct is declared first.
#[test]
fn a_nested_array_in_the_struct_of_an_output_is_the_same_error_in_both_orders() {
    let st = "pub struct St {\n  a: [[F32; 2]; 2],\n}\n";
    let g = "pub flow g(x: F32 at sample) -> St at sample {\n  St { a: [[x, x], [x, x]] }\n}\n";
    let st_first = package("order_nest_a", &[("main.onsa", &format!("{st}\n{g}"))]);
    let g_first = package("order_nest_b", &[("main.onsa", &format!("{g}\n{st}"))]);
    let (a, b) = (diagnostics_of(&st_first), diagnostics_of(&g_first));
    assert_eq!(a.iter().map(|x| x.0.as_str()).collect::<Vec<_>>(), ["E0810"], "{a:?}");
    assert_eq!(a, b, "the diagnostics differ with the order");
}
