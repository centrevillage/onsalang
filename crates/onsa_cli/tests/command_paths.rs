//! The path argument of the commands that read a package, as §18.2 fixes it for `interface`,
//! `graph` and `build` (spec §18.2, §15.1; S-323; with S-312, S-159, S-324 where they meet it;
//! W4-14 U4).
//!
//! What the spec fixes, and so what is checked here:
//! - the path is the last optional argument (a `.onsa` file, the root directory, `onsa.toml`), and
//!   a command that takes a name puts the name first: `interface [<path>]`, `graph <flow> [<path>]`,
//!   `build --target <name> [<path>]`. Without a path the manifest is searched for upwards from
//!   the working directory, and not found is a usage error (exit code 2). A module name is not a
//!   path, so `interface dsp.voice` is an I/O error (2);
//! - a file of a package makes the command read the whole package and narrow the result to the
//!   module of the file: `interface` prints the declarations of that module, `graph` finds its
//!   flow among the flows of that module. A file with no manifest above it is a package of its
//!   own. `build` has the whole package for its result, so a file is a usage error (2);
//! - `<flow>` is a name with the module path (`sub.beta.echo`) or a name that is one in the range
//!   that was chosen (the module of the file, or else the package). If it is not one, the command
//!   ends in 2 and lists the candidates (a usage error: on the standard error). A name with the
//!   module path that is not the module of the given file is 2 too;
//! - the input of the package is read the same way as `check` reads it: the `tests/` of the root
//!   is E0200 and a directory name that is not snake_case is E0320 for `interface`, `graph` and
//!   `build` too. The exit code is 1, and with `--json` the document is that of `check` (§18.1).
//!
//! Not written here: the tree that is gathered and the links (U1, `package_tree.rs`,
//! `package_links.rs`), the rule of the names (U2, U3), `check` and `test` (`package_input.rs`),
//! and the content of the manifest (W4-02). `audit`, `play` and `probe` are not in this version
//! of the CLI. The JSON of `interface` and the exact text of its output are not fixed by the spec,
//! so a declaration is looked for by the name of a `pub fn` that nothing else mentions.

mod test_support;

use std::path::{Path, PathBuf};

use serde_json::Value;
use test_support::*;

const MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"pk_\"\nfns = [\"alpha.alpha_fn\"]\n\n[targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\nprovides = []\n";

/// `alpha_fn` is used by `sub/beta.onsa`; `alpha_only_fn` and the flows `only_in_alpha` and `echo`
/// are not named by anything but this module (`echo` is in `beta` too).
const ALPHA: &str = "\
pub fn alpha_fn() -> I32 {
  1
}

pub fn alpha_only_fn() -> I32 {
  2
}

pub flow echo(x: F32 at sample, g: F32 at block) -> F32 at sample {
  let from_alpha = x * g
  from_alpha
}

pub flow only_in_alpha(x: F32 at sample) -> F32 at sample {
  let alpha_only = x * 2.0
  alpha_only
}
";

/// Uses `alpha`, has its own `echo`, and a flow that calls a flow of `alpha` and has a `par`.
const BETA: &str = "\
use alpha.{alpha_fn, only_in_alpha}

pub fn beta_fn() -> I32 {
  alpha_fn() + 1
}

pub flow echo(x: F32 at sample, g: F32 at block) -> F32 at sample {
  let from_beta = x + g
  from_beta
}

pub flow chain(x: F32 at sample) -> F32 at sample {
  let chained = only_in_alpha~(x)
  let copies = par i in 0 ..< 3 {
    only_in_alpha~(chained)
  }
  (copies[0] + copies[1] + copies[2]) * 0.25
}
";

const SOLO: &str = "\
pub fn solo_fn() -> I32 {
  1
}

pub flow tone(x: F32 at sample) -> F32 at sample {
  let solo_node = x * 0.5
  solo_node
}
";

const OK_FN: &str = "pub fn f() -> I32 {\n  1\n}\n";

fn s(x: &str) -> String {
    x.to_string()
}

/// `onsa.toml`, `alpha.onsa` and `sub/beta.onsa`. `check` finds nothing in it.
fn package(tag: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", MANIFEST);
    d.write("alpha.onsa", ALPHA);
    d.write("sub/beta.onsa", BETA);
    d
}

fn abs(d: &Dir, rel: &str) -> String {
    d.root().join(rel).to_string_lossy().into_owned()
}

fn at(d: &Dir, rel: &str) -> PathBuf {
    d.root().join(rel)
}

/// A command that ended in 2 without a diagnostic: the reason is on the standard error, and the
/// standard output is empty (§18.2, `spec/tools.md` §4).
fn assert_usage_error(out: &Out, what: &str) {
    assert_eq!(out.code, 2, "{what}: {}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout, "", "{what}: nothing on the standard output");
    assert!(!out.stderr.is_empty(), "{what}: the reason is on the standard error");
}

fn has_node(out: &Out, name: &str) -> bool {
    out.stdout.contains(&format!("\"{name}\""))
}

/// A DOT graph of a flow: the output begins with `digraph`.
fn assert_dot(out: &Out, what: &str) {
    assert_eq!(out.code, 0, "{what}: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.trim_start().starts_with("digraph"), "{what}: not a DOT graph: {}", out.stdout);
}

fn graph(cwd: &Path, args: &[&str]) -> Out {
    let mut a = vec!["graph"];
    a.extend_from_slice(args);
    run(cwd, &a)
}

fn interface(cwd: &Path, args: &[&str]) -> Out {
    let mut a = vec!["interface"];
    a.extend_from_slice(args);
    run(cwd, &a)
}

/// `(code, file)` of every diagnostic of a document, sorted.
fn json_pairs(doc: &Value) -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> =
        diagnostics(doc).iter().map(|d| (str_of(d, "code").to_string(), span_of(&d["span"]).file)).collect();
    v.sort();
    v
}

/// `(code, file)` of every diagnostic in the text output: the lines
/// `<file>:<line>:<column>: error[<code>]: <message>` (`spec/tools.md` §4), sorted.
fn text_pairs(text: &str) -> Vec<(String, String)> {
    let mut v = Vec::new();
    for line in text.lines() {
        let Some(i) = line.find(": error[") else { continue };
        let code = line[i + ": error[".len()..].split(']').next().unwrap_or("").to_string();
        let mut parts = line[..i].rsplitn(3, ':');
        let (_col, _line, file) = (parts.next(), parts.next(), parts.next().unwrap_or(""));
        v.push((code, file.to_string()));
    }
    v.sort();
    v
}

// ---- interface: the path is the last optional argument (S-323) ------------------------------------

/// §15.1, §18.2: without a file the whole package is the result, whichever way the package is named:
/// no path (searched for upwards), the directory, `onsa.toml`.
#[test]
fn interface_without_a_file_prints_every_module_of_the_package() {
    let d = package("if_whole");
    let elsewhere = Dir::bare("if_whole_elsewhere");
    let cases: Vec<(PathBuf, Vec<String>)> = vec![
        (d.root().to_path_buf(), vec![]),
        (at(&d, "sub"), vec![]),
        (d.root().to_path_buf(), vec![s(".")]),
        (d.root().to_path_buf(), vec![s("onsa.toml")]),
        (d.root().to_path_buf(), vec![s("./onsa.toml")]),
        (at(&d, "sub"), vec![s("..")]),
        (at(&d, "sub"), vec![s("../onsa.toml")]),
        (elsewhere.root().to_path_buf(), vec![d.arg()]),
        (elsewhere.root().to_path_buf(), vec![abs(&d, "onsa.toml")]),
    ];
    for (cwd, args) in cases {
        let a: Vec<&str> = args.iter().map(String::as_str).collect();
        let out = interface(&cwd, &a);
        assert_eq!(out.code, 0, "{args:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        for name in ["alpha_fn", "alpha_only_fn", "beta_fn"] {
            assert!(
                out.stdout.contains(name),
                "{args:?} from {cwd:?}: `{name}` is a declaration of the package: {}",
                out.stdout
            );
        }
        assert!(!out.stdout.contains("error["), "{args:?} from {cwd:?}: {}", out.stdout);
        let mut j = vec!["interface", "--json"];
        j.extend_from_slice(&a);
        let out = run(&cwd, &j);
        assert_eq!(out.code, 0, "{j:?} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "{j:?} from {cwd:?}: {}", out.stdout);
    }
}

/// §15.1: a file of a package gathers the package (`beta` uses `alpha`, so it is clean) and the result
/// is the declarations of the module of the file, whatever the working directory and the way the path
/// is written. The other modules of the package are not printed.
#[test]
fn interface_of_a_file_prints_the_declarations_of_its_module_only() {
    let d = package("if_file");
    let elsewhere = Dir::bare("if_file_elsewhere");
    let beta: Vec<(PathBuf, String)> = vec![
        (d.root().to_path_buf(), s("sub/beta.onsa")),
        (d.root().to_path_buf(), s("./sub/../sub/beta.onsa")),
        (at(&d, "sub"), s("beta.onsa")),
        (at(&d, "sub"), s("./beta.onsa")),
        (at(&d, "sub"), s("../sub/beta.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "sub/beta.onsa")),
    ];
    for (cwd, arg) in &beta {
        let out = interface(cwd, &[arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains("beta_fn"), "{arg} from {cwd:?}: {}", out.stdout);
        assert!(!out.stdout.contains("alpha_only_fn"), "{arg} from {cwd:?}: `alpha` is not printed: {}", out.stdout);
        assert!(!out.stdout.contains("error["), "{arg} from {cwd:?}: {}", out.stdout);
        let out = run(cwd, &["interface", "--json", arg]);
        assert_eq!(out.code, 0, "--json {arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(diagnostics(&doc_of(&out)).is_empty(), "--json {arg} from {cwd:?}: {}", out.stdout);
    }
    for (cwd, arg) in [
        (d.root().to_path_buf(), s("alpha.onsa")),
        (at(&d, "sub"), s("../alpha.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "alpha.onsa")),
    ] {
        let out = interface(&cwd, &[&arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains("alpha_fn") && out.stdout.contains("alpha_only_fn"), "{arg}: {}", out.stdout);
        assert!(!out.stdout.contains("beta_fn"), "{arg} from {cwd:?}: `beta` is not printed: {}", out.stdout);
    }
}

/// §15.1: a file with no manifest above it is a package of its own, with its own declarations only.
#[test]
fn interface_of_a_single_file_with_no_manifest_prints_that_file() {
    let d = Dir::bare("if_single");
    d.write("loose/solo.onsa", SOLO);
    d.write("loose/other.onsa", "pub fn other_fn() -> I32 {\n  3\n}\n");
    for (cwd, arg) in [(at(&d, "loose"), s("solo.onsa")), (d.root().to_path_buf(), s("loose/solo.onsa"))] {
        let out = interface(&cwd, &[&arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(out.stdout.contains("solo_fn"), "{arg}: {}", out.stdout);
        assert!(!out.stdout.contains("other_fn"), "{arg}: the file beside it is not in the package: {}", out.stdout);
    }
}

/// §15.1: the directory a loose file is in is not a path element of its module, so the name of the
/// directory is not asked (`.hid/ok.onsa` is no error).
#[test]
fn a_single_file_in_a_dot_directory_is_no_error_for_interface() {
    let d = Dir::bare("single_dot");
    d.write(".hid/solo.onsa", SOLO);
    let out = interface(d.root(), &[".hid/solo.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("solo_fn"), "{}", out.stdout);
}

#[test]
fn a_single_file_in_a_dot_directory_is_no_error_for_graph() {
    let d = Dir::bare("single_dot_graph");
    d.write(".hid/solo.onsa", SOLO);
    let out = graph(d.root(), &["tone", ".hid/solo.onsa"]);
    assert_dot(&out, "graph tone .hid/solo.onsa");
    assert!(has_node(&out, "solo_node"), "{}", out.stdout);
}

/// §18.2: `<mod>` is gone: the argument is a path, so a module name, or a module path without the
/// extension, names no file (an I/O error, 2) wherever the package is.
#[test]
fn interface_with_a_module_name_is_an_io_error() {
    let d = package("if_modname");
    for cwd in [d.root().to_path_buf(), at(&d, "sub")] {
        for name in ["alpha", "sub.beta", "sub/beta", "beta", "alpha."] {
            for json in [false, true] {
                let out = if json { interface(&cwd, &["--json", name]) } else { interface(&cwd, &[name]) };
                assert_eq!(out.code, 2, "{name} json={json} from {cwd:?}: {}{}", out.stdout, out.stderr);
                assert_eq!(out.stdout, "", "{name} json={json} from {cwd:?}: nothing on the standard output");
                assert!(!out.stderr.is_empty(), "{name} json={json}: the reason is on the standard error");
            }
        }
    }
}

// ---- graph <flow> [<path>] (S-323) -----------------------------------------------------------------

/// §18.2: the flow comes first and the path is last and optional. Every way to name the package or
/// the file of the flow finds the same flow and prints the same graph.
#[test]
fn graph_takes_the_flow_first_and_the_path_last() {
    let d = package("g_forms");
    let elsewhere = Dir::bare("g_forms_elsewhere");
    let cases: Vec<(PathBuf, Vec<String>)> = vec![
        (d.root().to_path_buf(), vec![]),
        (at(&d, "sub"), vec![]),
        (d.root().to_path_buf(), vec![s(".")]),
        (d.root().to_path_buf(), vec![s("onsa.toml")]),
        (at(&d, "sub"), vec![s("..")]),
        (at(&d, "sub"), vec![s("../onsa.toml")]),
        (elsewhere.root().to_path_buf(), vec![d.arg()]),
        (elsewhere.root().to_path_buf(), vec![abs(&d, "onsa.toml")]),
        (d.root().to_path_buf(), vec![s("alpha.onsa")]),
        (at(&d, "sub"), vec![s("../alpha.onsa")]),
        (elsewhere.root().to_path_buf(), vec![abs(&d, "alpha.onsa")]),
    ];
    let mut outputs = Vec::new();
    for (cwd, args) in cases {
        let mut a = vec!["only_in_alpha"];
        a.extend(args.iter().map(String::as_str));
        let out = graph(&cwd, &a);
        assert_dot(&out, &format!("graph {a:?} from {cwd:?}"));
        assert!(has_node(&out, "alpha_only"), "{a:?} from {cwd:?}: {}", out.stdout);
        outputs.push((format!("{a:?} from {cwd:?}"), out.stdout));
    }
    for (what, text) in &outputs[1..] {
        assert_eq!(text, &outputs[0].1, "{what}: the same flow gives the same graph as {}", outputs[0].0);
    }
}

/// §18.2: the old order (path, then flow) names a flow that is a path and a path that is a flow
/// name: both are 2, with nothing on the standard output.
#[test]
fn graph_with_the_path_before_the_flow_is_a_usage_error() {
    let d = package("g_old");
    for args in [
        vec![".", "only_in_alpha"],
        vec!["alpha.onsa", "only_in_alpha"],
        vec!["onsa.toml", "alpha.only_in_alpha"],
        vec!["sub/beta.onsa", "echo"],
    ] {
        assert_usage_error(&graph(d.root(), &args), &format!("graph {args:?}"));
    }
}

/// §18.2: a name that is one in the chosen range is enough, and a file chooses the module of the file.
/// `echo` is in both `alpha` and `sub.beta`: with no file it is not one (2, the candidates are
/// listed on the standard error), with a file it is the flow of that file.
#[test]
fn graph_of_a_file_finds_the_flow_among_the_flows_of_its_module() {
    let d = package("g_file");
    let elsewhere = Dir::bare("g_file_elsewhere");
    for (cwd, arg) in [
        (d.root().to_path_buf(), s("alpha.onsa")),
        (at(&d, "sub"), s("../alpha.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "alpha.onsa")),
    ] {
        let out = graph(&cwd, &["echo", &arg]);
        assert_dot(&out, &format!("graph echo {arg} from {cwd:?}"));
        assert!(has_node(&out, "from_alpha") && !has_node(&out, "from_beta"), "{arg}: {}", out.stdout);
    }
    for (cwd, arg) in [
        (d.root().to_path_buf(), s("sub/beta.onsa")),
        (at(&d, "sub"), s("beta.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "sub/beta.onsa")),
    ] {
        let out = graph(&cwd, &["echo", &arg]);
        assert_dot(&out, &format!("graph echo {arg} from {cwd:?}"));
        assert!(has_node(&out, "from_beta") && !has_node(&out, "from_alpha"), "{arg}: {}", out.stdout);
    }
    // with no file, and with the package or its manifest: not one
    for args in [vec!["echo"], vec!["echo", "."], vec!["echo", "onsa.toml"]] {
        let out = graph(d.root(), &args);
        assert_usage_error(&out, &format!("graph {args:?}"));
        assert!(
            out.stderr.contains("alpha") && out.stderr.contains("sub.beta"),
            "{args:?}: the candidates are listed: {}",
            out.stderr
        );
    }
    let out = graph(&at(&d, "sub"), &["echo"]);
    assert_usage_error(&out, "graph echo from sub");
    assert!(
        out.stderr.contains("alpha") && out.stderr.contains("sub.beta"),
        "the candidates are listed: {}",
        out.stderr
    );
}

/// §18.2: the name with the module path finds the flow whatever the range. With a file, the module
/// path has to be the module of the file (2 if it is not), and a flow of another module cannot be
/// chosen by its bare name either.
#[test]
fn graph_with_a_module_path_and_a_file_must_name_the_module_of_the_file() {
    let d = package("g_qualified");
    for (name, node) in [("alpha.echo", "from_alpha"), ("sub.beta.echo", "from_beta"), ("sub.beta.chain", "chained")] {
        let out = graph(d.root(), &[name]);
        assert_dot(&out, &format!("graph {name}"));
        assert!(has_node(&out, node), "{name}: {}", out.stdout);
        let out = graph(&at(&d, "sub"), &[name]);
        assert_dot(&out, &format!("graph {name} from sub"));
        assert!(has_node(&out, node), "{name} from sub: {}", out.stdout);
    }
    // a bare name that is one in the package, and a bare name of the file's module
    let out = graph(d.root(), &["only_in_alpha"]);
    assert_dot(&out, "graph only_in_alpha");
    let out = graph(d.root(), &["chain"]);
    assert_dot(&out, "graph chain");
    assert!(has_node(&out, "chained"), "{}", out.stdout);
    // the module path is the module of the file
    for (name, file) in
        [("alpha.echo", "alpha.onsa"), ("sub.beta.echo", "sub/beta.onsa"), ("alpha.only_in_alpha", "alpha.onsa")]
    {
        let out = graph(d.root(), &[name, file]);
        assert_dot(&out, &format!("graph {name} {file}"));
    }
    // the module path is another module, a module that is not there, or the flow is not there
    for args in [
        vec!["sub.beta.echo", "alpha.onsa"],
        vec!["alpha.echo", "sub/beta.onsa"],
        vec!["alpha.only_in_alpha", "sub/beta.onsa"],
        vec!["sub.nosuch.echo", "sub/beta.onsa"],
        vec!["alpha.nosuch", "alpha.onsa"],
        vec!["alpha.nosuch"],
        vec!["nosuch"],
        vec!["nosuch", "alpha.onsa"],
        vec!["nosuch", "."],
    ] {
        assert_usage_error(&graph(d.root(), &args), &format!("graph {args:?}"));
    }
    // a flow of another module of the package cannot be chosen by a file
    for args in [vec!["only_in_alpha", "sub/beta.onsa"], vec!["chain", "alpha.onsa"]] {
        assert_usage_error(&graph(d.root(), &args), &format!("graph {args:?}"));
    }
}

/// §18.2, §11.6: a flow that calls a flow of another module (`only_in_alpha~`) and has a `par` is
/// drawn from its own module, with the `let` names as nodes, whether the file narrows or the module
/// path names it.
#[test]
fn graph_of_a_flow_that_calls_another_module_and_has_a_par() {
    let d = package("g_chain");
    for args in
        [vec!["chain", "sub/beta.onsa"], vec!["sub.beta.chain", "sub/beta.onsa"], vec!["sub.beta.chain"], vec!["chain"]]
    {
        let out = graph(d.root(), &args);
        assert_dot(&out, &format!("graph {args:?}"));
        assert!(has_node(&out, "chained") && has_node(&out, "copies"), "{args:?}: {}", out.stdout);
        assert!(!has_node(&out, "from_beta") && !has_node(&out, "alpha_only"), "{args:?}: {}", out.stdout);
    }
}

/// §15.1: a file with no manifest above it is a package of its own: its module is named by the file,
/// and no flow of the package that is beside it is found.
#[test]
fn graph_of_a_single_file_with_no_manifest() {
    let d = Dir::bare("g_single");
    d.write("loose/solo.onsa", SOLO);
    d.write(
        "loose/other.onsa",
        "pub flow far(x: F32 at sample) -> F32 at sample {\n  let far_node = x\n  far_node\n}\n",
    );
    for (cwd, arg) in [(at(&d, "loose"), s("solo.onsa")), (d.root().to_path_buf(), s("loose/solo.onsa"))] {
        for name in ["tone", "solo.tone"] {
            let out = graph(&cwd, &[name, &arg]);
            assert_dot(&out, &format!("graph {name} {arg} from {cwd:?}"));
            assert!(has_node(&out, "solo_node"), "{name} {arg}: {}", out.stdout);
        }
        for name in ["other.tone", "loose.solo.tone", "far", "other.far"] {
            assert_usage_error(&graph(&cwd, &[name, &arg]), &format!("graph {name} {arg} from {cwd:?}"));
        }
    }
}

/// §15.1, §18.2: what is wrong with the path is a usage error for `graph` as for the other commands:
/// a directory with no manifest, a file that is not `.onsa` or `onsa.toml`, a file below `target/` of
/// the root, two paths, no path and no manifest above, and no flow at all.
#[test]
fn graph_with_a_path_that_is_not_a_package_input_is_a_usage_error() {
    let d = package("g_usage");
    d.write("notes.txt", "plain text\n");
    d.write("target/g.onsa", ALPHA);
    d.write("onsa.toml.bak", "plain text\n");
    let bare = Dir::bare("g_usage_bare");
    bare.write("solo.onsa", SOLO);
    for args in [
        vec!["only_in_alpha", "sub"],
        vec!["only_in_alpha", "sub/"],
        vec!["only_in_alpha", "notes.txt"],
        vec!["only_in_alpha", "onsa.toml.bak"],
        vec!["only_in_alpha", "target/g.onsa"],
        vec!["only_in_alpha", "alpha.onsa", "sub/beta.onsa"],
        vec!["only_in_alpha", ".", "."],
        vec!["only_in_alpha", "missing.onsa"],
    ] {
        assert_usage_error(&graph(d.root(), &args), &format!("graph {args:?}"));
    }
    assert_usage_error(&graph(d.root(), &[]), "graph with no flow");
    // no path and no manifest above: a `.onsa` file in the working directory is not a package
    assert_usage_error(&graph(bare.root(), &["tone"]), "graph tone with no manifest above");
    assert_usage_error(&graph(bare.root(), &["tone", "."]), "graph tone . with no manifest");
}

// ---- build --target <name> [<path>] (S-323) ----------------------------------------------------------

fn built(d: &Dir) -> bool {
    d.root().join("target/host/onsa.h").is_file()
}

/// §15.1, §18.2: `build` without a path searches for `onsa.toml` upwards like the other commands and
/// puts the product below `target/` of the root (the place that §15.1 keeps out of the modules).
#[test]
fn build_without_a_path_builds_the_package_above_the_working_directory() {
    let d = package("b_up");
    let out = run(&at(&d, "sub"), &["build", "--target", "host"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(built(&d), "the product is below target/ of the root");
    assert!(!at(&d, "sub/target").exists(), "and not below the working directory");
}

/// §18.2: the directory, `onsa.toml` and the path from another directory build the same package.
#[test]
fn build_with_a_directory_or_the_manifest_builds_that_package() {
    let d = package("b_forms");
    let elsewhere = Dir::bare("b_forms_elsewhere");
    let cases: Vec<(PathBuf, String)> = vec![
        (d.root().to_path_buf(), s(".")),
        (d.root().to_path_buf(), s("onsa.toml")),
        (d.root().to_path_buf(), s("./onsa.toml")),
        (at(&d, "sub"), s("..")),
        (at(&d, "sub"), s("../onsa.toml")),
        (elsewhere.root().to_path_buf(), d.arg()),
        (elsewhere.root().to_path_buf(), abs(&d, "onsa.toml")),
    ];
    for (cwd, arg) in cases {
        let _ = std::fs::remove_dir_all(at(&d, "target"));
        let out = run(&cwd, &["build", "--target", "host", &arg]);
        assert_eq!(out.code, 0, "{arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert!(built(&d), "{arg} from {cwd:?}: the product is below target/ of the root");
    }
}

/// §15.1, §18.2: `build` has the whole package for its result, so what is not the root of one is a
/// usage error, and nothing is built: a directory with no manifest, no path with no manifest above,
/// and a missing `--target` (the default target is not chosen without being said, §12.1).
#[test]
fn build_with_a_path_that_is_not_the_root_of_a_package_is_a_usage_error_and_builds_nothing() {
    let d = package("b_usage");
    let bare = Dir::bare("b_usage_bare");
    bare.write("solo.onsa", SOLO);
    let out = run(d.root(), &["build", "--target", "host", "sub"]);
    assert_usage_error(&out, "build sub");
    let out = run(&at(&d, "sub"), &["build", "--target", "host", "."]);
    assert_usage_error(&out, "build . in sub");
    assert!(!built(&d) && !at(&d, "sub/target").exists(), "nothing is built");
    let out = run(bare.root(), &["build", "--target", "host"]);
    assert_usage_error(&out, "build with no path and no manifest above");
    let out = run(bare.root(), &["build", "--target", "host", "."]);
    assert_usage_error(&out, "build . with no manifest");
    assert!(!bare.root().join("target").exists(), "nothing is built");
    for args in [vec!["build"], vec!["build", "."], vec!["build", "onsa.toml"]] {
        let out = run(d.root(), &args);
        assert_usage_error(&out, &format!("{args:?} without --target"));
    }
    assert!(!built(&d), "nothing is built");
}

/// §15.1, §18.2: a file is a usage error for `build` also when it is the file of the package that
/// is found upwards from it, or one that has no package, and also from another directory.
#[test]
fn build_with_a_file_is_a_usage_error_whichever_package_the_file_is_in() {
    let d = package("b_file");
    let elsewhere = Dir::bare("b_file_elsewhere");
    elsewhere.write("solo.onsa", SOLO);
    for (cwd, arg) in [
        (d.root().to_path_buf(), s("alpha.onsa")),
        (d.root().to_path_buf(), s("sub/beta.onsa")),
        (at(&d, "sub"), s("beta.onsa")),
        (elsewhere.root().to_path_buf(), abs(&d, "alpha.onsa")),
        (elsewhere.root().to_path_buf(), s("solo.onsa")),
    ] {
        let out = run(&cwd, &["build", "--target", "host", &arg]);
        assert_usage_error(&out, &format!("build {arg} from {cwd:?}"));
    }
    assert!(!built(&d), "nothing is built");
}

// ---- the input of the package is read the same way as `check` reads it ------------------------------

/// A package with a module and a `tests/` file at the root and a directory whose name is not
/// snake_case: `check` finds E0200 and E0320.
fn package_with_bad_inputs(tag: &str) -> Dir {
    let d = Dir::bare(tag);
    d.write("onsa.toml", MANIFEST);
    d.write("alpha.onsa", ALPHA);
    d.write("tests/x.onsa", OK_FN);
    d.write("Bad-Dir/y.onsa", OK_FN);
    d
}

fn check_pairs(cwd: &Path, args: &[&str]) -> Vec<(String, String)> {
    let mut a = vec!["check", "--json"];
    a.extend_from_slice(args);
    let out = run(cwd, &a);
    assert_eq!(out.code, 1, "{a:?}: {}{}", out.stdout, out.stderr);
    json_pairs(&doc_of(&out))
}

/// §15.1: the `tests/` of the root is E0200 for the commands that gather the modules, and the
/// directory name is E0320, for `interface`, `graph` and `build` as for `check`. The exit code is 1
/// (the command found a problem, §18.2), and with `--json` the document is that of `check` (§18.1).
#[test]
fn interface_graph_and_build_report_the_input_diagnostics_that_check_reports() {
    let d = package_with_bad_inputs("same_input");
    let want = check_pairs(d.root(), &["."]);
    assert!(want.contains(&(s("E0200"), s("tests/x.onsa"))), "{want:?}");
    assert!(want.contains(&(s("E0320"), s("Bad-Dir/y.onsa"))), "{want:?}");
    let elsewhere = Dir::bare("same_input_elsewhere");
    // `interface`, with and without `--json`: the path forms that this version reads
    for (cwd, arg) in [
        (d.root().to_path_buf(), s(".")),
        (d.root().to_path_buf(), s("onsa.toml")),
        (elsewhere.root().to_path_buf(), d.arg()),
    ] {
        let out = run(&cwd, &["interface", "--json", &arg]);
        assert_eq!(out.code, 1, "interface --json {arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(json_pairs(&doc_of(&out)), want, "interface --json {arg} from {cwd:?}");
        let out = run(&cwd, &["interface", &arg]);
        assert_eq!(out.code, 1, "interface {arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(text_pairs(&out.stdout), want, "interface {arg} from {cwd:?}");
    }
    // `build`, with the directory as before
    for (cwd, arg) in [
        (d.root().to_path_buf(), s(".")),
        (d.root().to_path_buf(), s("onsa.toml")),
        (elsewhere.root().to_path_buf(), d.arg()),
    ] {
        let out = run(&cwd, &["build", "--target", "host", &arg]);
        assert_eq!(out.code, 1, "build {arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(text_pairs(&out.stdout), want, "build {arg} from {cwd:?}");
    }
}

/// The same for the forms that are new in S-323: no path (the package above), and `graph <flow> <path>`.
#[test]
fn the_new_path_forms_report_the_same_input_diagnostics() {
    let d = package_with_bad_inputs("same_input_new");
    let want = check_pairs(d.root(), &["."]);
    let elsewhere = Dir::bare("same_input_new_elsewhere");
    for cwd in [d.root().to_path_buf(), at(&d, "Bad-Dir")] {
        let out = run(&cwd, &["interface", "--json"]);
        assert_eq!(out.code, 1, "interface --json from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(json_pairs(&doc_of(&out)), want, "interface --json from {cwd:?}");
        let out = run(&cwd, &["build", "--target", "host"]);
        assert_eq!(out.code, 1, "build from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(text_pairs(&out.stdout), want, "build from {cwd:?}");
        let out = graph(&cwd, &["only_in_alpha"]);
        assert_eq!(out.code, 1, "graph from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(text_pairs(&out.stdout), want, "graph from {cwd:?}");
    }
    for (cwd, arg) in [
        (d.root().to_path_buf(), s(".")),
        (d.root().to_path_buf(), s("onsa.toml")),
        (elsewhere.root().to_path_buf(), d.arg()),
    ] {
        let out = graph(&cwd, &["only_in_alpha", &arg]);
        assert_eq!(out.code, 1, "graph only_in_alpha {arg} from {cwd:?}: {}{}", out.stdout, out.stderr);
        assert_eq!(text_pairs(&out.stdout), want, "graph only_in_alpha {arg} from {cwd:?}");
    }
}

/// §15.1: a file given by its path that is in the `tests/` of the root is E0200 (it is not a module),
/// and one below a directory with a bad name is E0320 on the file, for `interface` as for `check`.
#[test]
fn interface_of_a_file_in_tests_or_in_a_bad_directory_reports_the_error_of_that_file() {
    let d = package_with_bad_inputs("same_input_file");
    for (arg, want) in [("tests/x.onsa", ("E0200", "tests/x.onsa")), ("Bad-Dir/y.onsa", ("E0320", "Bad-Dir/y.onsa"))] {
        let (code, file) = want;
        let checked = check_pairs(d.root(), &[arg]);
        assert!(checked.contains(&(s(code), s(file))), "check {arg}: {checked:?}");
        let out = run(d.root(), &["interface", "--json", arg]);
        assert_eq!(out.code, 1, "interface --json {arg}: {}{}", out.stdout, out.stderr);
        let got = json_pairs(&doc_of(&out));
        assert!(got.contains(&(s(code), s(file))), "interface --json {arg}: {got:?}");
        let out = run(d.root(), &["interface", arg]);
        assert_eq!(out.code, 1, "interface {arg}: {}{}", out.stdout, out.stderr);
        assert!(text_pairs(&out.stdout).contains(&(s(code), s(file))), "interface {arg}: {}", out.stdout);
    }
}

// ---- a package inside a package (S-324) --------------------------------------------------------------

/// `inner/` has its own manifest, so it is a package of its own: not gathered by the outer package,
/// and the package of the files below it.
fn package_with_a_nested_package(tag: &str) -> Dir {
    let d = package(tag);
    d.write("inner/onsa.toml", "[package]\nname = \"inner_pkg\"\nedition = \"2026\"\n");
    d.write(
        "inner/x.onsa",
        "pub fn inner_fn() -> I32 {\n  4\n}\n\npub flow inner_flow(x: F32 at sample) -> F32 at sample {\n  let inner_node = x * 3.0\n  inner_node\n}\n",
    );
    d.write("inner/y.onsa", "pub fn inner_other_fn() -> I32 {\n  5\n}\n");
    d
}

/// §15.1: the outer package does not gather `inner/`, and the inner package is read by its directory
/// or its manifest: its own modules, and not those of the outer package.
#[test]
fn interface_of_a_nested_package_is_that_package_and_the_outer_one_does_not_gather_it() {
    let d = package_with_a_nested_package("nested_if");
    for arg in ["inner", "inner/onsa.toml"] {
        let out = interface(d.root(), &[arg]);
        assert_eq!(out.code, 0, "{arg}: {}{}", out.stdout, out.stderr);
        for name in ["inner_fn", "inner_other_fn"] {
            assert!(out.stdout.contains(name), "{arg}: {}", out.stdout);
        }
        assert!(!out.stdout.contains("beta_fn"), "{arg}: the outer package is not read: {}", out.stdout);
    }
    let out = interface(d.root(), &["."]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("beta_fn"), "{}", out.stdout);
    assert!(!out.stdout.contains("inner_fn"), "the inner package is not gathered: {}", out.stdout);
}

/// §15.1, §18.2: a file below the inner manifest belongs to the inner package, and the result is the
/// module of the file; with no path from inside `inner/` the package is the inner one.
#[test]
fn interface_of_a_file_of_a_nested_package_is_the_module_of_the_file_in_the_inner_package() {
    let d = package_with_a_nested_package("nested_if_file");
    let out = interface(d.root(), &["inner/x.onsa"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("inner_fn"), "{}", out.stdout);
    for name in ["inner_other_fn", "beta_fn", "alpha_fn"] {
        assert!(!out.stdout.contains(name), "`{name}` is not in the module of the file: {}", out.stdout);
    }
    let out = interface(&at(&d, "inner"), &[]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("inner_fn") && out.stdout.contains("inner_other_fn"), "{}", out.stdout);
    assert!(!out.stdout.contains("beta_fn"), "{}", out.stdout);
}

#[test]
fn graph_of_a_flow_of_a_nested_package_is_found_in_that_package_only() {
    let d = package_with_a_nested_package("nested_graph");
    for (cwd, args) in [
        (d.root().to_path_buf(), vec!["inner_flow", "inner/x.onsa"]),
        (d.root().to_path_buf(), vec!["x.inner_flow", "inner/x.onsa"]),
        (d.root().to_path_buf(), vec!["inner_flow", "inner"]),
        (d.root().to_path_buf(), vec!["inner_flow", "inner/onsa.toml"]),
        (at(&d, "inner"), vec!["inner_flow"]),
        (at(&d, "inner"), vec!["x.inner_flow", "x.onsa"]),
    ] {
        let out = graph(&cwd, &args);
        assert_dot(&out, &format!("graph {args:?} from {cwd:?}"));
        assert!(has_node(&out, "inner_node"), "{args:?} from {cwd:?}: {}", out.stdout);
    }
    // the outer package has no such flow, and the path of the module is from the root of its package
    for (cwd, args) in [
        (d.root().to_path_buf(), vec!["inner_flow"]),
        (d.root().to_path_buf(), vec!["inner_flow", "."]),
        (d.root().to_path_buf(), vec!["inner_flow", "alpha.onsa"]),
        (d.root().to_path_buf(), vec!["inner.x.inner_flow", "inner/x.onsa"]),
        (at(&d, "inner"), vec!["only_in_alpha"]),
    ] {
        assert_usage_error(&graph(&cwd, &args), &format!("graph {args:?} from {cwd:?}"));
    }
}
