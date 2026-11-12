//! `onsa_cases`: what the test runner and the compiler hold, as JSON, for the
//! gate's tools. Each list is read with the same code as the test runner and
//! the compiler, so the tools never parse Rust or Onsa source themselves.
//!
//! ```text
//! onsa_cases [ROOT]          the cases under tests/ and their settings (tools/spec_sections.py)
//! onsa_cases --run [--hosts] [ROOT]  run every case; the markers each compared (tools/diag_codes.py, K-13);
//!                            with `--hosts`, the host sequences too (tools/run_cases.py)
//! onsa_cases --c ITEM [ROOT] a gate item of the C checks (Q-07, W1-06; `onsa_tests::ccheck`)
//! onsa_cases --c-items       the names of those items (the cross-check item, tools/crosscheck.py, matches them with the gate's)
//! onsa_cases --vectors IMPL [ROOT]  the test vectors against `interp` or `c` (gate items vectors-interp,
//!                            vectors-c; W2-02, `onsa_tests::vectors`)
//! onsa_cases --codes         the registry of diagnostic codes (tools/diag_codes.py, S-109)
//! onsa_cases --keywords      the keywords of the lexer, `onsa_syntax::token::KEYWORDS` (tools/keywords.py)
//! onsa_cases --continuing    the symbols after which a line goes on, `onsa_tests::inventory::continuing_spellings` (tools/fmt_props.py)
//! onsa_cases --symbols       the symbols of more than one character, `onsa_tests::inventory::long_symbols` (tools/fmt_props.py)
//! onsa_cases --std-names     the names the embedded std declares (tools/builtin_names.py, Q-14)
//! onsa_cases --builtin-members  the builtin methods and associated items of sema's table (the same)
//! onsa_cases --fix-same-place FILE...  the near "same place" of the fix contract for the fuzzing
//!                            (tools/fuzz.py, S-236, W3-17; `onsa_tests::fix_contract::same_place`)
//! onsa_cases --fix-contract FILE...  the contract of the fix candidates of §18.1, as a case's,
//!                            on each file (`onsa_tests::single_files::fix_contract`)
//! onsa_cases --default-inits FILE...  the delay calls whose `init` is the default (tools/default_inits.py, S-539)
//! onsa_cases --fix-loop [--json] [--branches] [--pick first|last] [--steps N] [--states N] [--diverge N] FILE...
//!                            the fix candidates applied again and again until the loop stops
//!                            (S-236, rules/criteria.md 7.27, W3-22; `onsa_tests::fix_loop`)
//! onsa_cases --fix-loop-gate [ROOT]  the gate item fix-loop (`onsa_tests::fix_loop::gate`)
//! onsa_cases --fmt FILE      what `onsa fmt FILE` would write, on the standard output; the file is
//!                            not written (tools/fmt_props.py, X-1 U12)
//! onsa_cases --phases [--lower] [--rounds N] PATH...  the time of each phase of the compiler on
//!                            each input (X-20, `onsa_tests::phases`)
//! onsa_cases --serve         the commands of the gate's tools on the texts of the standard input,
//!                            one request after another (tools/batch.py; `onsa_tests::serve`)
//! onsa_cases --test-items [ROOT]  where the test modules of crates/*/src are, as the scan of the
//!                            tests of onsa_diag reads them (the gate item cross-check, RF-21)
//! ```
//!
//! The first form prints:
//!
//! ```text
//! [{"path": "tests/spec/fn/mean.onsa", "kind": "file", "name": "mean",
//!   "mode": "check", "spec": ["§6.1"], "golden": [], "golden_graph": [],
//!   "conformance": false, "targets": [], "manifest": null,
//!   "files": [{"path": "tests/spec/fn/mean.onsa", "syntax_errors": false}]}, ...]
//! ```
//!
//! `manifest` is the manifest of a file's fragment without its `[test]`
//! table, as TOML (an `onsa.toml` does not take it; `tools/compare.py c`
//! builds the case as a package with it), `null` for a package and for a
//! fragment of `[test]` alone.
//!
//! `files` are the source files of the case (from the repository root), and
//! whether the lexer or the parser reports a diagnostic on each
//! (`onsa_syntax::Parsed::syntax_errors`, the one place `fmt` decides to
//! refuse a file; `tools/fmt_props.py` reads it, W3-02/b 5).
//!
//! `--run` prints the form of `onsa_tests::run::runs_json`; it does not run
//! the host sequences of the cases (`host_names` names them) unless
//! `--hosts` is given: they then run as `cargo test -p onsa_tests --test cases`
//! runs them (without a C compiler, a problem of kind `harness`). Exits 1 when a
//! case or a std module cannot be read (`--run` reports those in its
//! `errors` and in the runs instead, and exits 0), 2 on a usage error.
//!
//! `--c ITEM` prints a line per case of the item and exits 1 when the item
//! fails after `tests/pending.toml` is applied, 2 when it cannot run (a
//! compiler is missing; `onsa_tests::ccheck`). `--vectors IMPL` prints the
//! failing and pending operations and exits the same way.
//!
//! `--fix-same-place` checks each file as `onsa check` does (a single-file
//! package) and prints, in the order of the files,
//!
//! ```text
//! [{"file": "m.onsa", "candidates": 2,
//!   "violations": [{"code": "E0010", "line": 2, "col": 3, "title": "parenthesize the `&&`",
//!                   "left": "E0010", "left_line": 2, "left_col": 3, "message": "..."}],
//!   "internal": null, "unreadable": null}, ...]
//! ```
//!
//! `internal`: the check of the file itself ended in an internal error;
//! `unreadable`: the file cannot be read (or is not UTF-8). Exits 0, 2 on a
//! usage error.
//!
//! `--fix-contract` prints a line per problem and a line of the counts
//! (`onsa_tests::single_files::fix_contract`; give it inputs that hold one
//! error a unit) and exits 0 when it passes, 1 otherwise, 2 on a usage error:
//!
//! ```text
//! m.onsa:2:11 E0010 fix1 `read it as `(a && b) || c``: after it, the units its edits touch hold 3:3 E0010 ...
//! fix-contract: 1 file(s), 2 candidate(s), 1 problem(s)
//! ```
//!
//! `--fix-loop` checks each file as `--fix-same-place` does and, step by
//! step, applies the first candidate of the first reported diagnostic that
//! has candidates (`--pick last`: the last one) and checks the text again,
//! until the walk stops: `clean`, `no-candidate`, `cycle` (`how` = `state`
//! or `undo`), `limit` (`--steps N`), `diverge` (`--diverge N`), `internal`
//! or `cannot-apply`. `--branches` walks every candidate, the walks that take
//! fewer other candidates first, at most `--states N` texts after the walk
//! that takes none. The stops (counted by walk, not by text), the
//! defaults and the order of the branches are `onsa_tests::fix_loop`'s
//! documentation. It prints a line per file and a line per step:
//!
//! ```text
//! m.onsa: cycle (undoes step 1) after 3 steps; 2 errors at the start (--pick first)
//!   1. E0812 2:3 candidate 1/1 `remove `~`` -> 2 errors
//!   2. E0020 5:1 candidate 1/1 `remove the visibility` -> 1 error
//!   3. E0811 2:3 candidate 1/1 `add `~`` -> 0 errors
//! ```
//!
//! (a step's place is in the text before it), or with `--json`
//!
//! ```text
//! [{"file": "m.onsa", "errors": 2, "pick": "first", "branches": false,
//!   "stops": {"cycle": 1}, "undos": 1, "longest": 3, "explored": 4, "joined": 0,
//!   "truncated": false, "discrepancies": null,
//!   "walks": [{"stop": "cycle", "how": "undo", "back_to": 1,
//!              "steps": [{"code": "E0812", "line": 2, "col": 3, "candidate": 1, "of": 1,
//!                         "title": "remove `~`", "errors": 2}, ...]}],
//!   "internal": null, "unreadable": null}, ...]
//! ```
//!
//! `walks` holds the first walk and those that stop on neither `clean` nor
//! `no-candidate` (at most 20: `cycle`, then `diverge`, `internal`,
//! `cannot-apply`, `limit`). Exits 0, 2 on a usage error.
//!
//! `--fmt FILE` formats with the command's function (`onsa_driver::format_file`,
//! with its check of the output, `spec/tools.md` §3.5; `onsa_tests::single_files::fmt`,
//! which `--serve` runs too) and ends as `onsa fmt`
//! does: 2 when the file cannot be read or has a syntax diagnostic (§3.1;
//! the diagnostics go to the standard error, as text, since the standard
//! output is the formatted text), 101 on an internal error, printed as the
//! command prints it (`onsa: internal error: …`).
//!
//! `--fix-loop-gate` is the gate item `fix-loop` over ROOT (default: the
//! repository; `onsa_tests::fix_loop::gate`). Exits 1 when it fails to walk
//! what it says, or a walk ends in a cycle or at the limit (S-475) on an
//! input `tests/pending.toml` does not hold.
//!
//! `--phases` checks each PATH (a `.onsa` file or a package, as `onsa check`
//! reads it) N times (default 3) and prints a line per path, the least
//! microseconds of the whole and of each phase (`onsa_diag::timing`):
//!
//! ```text
//! {"path": "m.onsa", "outcome": "Clean", "total_us": 5120, "phases_us": {"syntax": 1830, ...}}
//! ```
//!
//! With `--lower`, a check with no diagnostic goes on to Core and its verifier.
//! A path that cannot be read is a line `{"path": …, "error": …}`. Exits 0, 2
//! on a usage error.

use std::path::PathBuf;
use std::process::ExitCode;

// The scan is the tests' of onsa_diag, one file (RF-21).
#[path = "../../../onsa_diag/src/unsupported/tests/scan.rs"]
mod scan;

/// The forms of the command, in the order of the usage: the flag (`""`: none),
/// the least and the most arguments after it, and the words of the usage after it.
const FORMS: &[(&str, usize, usize, &str)] = &[
    ("", 0, 1, "[ROOT]"),
    ("--run", 0, 2, "[--hosts] [ROOT]"),
    ("--c", 1, 2, "ITEM [ROOT]"),
    ("--vectors", 1, 2, "interp|c [ROOT]"),
    ("--c-items", 0, 0, ""),
    ("--codes", 0, 0, ""),
    ("--keywords", 0, 0, ""),
    ("--continuing", 0, 0, ""),
    ("--symbols", 0, 0, ""),
    ("--std-names", 0, 0, ""),
    ("--builtin-members", 0, 0, ""),
    ("--fix-same-place", 1, MANY, "FILE..."),
    ("--fix-contract", 1, MANY, "FILE..."),
    ("--default-inits", 1, MANY, "FILE..."),
    ("--fix-loop", 1, MANY, "[--json] [--branches] [--pick first|last] [--steps N] [--states N] [--diverge N] FILE..."),
    ("--fix-loop-gate", 0, 1, "[ROOT]"),
    ("--fmt", 1, 1, "FILE"),
    ("--phases", 1, MANY, "[--lower] [--rounds N] PATH..."),
    ("--serve", 0, 0, ""),
    ("--test-items", 0, 1, "[ROOT]"),
];
const MANY: usize = usize::MAX;

/// The usage, from [`FORMS`].
fn usage_text() -> String {
    let forms: Vec<String> =
        FORMS.iter().map(|(flag, _, _, words)| format!("{flag} {words}").trim().to_string()).collect();
    format!("onsa_cases {}", forms.join(" | "))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mode, rest) = match args.first().map(String::as_str) {
        Some(m) if m.starts_with("--") => (m, &args[1..]),
        _ => ("", &args[..]),
    };
    let root = || match rest.first() {
        Some(r) => PathBuf::from(r),
        None => onsa_tests::case::repo_root(),
    };
    // A flag the table does not have takes no argument: it is unknown (the last arm).
    let form = FORMS.iter().find(|f| f.0 == mode);
    if !form.map_or(rest.is_empty(), |&(_, least, most, _)| (least..=most).contains(&rest.len())) {
        eprintln!("usage: {}", usage_text());
        return ExitCode::from(2);
    }
    match mode {
        "" => cases(&root()),
        "--run" => {
            let hosts = rest.first().is_some_and(|a| a == "--hosts");
            let rest = &rest[usize::from(hosts)..];
            if rest.len() > 1 || rest.first().is_some_and(|a| a.starts_with("--")) {
                return usage("--run takes `--hosts` and then the root");
            }
            let root = rest.first().map(PathBuf::from).unwrap_or_else(onsa_tests::case::repo_root);
            let (cases, errors) = onsa_tests::case::collect(&root);
            let steps = if hosts { onsa_tests::run::HostSteps::Run } else { onsa_tests::run::HostSteps::Skip };
            let runs = onsa_tests::run::run_each(&root, &cases, |_| onsa_tests::golden::Update::Off, steps);
            print(&onsa_tests::run::runs_json(&runs, &errors));
            ExitCode::SUCCESS
        }
        "--c" => {
            let Some(item) = onsa_tests::c::item(&rest[0]) else {
                let names: Vec<&str> = onsa_tests::c::ITEMS.iter().map(|i| i.name).collect();
                eprintln!("unknown item `{}` (one of {})", rest[0], names.join(", "));
                return ExitCode::from(2);
            };
            let root = rest.get(1).map(PathBuf::from).unwrap_or_else(onsa_tests::case::repo_root);
            let report = onsa_tests::ccheck::run_item(&root, item);
            println!("{}", report.text());
            ExitCode::from(report.exit_code())
        }
        "--vectors" => {
            let Some(which) = onsa_tests::vectors::Impl::parse(&rest[0]) else {
                eprintln!("unknown implementation `{}` (interp or c)", rest[0]);
                return ExitCode::from(2);
            };
            let root = rest.get(1).map(PathBuf::from).unwrap_or_else(onsa_tests::case::repo_root);
            let report = onsa_tests::vectors::run_item(&root, which);
            println!("{}", onsa_tests::vectors::text(&report));
            ExitCode::from(report.exit_code())
        }
        "--fix-same-place" => {
            print!("{}", onsa_tests::single_files::fix_same_place(rest, onsa_tests::single_files::read_input));
            ExitCode::SUCCESS
        }
        "--fix-contract" => {
            let (out, passed) = onsa_tests::single_files::fix_contract(rest, onsa_tests::single_files::read_input);
            print!("{out}");
            if passed { ExitCode::SUCCESS } else { ExitCode::FAILURE }
        }
        "--serve" => {
            // As `onsa` does before its command.
            onsa_driver::verify_core_in_debug_only();
            match onsa_tests::serve::serve(&mut std::io::stdin().lock(), &mut std::io::stdout().lock()) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("onsa_cases --serve: {e}");
                    ExitCode::from(2)
                }
            }
        }
        "--default-inits" => {
            print(&serde_json::json!(default_inits(rest)));
            ExitCode::SUCCESS
        }
        "--fix-loop" => match fix_loop_args(rest) {
            Ok((options, json, files)) => {
                let reports = onsa_tests::fix_loop::walk_files(&files, &options);
                if json {
                    print(&serde_json::json!(reports));
                } else {
                    print!("{}", onsa_tests::fix_loop::text(&reports));
                }
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("{e}; usage: {}", usage_text());
                ExitCode::from(2)
            }
        },
        "--fix-loop-gate" => {
            let g = onsa_tests::fix_loop::gate(&root(), onsa_tests::fix_loop::GATE_BUDGET);
            println!("{}", g.text);
            if g.failed { ExitCode::FAILURE } else { ExitCode::SUCCESS }
        }
        "--fmt" => fmt(&rest[0]),
        "--phases" => phases(rest),
        "--test-items" => {
            let root = root();
            print(&serde_json::json!(scan::test_module_answers(&root, &scan::crate_sources(&root.join("crates")))));
            ExitCode::SUCCESS
        }
        "--c-items" => {
            print(&serde_json::json!(onsa_tests::c::ITEMS.iter().map(|i| i.name).collect::<Vec<_>>()));
            ExitCode::SUCCESS
        }
        "--codes" => {
            print(&onsa_tests::inventory::codes());
            ExitCode::SUCCESS
        }
        "--keywords" => {
            print(&serde_json::json!(onsa_syntax::token::KEYWORDS.iter().map(|k| k.text).collect::<Vec<_>>()));
            ExitCode::SUCCESS
        }
        "--continuing" => {
            print(&serde_json::json!(onsa_tests::inventory::continuing_spellings()));
            ExitCode::SUCCESS
        }
        "--symbols" => {
            print(&serde_json::json!(onsa_tests::inventory::long_symbols()));
            ExitCode::SUCCESS
        }
        "--builtin-members" => {
            print(&serde_json::json!(onsa_tests::inventory::builtin_member_names()));
            ExitCode::SUCCESS
        }
        "--std-names" => match onsa_tests::inventory::std_names() {
            Ok(names) => {
                print(&serde_json::json!(names));
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("{e}");
                ExitCode::FAILURE
            }
        },
        other => {
            eprintln!("unknown option `{other}`; usage: {}", usage_text());
            ExitCode::from(2)
        }
    }
}

/// The manifest of the fragment of a file case without its `[test]` table,
/// as TOML (`None`: a package, or `[test]` alone).
fn fragment_manifest(s: &onsa_tests::case::Setup) -> Result<Option<String>, String> {
    let Some(m) = s.input.manifest.as_ref().filter(|m| m.form == onsa_driver::ManifestForm::Fragment) else {
        return Ok(None);
    };
    let mut table: toml::Table = toml::from_str(&m.text).map_err(|e| format!("fragment: {e}"))?;
    table.remove("test");
    let text = toml::to_string(&table).map_err(|e| format!("fragment without [test]: {e}"))?;
    Ok((!table.is_empty()).then_some(text))
}

/// The source files of a case, from the repository root, with whether the
/// lexer or the parser reports a diagnostic on each.
fn files(c: &onsa_tests::case::Case, s: &onsa_tests::case::Setup) -> serde_json::Value {
    let files: Vec<serde_json::Value> = s
        .input
        .files
        .iter()
        .map(|f| {
            let path = match c.kind {
                onsa_tests::case::CaseKind::File => c.path.clone(),
                onsa_tests::case::CaseKind::Package => format!("{}/{}", c.path, f.path),
            };
            // The parser may panic on a broken input; that is the runner's to report.
            let syntax_errors =
                onsa_driver::guard(|| onsa_syntax::parse(onsa_diag::FileId(0), &f.text).syntax_errors())
                    .unwrap_or(true);
            serde_json::json!({"path": path, "syntax_errors": syntax_errors})
        })
        .collect();
    serde_json::json!(files)
}

/// `--default-inits`: the delay calls of each file and those whose `init`
/// equals the default (S-539, `tools/default_inits.py`), each file on a thread
/// with the stack of a command; an unreadable file or an internal error is
/// reported, never skipped.
fn default_inits(files: &[String]) -> Vec<serde_json::Value> {
    onsa_tests::single_files::on_stacks(files.len(), |i| {
        let path = &files[i];
        match onsa_tests::single_files::read_input(path) {
            Err(e) => serde_json::json!({"file": path, "unreadable": e}),
            Ok(text) => match onsa_driver::guard(|| onsa_tests::default_inits::find(&text)) {
                Ok(found) => {
                    let mut v = serde_json::json!(found);
                    v["file"] = serde_json::json!(path);
                    v
                }
                Err(e) => serde_json::json!({"file": path, "internal": e.message}),
            },
        }
    })
}

/// The options and the files of `--fix-loop`, and whether it prints JSON.
fn fix_loop_args(args: &[String]) -> Result<(onsa_tests::fix_loop::Options, bool, Vec<String>), String> {
    let mut options = onsa_tests::fix_loop::Options::default();
    let mut json = false;
    let mut files = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut number = |name: &str| -> Result<usize, String> {
            let v = it.next().ok_or_else(|| format!("{name} needs a number"))?;
            v.parse().ok().filter(|&n| n > 0).ok_or_else(|| format!("{name} needs a number above 0, not `{v}`"))
        };
        match a.as_str() {
            "--json" => json = true,
            "--branches" => options.branches = true,
            "--pick" => {
                let v = it.next().map(String::as_str).unwrap_or("");
                options.pick =
                    onsa_tests::fix_loop::Pick::parse(v).ok_or_else(|| format!("--pick first|last, not `{v}`"))?;
            }
            "--steps" => options.steps = Some(number("--steps")?),
            "--states" => options.states = number("--states")?,
            "--diverge" => options.diverge = number("--diverge")?,
            o if o.starts_with("--") => return Err(format!("unknown option `{o}` of --fix-loop")),
            f => files.push(f.to_string()),
        }
    }
    if files.is_empty() {
        return Err("--fix-loop needs a file".into());
    }
    Ok((options, json, files))
}

fn phases(args: &[String]) -> ExitCode {
    let (mut lower, mut rounds, mut paths) = (false, 3, Vec::new());
    let mut args = args.iter();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--lower" => lower = true,
            "--rounds" => match args.next().and_then(|n| n.parse().ok()) {
                Some(n) => rounds = n,
                None => return usage("--rounds needs a number"),
            },
            o if o.starts_with("--") => return usage(&format!("unknown option `{o}` of --phases")),
            p => paths.push(p),
        }
    }
    if paths.is_empty() {
        return usage("--phases needs a path");
    }
    for p in paths {
        let measured = onsa_driver::read_input(Some(std::path::Path::new(p)))
            .and_then(|input| onsa_tests::phases::measure(&input, lower, rounds));
        match measured {
            Ok((outcome, times)) => println!("{}", onsa_tests::phases::json(p, outcome, &times)),
            Err(e) => println!("{}", serde_json::json!({"path": p, "error": e})),
        }
    }
    ExitCode::SUCCESS
}

fn usage(e: &str) -> ExitCode {
    eprintln!("{e}; usage: {}", usage_text());
    ExitCode::from(2)
}

/// `--fmt FILE`: the text `onsa fmt FILE` would write, on the standard output.
fn fmt(path: &str) -> ExitCode {
    // Read and refused as the command reads them (a file that is not UTF-8 too).
    match onsa_tests::single_files::fmt(path, std::fs::read_to_string(path)) {
        Ok(out) => {
            use std::io::Write;
            let mut stdout = std::io::stdout().lock();
            if let Err(e) = stdout.write_all(out.as_bytes()).and_then(|()| stdout.flush()) {
                eprintln!("onsa: cannot write to standard output: {e}");
                return ExitCode::from(2);
            }
            ExitCode::SUCCESS
        }
        Err((code, err)) => {
            eprint!("{err}");
            ExitCode::from(code)
        }
    }
}

fn print(v: &serde_json::Value) {
    println!("{}", serde_json::to_string_pretty(v).expect("serializes"));
}

fn cases(root: &std::path::Path) -> ExitCode {
    let mut items = Vec::new();
    let mut failed = false;
    let (cases, errors) = onsa_tests::case::collect(root);
    for e in &errors {
        eprintln!("{e}");
        failed = true;
    }
    for c in cases {
        let read = c.setup.clone().and_then(|s| Ok((s.targets()?, fragment_manifest(&s)?, s)));
        match read {
            Ok((targets, manifest, s)) => items.push(serde_json::json!({
                "path": c.path,
                "kind": c.kind,
                "name": c.name,
                "mode": s.test.mode,
                "spec": s.test.spec,
                "golden": s.test.golden,
                "golden_graph": s.test.golden_graph,
                "conformance": s.test.conformance,
                "targets": targets,
                "manifest": manifest,
                "files": files(&c, &s),
            })),
            Err(e) => {
                eprintln!("{}: {e}", c.path);
                failed = true;
            }
        }
    }
    print(&serde_json::json!(items));
    if failed { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

#[cfg(test)]
mod tests {
    use onsa_driver::ManifestForm;

    /// W5-13 U9b: the `manifest` of the list is the fragment without its
    /// `[test]` table (its tables below it too), none for `[test]` alone or a
    /// package's `onsa.toml`.
    #[test]
    fn the_manifest_of_a_fragment_leaves_its_test_table() {
        let setup = |text: &str, form| onsa_tests::case::Setup {
            input: onsa_driver::PackageInput {
                manifest: Some(onsa_driver::ManifestSource { path: "m.onsa".into(), text: text.into(), form }),
                ..Default::default()
            },
            test: Default::default(),
        };
        let text = "[package]\nname = \"a\"\n[targets.t1]\n[test]\nmode = \"check\"\n[[test.fix]]\nat = \"1:1\"\n\
                    [targets.t2]\nkind = \"source\"\n";
        let got = super::fragment_manifest(&setup(text, ManifestForm::Fragment)).unwrap().unwrap();
        let want = "[package]\nname = \"a\"\n[targets.t1]\n[targets.t2]\nkind = \"source\"\n";
        assert_eq!(toml::from_str::<toml::Table>(&got).unwrap(), toml::from_str::<toml::Table>(want).unwrap());
        let alone = setup("[test]\nmode = \"check\"\n", ManifestForm::Fragment);
        assert_eq!(super::fragment_manifest(&alone), Ok(None));
        assert_eq!(super::fragment_manifest(&setup(text, ManifestForm::File)), Ok(None));
    }
}
