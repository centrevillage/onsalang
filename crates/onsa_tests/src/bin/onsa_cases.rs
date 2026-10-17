//! `onsa_cases`: what the test runner and the compiler hold, as JSON, for the
//! gate's tools. Each list is read with the same code as the test runner and
//! the compiler, so the tools never parse Rust or Onsa source themselves.
//!
//! ```text
//! onsa_cases [ROOT]          the cases under tests/ and their settings (tools/spec_sections.py)
//! onsa_cases --run [ROOT]    run every case; the markers each compared (tools/diag_codes.py, K-13)
//! onsa_cases --c ITEM [ROOT] a gate item of the C checks (Q-07, W1-06; `onsa_tests::ccheck`)
//! onsa_cases --c-items       the names of those items (tools/test_gate.py matches them with the gate's)
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
//! onsa_cases --fix-loop [--json] [--branches] [--pick first|last] [--steps N] [--states N] [--diverge N] FILE...
//!                            the fix candidates applied again and again until the loop stops
//!                            (S-236, rules/criteria.md 7.27, W3-22; `onsa_tests::fix_loop`)
//! onsa_cases --fix-loop-gate [ROOT]  the gate item fix-loop (`onsa_tests::fix_loop::gate`)
//! ```
//!
//! The first form prints:
//!
//! ```text
//! [{"path": "tests/spec/fn/mean.onsa", "kind": "file", "name": "mean",
//!   "mode": "check", "spec": ["§6.1"], "golden": [], "golden_graph": [],
//!   "conformance": false, "targets": [],
//!   "files": [{"path": "tests/spec/fn/mean.onsa", "syntax_errors": false}]}, ...]
//! ```
//!
//! `files` are the source files of the case (from the repository root), and
//! whether the lexer or the parser reports a diagnostic on each
//! (`onsa_syntax::Parsed::syntax_errors`, the one place `fmt` decides to
//! refuse a file; `tools/fmt_props.py` reads it, W3-02/b 5).
//!
//! `--run` prints the form of `onsa_tests::run::runs_json`. Exits 1 when a
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
//! `--fix-loop-gate` is the gate item `fix-loop` over ROOT (default: the
//! repository; `onsa_tests::fix_loop::gate`). Exits 1 when it fails to walk
//! what it says, never on what the walks find.

use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "onsa_cases [--run] [ROOT] | --c ITEM [ROOT] | --vectors interp|c [ROOT] | --c-items | --codes | --keywords | --continuing | --symbols | \
     --std-names | --builtin-members | --fix-same-place FILE... | --default-inits FILE... | --fix-loop [--json] [--branches] [--pick first|last] \
     [--steps N] [--states N] [--diverge N] FILE... | --fix-loop-gate [ROOT]";

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
    let too_many = match mode {
        "" | "--run" | "--fix-loop-gate" => rest.len() > 1,
        "--c" | "--vectors" => rest.is_empty() || rest.len() > 2,
        "--fix-same-place" | "--fix-loop" | "--default-inits" => rest.is_empty(),
        _ => !rest.is_empty(),
    };
    if too_many {
        eprintln!("usage: {USAGE}");
        return ExitCode::from(2);
    }
    match mode {
        "" => cases(&root()),
        "--run" => {
            let root = root();
            let (cases, errors) = onsa_tests::case::collect(&root);
            let runs = onsa_tests::run::run_each(
                &root,
                &cases,
                |_| onsa_tests::golden::Update::Off,
                onsa_tests::run::HostSteps::Skip,
            );
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
            print(&serde_json::json!(fix_same_place(rest)));
            ExitCode::SUCCESS
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
                eprintln!("{e}; usage: {USAGE}");
                ExitCode::from(2)
            }
        },
        "--fix-loop-gate" => {
            let g = onsa_tests::fix_loop::gate(&root(), onsa_tests::fix_loop::GATE_BUDGET);
            println!("{}", g.text);
            if g.failed { ExitCode::FAILURE } else { ExitCode::SUCCESS }
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
            eprintln!("unknown option `{other}`; usage: {USAGE}");
            ExitCode::from(2)
        }
    }
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

/// `--fix-same-place`: each file on a thread with the stack of a command, in parallel.
fn fix_same_place(files: &[String]) -> Vec<serde_json::Value> {
    onsa_tests::single_files::on_stacks(files.len(), |i| {
        let path = &files[i];
        match onsa_tests::single_files::read_input(path) {
            Err(e) => serde_json::json!({"file": path, "unreadable": e}),
            // A panic outside the driver's stages is an internal error too.
            Ok(text) => match onsa_driver::guard(|| onsa_tests::fix_contract::same_place(&text)) {
                Ok(r) => {
                    let mut v = serde_json::json!(r);
                    v["file"] = serde_json::json!(path);
                    v
                }
                Err(e) => serde_json::json!({"file": path, "candidates": 0, "violations": [], "internal": e.message}),
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
        match &c.setup {
            Ok(s) => items.push(serde_json::json!({
                "path": c.path,
                "kind": c.kind,
                "name": c.name,
                "mode": s.test.mode,
                "spec": s.test.spec,
                "golden": s.test.golden,
                "golden_graph": s.test.golden_graph,
                "conformance": s.test.conformance,
                "targets": s.targets(),
                "files": files(&c, s),
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
