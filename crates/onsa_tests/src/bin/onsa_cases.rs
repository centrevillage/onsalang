//! `onsa_cases`: what the test runner and the compiler hold, as JSON, for the
//! gate's tools. Each list is read with the same code as the test runner and
//! the compiler, so the tools never parse Rust or Onsa source themselves.
//!
//! ```text
//! onsa_cases [ROOT]          the cases under tests/ and their settings (tools/spec_sections.py)
//! onsa_cases --run [ROOT]    run every case; the markers each compared (tools/diag_codes.py, K-13)
//! onsa_cases --c ITEM [ROOT] a gate item of the C checks (Q-07, W1-06; `onsa_tests::ccheck`)
//! onsa_cases --c-items       the names of those items (tools/test_gate.py matches them with the gate's)
//! onsa_cases --codes         the registry of diagnostic codes (tools/diag_codes.py, S-109)
//! onsa_cases --std-names     the names the embedded std declares (tools/builtin_names.py, Q-14)
//! onsa_cases --builtin-members  the builtin methods and associated items of sema's table (the same)
//! ```
//!
//! The first form prints:
//!
//! ```text
//! [{"path": "tests/spec/fn/mean.onsa", "kind": "file", "name": "mean",
//!   "mode": "check", "spec": ["§6.1"], "golden": [], "golden_graph": [],
//!   "conformance": false, "targets": []}, ...]
//! ```
//!
//! `--run` prints the form of `onsa_tests::run::runs_json`. Exits 1 when a
//! case or a std module cannot be read (`--run` reports those in its
//! `errors` and in the runs instead, and exits 0), 2 on a usage error.
//!
//! `--c ITEM` prints a line per case of the item and exits 1 when the item
//! fails after `tests/pending.toml` is applied, 2 when it cannot run (a
//! compiler is missing; `onsa_tests::ccheck`).

use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str =
    "onsa_cases [--run] [ROOT] | --c ITEM [ROOT] | --c-items | --codes | --std-names | --builtin-members";

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
        "" | "--run" => rest.len() > 1,
        "--c" => rest.is_empty() || rest.len() > 2,
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
            let runs = onsa_tests::run::run_each(&root, &cases, |_| false);
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
        "--c-items" => {
            print(&serde_json::json!(onsa_tests::c::ITEMS.iter().map(|i| i.name).collect::<Vec<_>>()));
            ExitCode::SUCCESS
        }
        "--codes" => {
            print(&onsa_tests::inventory::codes());
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
