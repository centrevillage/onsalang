//! The `onsa` command (spec §18.2). M0: `check` and `explain`.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use onsa_diag::{Code, SourceMap};

#[derive(Parser)]
#[command(name = "onsa", version, about = "Onsa compiler")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check types, effects, rt, flow and policy
    Check {
        /// Print diagnostics as JSON (spec §18.1)
        #[arg(long)]
        json: bool,
        /// `.onsa` files to check (a single package)
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Explain a diagnostic code
    Explain {
        /// The code, e.g. `E0811`
        code: String,
    },
}

/// Exit codes: 0 no diagnostics, 1 diagnostics reported, 2 usage or I/O error.
fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Command::Check { json, paths } => check(json, &paths),
        Command::Explain { code } => explain(&code),
    }
}

fn check(json: bool, paths: &[PathBuf]) -> ExitCode {
    let mut sources = SourceMap::default();
    for path in paths {
        match std::fs::read_to_string(path) {
            Ok(text) => {
                sources.add(path.to_string_lossy(), text);
            }
            Err(e) => {
                eprintln!("onsa: cannot read {}: {e}", path.display());
                return ExitCode::from(2);
            }
        }
    }
    let result = onsa_driver::check(&sources);
    if json {
        println!("{}", onsa_diag::to_json(&sources, &result.diagnostics));
    } else {
        print!("{}", onsa_diag::to_text(&sources, &result.diagnostics));
    }
    if result.diagnostics.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) }
}

fn explain(code: &str) -> ExitCode {
    let Some(code) = Code::parse(code) else {
        eprintln!("onsa: unknown diagnostic code `{code}`");
        return ExitCode::from(2);
    };
    match code.explain() {
        Some(text) => print!("{text}"),
        None => println!("# {}: {}\n\n(No long explanation written yet.)", code.as_str(), code.title()),
    }
    ExitCode::SUCCESS
}
