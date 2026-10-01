//! The `onsa` command (spec §18.2). M0: `check` and `explain`; M1: `fmt`.

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
    /// Normalize files to the canonical form (spec §18.2)
    Fmt {
        /// Do not write; exit 1 if any file would change
        #[arg(long)]
        check: bool,
        /// `.onsa` files to format
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Structural difference between two files (`--ast`)
    Diff {
        /// Compare syntax trees (the only mode for now)
        #[arg(long)]
        ast: bool,
        old: PathBuf,
        new: PathBuf,
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
        Command::Fmt { check, paths } => fmt(check, &paths),
        Command::Diff { ast, old, new } => diff(ast, &old, &new),
        Command::Explain { code } => explain(&code),
    }
}

fn fmt(check: bool, paths: &[PathBuf]) -> ExitCode {
    let mut changed = false;
    for path in paths {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("onsa: cannot read {}: {e}", path.display());
                return ExitCode::from(2);
            }
        };
        let mut sources = SourceMap::default();
        let file = sources.add(path.to_string_lossy(), text.clone());
        let parsed = onsa_syntax::parse(file, &text);
        let Some(out) = onsa_syntax::format(&parsed, &text) else {
            eprint!("{}", onsa_diag::to_text(&sources, &parsed.diagnostics));
            return ExitCode::from(2);
        };
        if out == text {
            continue;
        }
        changed = true;
        if check {
            println!("would reformat {}", path.display());
        } else if let Err(e) = std::fs::write(path, out) {
            eprintln!("onsa: cannot write {}: {e}", path.display());
            return ExitCode::from(2);
        }
    }
    if check && changed { ExitCode::from(1) } else { ExitCode::SUCCESS }
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

/// `onsa diff --ast old new`: items added / removed / changed, ignoring trivia (spec §18.2).
fn diff(ast: bool, old_path: &PathBuf, new_path: &PathBuf) -> ExitCode {
    if !ast {
        eprintln!("onsa: `diff` needs `--ast` (textual diff is what `git diff` is for)");
        return ExitCode::from(2);
    }
    let mut sources = SourceMap::default();
    let mut parsed = Vec::new();
    for path in [old_path, new_path] {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("onsa: cannot read {}: {e}", path.display());
                return ExitCode::from(2);
            }
        };
        let file = sources.add(path.to_string_lossy(), text.clone());
        let p = onsa_syntax::parse(file, &text);
        if p.diagnostics.iter().any(|d| d.code.number() <= 20) {
            print!("{}", onsa_diag::to_text(&sources, &p.diagnostics));
            return ExitCode::from(2);
        }
        parsed.push(p);
    }
    let diffs = onsa_syntax::diff::diff(&parsed[0], &parsed[1]);
    let line = |span: Option<onsa_diag::Span>| span.map(|s| sources.file(s.file).line_col(s.start).line).unwrap_or(0);
    for d in &diffs {
        use onsa_syntax::diff::Change;
        match d.change {
            Change::Added => println!("+ {}  (new:{})", d.key, line(d.new)),
            Change::Removed => println!("- {}  (old:{})", d.key, line(d.old)),
            Change::Changed => println!(
                "~ {}  (old:{} new:{}; first change at new:{})",
                d.key,
                line(d.old),
                line(d.new),
                line(d.first)
            ),
        }
    }
    if diffs.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) }
}
