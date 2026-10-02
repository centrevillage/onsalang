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
        /// `.onsa` files (one package), or a package directory / `onsa.toml`
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
    /// Print an internal representation (hidden; `--core` for Core IR)
    #[command(hide = true)]
    Dump {
        /// Core IR after lowering and monomorphization
        #[arg(long)]
        core: bool,
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Run `test` blocks in the interpreter (spec §18.2)
    Test {
        /// Emit JSON
        #[arg(long)]
        json: bool,
        /// Run only tests whose name contains this text
        #[arg(long)]
        filter: Option<String>,
        /// `.onsa` files (one package), or a package directory / `onsa.toml`
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Public signatures, kinds, sizes, @param and flow APIs (spec §18.2)
    Interface {
        /// Emit JSON
        #[arg(long)]
        json: bool,
        /// `.onsa` file, package directory, or `onsa.toml`
        path: PathBuf,
    },
    /// Signal graph of a flow as DOT (spec §18.2)
    Graph {
        /// Render to SVG with Graphviz `dot`
        #[arg(long)]
        svg: bool,
        /// `.onsa` file, package directory, or `onsa.toml`
        path: PathBuf,
        /// Flow name (`voice` or `dsp.voice`)
        flow: String,
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
        Command::Dump { core, paths } => dump(core, &paths),
        Command::Test { json, filter, paths } => test(json, filter, &paths),
        Command::Interface { json, path } => interface(json, &path),
        Command::Graph { svg, path, flow } => graph(svg, &path, &flow),
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
    let mut loaded = match onsa_driver::load(paths) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("onsa: {e}");
            return ExitCode::from(2);
        }
    };
    let result = onsa_driver::check_loaded(&mut loaded);
    if json {
        println!("{}", onsa_diag::to_json(&loaded.sources, &result.diagnostics));
    } else {
        print!("{}", onsa_diag::to_text(&loaded.sources, &result.diagnostics));
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

/// `onsa dump --core`: the Core IR of a package (after `check` passes).
fn dump(core: bool, paths: &[PathBuf]) -> ExitCode {
    if !core {
        eprintln!("onsa: `dump` needs `--core`");
        return ExitCode::from(2);
    }
    let mut loaded = match onsa_driver::load(paths) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("onsa: {e}");
            return ExitCode::from(2);
        }
    };
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    if !analyzed.diagnostics.is_empty() {
        print!("{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        return ExitCode::from(1);
    }
    match onsa_driver::lower_core(&analyzed) {
        Ok(module) => {
            print!("{}", onsa_core::dump(&module));
            ExitCode::SUCCESS
        }
        Err(diags) => {
            print!("{}", onsa_diag::to_text(&loaded.sources, &diags));
            ExitCode::from(1)
        }
    }
}

/// Load and analyze one package; print diagnostics and return `None` when it does not check.
fn analyzed_or_exit(path: &PathBuf) -> Result<(onsa_driver::Loaded, onsa_driver::Analyzed), ExitCode> {
    let mut loaded = match onsa_driver::load(std::slice::from_ref(path)) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("onsa: {e}");
            return Err(ExitCode::from(2));
        }
    };
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    if !analyzed.diagnostics.is_empty() {
        print!("{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        return Err(ExitCode::from(1));
    }
    Ok((loaded, analyzed))
}

/// `onsa interface <path> [--json]` (T3-11).
fn interface(json: bool, path: &PathBuf) -> ExitCode {
    let (_loaded, analyzed) = match analyzed_or_exit(path) {
        Ok(x) => x,
        Err(code) => return code,
    };
    let iface = onsa_driver::interface(&analyzed);
    if json {
        println!("{}", onsa_driver::render_json(&iface));
    } else {
        print!("{}", onsa_driver::render_text(&iface));
    }
    ExitCode::SUCCESS
}

/// `onsa graph <path> <flow> [--svg]` (T3-12).
fn graph(svg: bool, path: &PathBuf, flow: &str) -> ExitCode {
    let (_loaded, analyzed) = match analyzed_or_exit(path) {
        Ok(x) => x,
        Err(code) => return code,
    };
    let dot = match onsa_driver::graph(&analyzed, flow) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("onsa: {e}");
            return ExitCode::from(2);
        }
    };
    if svg {
        match onsa_driver::graph::to_svg(&dot) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("onsa: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        print!("{dot}");
    }
    ExitCode::SUCCESS
}

/// `onsa test <paths> [--json] [--filter <text>]` (T3-8): check, lower, run every `test`.
fn test(json: bool, filter: Option<String>, paths: &[PathBuf]) -> ExitCode {
    let mut loaded = match onsa_driver::load(paths) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("onsa: {e}");
            return ExitCode::from(2);
        }
    };
    let analyzed = onsa_driver::analyze_loaded(&mut loaded);
    if !analyzed.diagnostics.is_empty() {
        if json {
            println!("{}", onsa_diag::to_json(&loaded.sources, &analyzed.diagnostics));
        } else {
            print!("{}", onsa_diag::to_text(&loaded.sources, &analyzed.diagnostics));
        }
        return ExitCode::from(1);
    }
    let module = match onsa_driver::lower_core(&analyzed) {
        Ok(m) => m,
        Err(diags) => {
            if json {
                println!("{}", onsa_diag::to_json(&loaded.sources, &diags));
            } else {
                print!("{}", onsa_diag::to_text(&loaded.sources, &diags));
            }
            return ExitCode::from(1);
        }
    };
    let report = onsa_driver::run_tests(&module, &onsa_driver::TestOptions { filter });
    if json {
        println!("{}", report.render_json(&loaded.sources));
    } else {
        print!("{}", report.render_text(&loaded.sources));
    }
    if report.failed() == 0 { ExitCode::SUCCESS } else { ExitCode::from(1) }
}
