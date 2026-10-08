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
    /// Print an internal representation (hidden; `--core` for Core IR, `--cst` for the CST)
    #[command(hide = true)]
    Dump {
        /// Core IR after lowering and monomorphization
        #[arg(long)]
        core: bool,
        /// The CST of one file: the text of its leaves (the source, byte for byte)
        #[arg(long, conflicts_with = "core")]
        cst: bool,
        /// With `--cst`: the tree as indented lines instead of the text
        #[arg(long, requires = "cst")]
        tree: bool,
        /// The levels of the syntax (spec §2.5) of each declaration of one file, a line each
        #[arg(long, conflicts_with_all = ["core", "cst"])]
        levels: bool,
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Run `test` blocks in the interpreter (spec §18.2)
    Test {
        /// Emit JSON
        #[arg(long)]
        json: bool,
        /// Run only the tests whose full name (`dsp.voice "decays"`) contains this text
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
    /// Build a target of the manifest: C sources, headers, and a static library on the host (spec §15.3)
    Build {
        /// Target name from `[targets.<name>]`
        #[arg(long)]
        target: String,
        /// Output directory (default `target/<name>/` next to the manifest)
        #[arg(long)]
        out: Option<PathBuf>,
        /// Package directory or `onsa.toml` (default `.`)
        path: Option<PathBuf>,
    },
    /// Explain a diagnostic code
    Explain {
        /// The code, e.g. `E0811`
        code: String,
    },
}

/// What a command found: the exit code (spec §18.2, S-56). One table for
/// every command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    /// 0: success.
    Ok,
    /// 1: the command worked and found problems (diagnostics, unformatted
    /// files, differences, failed tests).
    Problems,
    /// 2: the command could not work (usage, input and output, `onsa.toml`,
    /// the syntax diagnostics of `fmt` and `diff --ast`).
    CannotWork,
    /// 101: an internal error (S-67): a bug of the compiler.
    Internal,
}

impl Outcome {
    fn code(self) -> u8 {
        match self {
            Outcome::Ok => 0,
            Outcome::Problems => 1,
            Outcome::CannotWork => 2,
            Outcome::Internal => 101,
        }
    }
}

/// Standard output is written through [`write_out`]: a failure to write
/// (a closed pipe) is an input and output error of the command (exit 2), not
/// a panic of the compiler.
macro_rules! out {
    ($($t:tt)*) => { write_out(&format!($($t)*)) };
}

macro_rules! outln {
    ($($t:tt)*) => { write_out(&format!("{}\n", format!($($t)*))) };
}

static STDOUT_ERROR: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

fn write_out(text: &str) {
    use std::io::Write;
    let mut stdout = std::io::stdout().lock();
    if let Err(e) = stdout.write_all(text.as_bytes()).and_then(|()| stdout.flush()) {
        let mut first = STDOUT_ERROR.lock().unwrap_or_else(|p| p.into_inner());
        first.get_or_insert_with(|| e.to_string());
    }
}

fn main() -> ExitCode {
    // The Core verifier runs in debug builds of the CLI only, until W8-02 (R-82).
    onsa_driver::verify_core_in_debug_only();
    let cli = Cli::parse();
    // The command runs on a thread with the stack of the test runner, so both
    // reach the same depth (`onsa_diag::stack`). A panic outside the driver's
    // stages (printing, the file system) is still an internal error (S-67).
    let run = onsa_diag::stack::spawn("onsa", move || onsa_driver::guard(|| run(cli.command)))
        .map_err(|e| format!("cannot start the command: {e}"));
    let outcome = match run.map(|t| t.join()) {
        Ok(Ok(Ok(outcome))) => outcome,
        Ok(Ok(Err(e))) => internal(&SourceMap::default(), &e),
        Ok(Err(_)) => {
            eprintln!("onsa: internal error: the command's thread ended abnormally");
            Outcome::Internal
        }
        Err(e) => {
            eprintln!("onsa: {e}");
            Outcome::CannotWork
        }
    };
    let failed_write = STDOUT_ERROR.lock().unwrap_or_else(|p| p.into_inner()).take();
    let outcome = match failed_write {
        Some(e) if outcome != Outcome::Internal => cannot_work(format!("cannot write to standard output: {e}")),
        _ => outcome,
    };
    ExitCode::from(outcome.code())
}

fn run(command: Command) -> Outcome {
    match command {
        Command::Check { json, paths } => check(json, &paths),
        Command::Fmt { check, paths } => fmt(check, &paths),
        Command::Diff { ast, old, new } => diff(ast, &old, &new),
        Command::Dump { core, cst, tree, levels, paths } => {
            if levels {
                dump_levels(&paths)
            } else if cst {
                dump_cst(tree, &paths)
            } else {
                dump(core, &paths)
            }
        }
        Command::Test { json, filter, paths } => test(json, filter, &paths),
        Command::Interface { json, path } => interface(json, &path),
        Command::Graph { svg, path, flow } => graph(svg, &path, &flow),
        Command::Build { target, out, path } => build(&target, out, path),
        Command::Explain { code } => explain(&code),
    }
}

/// Report an internal error (S-67): standard error only, exit 101.
// Spec §18.2 (S-182): with `--json` too, nothing goes to standard output; the text goes to standard error.
fn internal(sources: &SourceMap, e: &onsa_driver::InternalError) -> Outcome {
    eprint!("onsa: {}", e.render(sources));
    Outcome::Internal
}

fn cannot_work(message: impl std::fmt::Display) -> Outcome {
    eprintln!("onsa: {message}");
    Outcome::CannotWork
}

/// How diagnostics are printed. Every form has the one order of
/// `onsa_diag` (§18.1, S-234).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// The text of `docs/onsa-tools.md` §4.
    Text,
    /// The one JSON object of `--json` (§18.1, S-215).
    Json,
    /// The object of `onsa test --json` when no test ran: the one of
    /// [`Form::Json`] with an empty `tests` array (§18.1, S-233).
    TestJson,
}

impl Form {
    fn json(json: bool) -> Form {
        if json { Form::Json } else { Form::Text }
    }
}

/// The text or the JSON of diagnostics, made inside a guard with the sources,
/// so that a span a stage broke is an internal error naming its file.
fn render(form: Form, sources: &SourceMap, diagnostics: &[onsa_diag::Diagnostic]) -> Result<String, Outcome> {
    onsa_driver::guard(|| match form {
        Form::Text => onsa_diag::to_text(sources, diagnostics),
        Form::Json => format!("{}\n", onsa_diag::to_json(sources, diagnostics)),
        Form::TestJson => format!("{}\n", onsa_driver::TestReport::default().render_json(sources, diagnostics)),
    })
    .map_err(|e| internal(sources, &e))
}

/// Print diagnostics on standard output; `then` is the outcome when they print.
fn print_diagnostics(form: Form, sources: &SourceMap, diagnostics: &[onsa_diag::Diagnostic], then: Outcome) -> Outcome {
    match render(form, sources, diagnostics) {
        Ok(text) => {
            out!("{text}");
            then
        }
        Err(o) => o,
    }
}

/// `onsa fmt [--check] <path...>`: every file is processed, also after one
/// that cannot be read or has a syntax diagnostic; only the files without one
/// are written (`docs/onsa-tools.md` §3.1). On the standard output: `would
/// reformat <path>` for each file `--check` would change, in the order of the
/// files, then the syntax diagnostics of every file at once, in the order of
/// the diagnostics (§4, S-232). The exit code is 2 if a file could not be
/// taken (a syntax diagnostic, a read or a write), else 1 for `--check` with
/// a file to rewrite, else 0. An internal error stops at once.
// SPEC-GAP(S-261): with several files, 2 wins over 1, and the list of the
// files to reformat is a result of the command, on the standard output.
fn fmt(check: bool, paths: &[PathBuf]) -> Outcome {
    let mut changed = false;
    let mut failed = false;
    let mut sources = SourceMap::default();
    let mut report = Vec::new();
    // A file named twice is processed once (its diagnostics are not repeated).
    let mut seen = std::collections::HashSet::new();
    for path in paths {
        if !seen.insert(std::fs::canonicalize(path).unwrap_or_else(|_| path.clone())) {
            continue;
        }
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("onsa: cannot read {}: {e}", path.display());
                failed = true;
                continue;
            }
        };
        let file = sources.add(onsa_driver::slash_path(path), text.clone());
        let out = match onsa_driver::format_file(&sources, file) {
            Ok(onsa_driver::Formatted::Text(out)) => out,
            Ok(onsa_driver::Formatted::Syntax(diagnostics)) => {
                report.extend(diagnostics);
                failed = true;
                continue;
            }
            Err(e) => return internal(&sources, &e),
        };
        if out == text {
            continue;
        }
        changed = true;
        if check {
            outln!("would reformat {}", path.display());
        } else if let Err(e) = std::fs::write(path, out) {
            eprintln!("onsa: cannot write {}: {e}", path.display());
            failed = true;
        }
    }
    let then = if failed {
        Outcome::CannotWork
    } else if check && changed {
        Outcome::Problems
    } else {
        Outcome::Ok
    };
    if report.is_empty() { then } else { print_diagnostics(Form::Text, &sources, &report, then) }
}

fn load(paths: &[PathBuf]) -> Result<onsa_driver::Loaded, Outcome> {
    onsa_driver::load(paths).map_err(cannot_work)
}

fn check(json: bool, paths: &[PathBuf]) -> Outcome {
    let mut loaded = match load(paths) {
        Ok(l) => l,
        Err(o) => return o,
    };
    let result = match onsa_driver::check_loaded(&mut loaded) {
        Ok(r) => r,
        Err(e) => return internal(&loaded.sources, &e),
    };
    let then = if result.diagnostics.is_empty() { Outcome::Ok } else { Outcome::Problems };
    print_diagnostics(Form::json(json), &loaded.sources, &result.diagnostics, then)
}

fn explain(code: &str) -> Outcome {
    let Some(code) = Code::parse(code) else {
        return cannot_work(format!("unknown diagnostic code `{code}`"));
    };
    match code.explain() {
        Some(text) => out!("{text}"),
        None => outln!("# {}: {}\n\n(No long explanation written yet.)", code.as_str(), code.title()),
    }
    Outcome::Ok
}

/// `onsa diff --ast old new`: items added / removed / changed, ignoring trivia (`docs/onsa-tools.md` §3.5).
fn diff(ast: bool, old_path: &PathBuf, new_path: &PathBuf) -> Outcome {
    if !ast {
        return cannot_work("`diff` needs `--ast` (textual diff is what `git diff` is for)");
    }
    let mut sources = SourceMap::default();
    let mut files = Vec::new();
    for path in [old_path, new_path] {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => return cannot_work(format!("cannot read {}: {e}", path.display())),
        };
        // The same file on both sides is one file (its diagnostics once).
        let canonical = |p: &PathBuf| std::fs::canonicalize(p).unwrap_or_else(|_| p.clone());
        if files.len() == 1 && canonical(old_path) == canonical(new_path) {
            files.push(files[0]);
            continue;
        }
        files.push(sources.add(onsa_driver::slash_path(path), text));
    }
    let diffs = match onsa_driver::diff_ast(&sources, files[0], files[1]) {
        Ok(onsa_driver::AstDiff::Items(d)) => d,
        Ok(onsa_driver::AstDiff::Syntax(diagnostics)) => {
            return print_diagnostics(Form::Text, &sources, &diagnostics, Outcome::CannotWork);
        }
        Err(e) => return internal(&sources, &e),
    };
    let line = |span: Option<onsa_diag::Span>| span.map(|s| sources.file(s.file).line_col(s.start).line).unwrap_or(0);
    for d in &diffs {
        use onsa_syntax::diff::Change;
        match d.change {
            Change::Added => outln!("+ {}  (new:{})", d.key, line(d.new)),
            Change::Removed => outln!("- {}  (old:{})", d.key, line(d.old)),
            Change::Changed => {
                outln!("~ {}  (old:{} new:{}; first change at new:{})", d.key, line(d.old), line(d.new), line(d.first))
            }
        }
    }
    if diffs.is_empty() { Outcome::Ok } else { Outcome::Problems }
}

/// Load and analyze one package; print the diagnostics and return the
/// outcome when it does not check.
fn analyzed(form: Form, paths: &[PathBuf]) -> Result<(onsa_driver::Loaded, onsa_driver::Analyzed), Outcome> {
    let mut loaded = load(paths)?;
    let analyzed = match onsa_driver::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => return Err(internal(&loaded.sources, &e)),
    };
    if !analyzed.diagnostics.is_empty() {
        return Err(print_diagnostics(form, &loaded.sources, &analyzed.diagnostics, Outcome::Problems));
    }
    Ok((loaded, analyzed))
}

/// Lower to Core; print the E0200 and return the outcome when it does not lower.
fn lowered(
    form: Form,
    loaded: &onsa_driver::Loaded,
    analyzed: &onsa_driver::Analyzed,
) -> Result<onsa_core::Module, Outcome> {
    match onsa_driver::lower_core(analyzed) {
        Ok(m) => Ok(m),
        Err(onsa_driver::LowerError::Diagnostics(diags)) => {
            Err(print_diagnostics(form, &loaded.sources, &diags, Outcome::Problems))
        }
        Err(onsa_driver::LowerError::Internal(e)) => Err(internal(&loaded.sources, &e)),
    }
}

/// `onsa dump --cst [--tree] <file>`: the CST of one file (R-86). Exit 0
/// also when the file has syntax errors (the CST is complete); the syntax
/// diagnostics are not printed.
fn dump_cst(tree: bool, paths: &[PathBuf]) -> Outcome {
    let [path] = paths else {
        return cannot_work("`dump --cst` takes one file");
    };
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => return cannot_work(format!("cannot read {}: {e}", path.display())),
    };
    let mut sources = SourceMap::default();
    let file = sources.add(onsa_driver::slash_path(path), text);
    match onsa_driver::cst_dump(&sources, file, tree) {
        Ok(out) => {
            out!("{out}");
            Outcome::Ok
        }
        Err(e) => internal(&sources, &e),
    }
}

/// `onsa dump --levels`: the levels of each declaration of one file (the fmt properties).
fn dump_levels(paths: &[PathBuf]) -> Outcome {
    let [path] = paths else {
        return cannot_work("`dump --levels` takes one file");
    };
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => return cannot_work(format!("cannot read {}: {e}", path.display())),
    };
    let mut sources = SourceMap::default();
    let file = sources.add(path.to_string_lossy(), text);
    match onsa_driver::levels_dump(&sources, file) {
        Ok(out) => {
            out!("{out}");
            Outcome::Ok
        }
        Err(e) => internal(&sources, &e),
    }
}

/// `onsa dump --core`: the Core IR of a package (after `check` passes).
fn dump(core: bool, paths: &[PathBuf]) -> Outcome {
    if !core {
        return cannot_work("`dump` needs `--core`");
    }
    let (loaded, analyzed) = match analyzed(Form::Text, paths) {
        Ok(x) => x,
        Err(o) => return o,
    };
    match lowered(Form::Text, &loaded, &analyzed) {
        Ok(module) => {
            out!("{}", onsa_core::dump(&module));
            Outcome::Ok
        }
        Err(o) => o,
    }
}

/// `onsa interface <path> [--json]` (T3-11). With `--json`, diagnostics are
/// the document of `check --json` (§18.1).
fn interface(json: bool, path: &PathBuf) -> Outcome {
    let (loaded, analyzed) = match analyzed(Form::json(json), std::slice::from_ref(path)) {
        Ok(x) => x,
        Err(o) => return o,
    };
    let iface = match onsa_driver::interface(&analyzed) {
        Ok(i) => i,
        Err(e) => return internal(&loaded.sources, &e),
    };
    if json {
        outln!("{}", onsa_driver::render_json(&iface));
    } else {
        out!("{}", onsa_driver::render_text(&iface));
    }
    Outcome::Ok
}

/// `onsa graph <path> <flow> [--svg]` (T3-12).
fn graph(svg: bool, path: &PathBuf, flow: &str) -> Outcome {
    let (loaded, analyzed) = match analyzed(Form::Text, std::slice::from_ref(path)) {
        Ok(x) => x,
        Err(o) => return o,
    };
    let dot = match onsa_driver::graph(&analyzed, flow) {
        Ok(d) => d,
        Err(onsa_driver::GraphError::Usage(e)) => return cannot_work(e),
        Err(onsa_driver::GraphError::Internal(e)) => return internal(&loaded.sources, &e),
    };
    if svg {
        match onsa_driver::graph::to_svg(&dot) {
            Ok(s) => out!("{s}"),
            Err(e) => return cannot_work(e),
        }
    } else {
        out!("{dot}");
    }
    Outcome::Ok
}

/// `onsa test <paths> [--json] [--filter <text>]` (T3-8, §18.2): check, lower,
/// match `--filter`, run the selected tests. The checks and the E0200 of
/// lowering stop the run before the filter is matched; a filter that selects
/// no test is a usage error (exit 2, nothing on the standard output).
fn test(json: bool, filter: Option<String>, paths: &[PathBuf]) -> Outcome {
    let form = if json { Form::TestJson } else { Form::Text };
    let (loaded, analyzed) = match analyzed(form, paths) {
        Ok(x) => x,
        Err(o) => return o,
    };
    let module = match lowered(form, &loaded, &analyzed) {
        Ok(m) => m,
        Err(o) => return o,
    };
    let opts = onsa_driver::TestOptions { filter };
    let report = match onsa_driver::run_tests(&loaded.sources, &module, &opts) {
        Ok(onsa_driver::TestRun::Ran(r)) => r,
        Ok(onsa_driver::TestRun::NoMatch) => {
            let filter = opts.filter.as_deref().unwrap_or_default();
            return cannot_work(format!("`--filter {filter:?}` matches no test"));
        }
        // E0200, as those of lowering: no test ran (S-224).
        Ok(onsa_driver::TestRun::Unsupported(diags)) => {
            return print_diagnostics(form, &loaded.sources, &diags, Outcome::Problems);
        }
        Err(e) => return internal(&loaded.sources, &e),
    };
    // Inside a guard with the sources, as the diagnostics: a span a stage
    // broke is an internal error naming its file.
    let text = onsa_driver::guard(|| {
        if json {
            format!("{}\n", report.render_json(&loaded.sources, &[]))
        } else {
            report.render_text(&loaded.sources)
        }
    });
    match text {
        Ok(text) => out!("{text}"),
        Err(e) => return internal(&loaded.sources, &e),
    }
    if report.failed() == 0 { Outcome::Ok } else { Outcome::Problems }
}

/// `onsa build --target <name> [--out <dir>] [path]` (T4-5).
fn build(target: &str, out: Option<PathBuf>, path: Option<PathBuf>) -> Outcome {
    let path = path.unwrap_or_else(|| PathBuf::from("."));
    let opts = onsa_driver::BuildOptions { target: target.to_string(), out };
    match onsa_driver::build(&path, &opts) {
        Ok(r) => {
            outln!("built `{}` for {} ({}) in {}", r.target, r.platform, r.kind, r.out_dir.display());
            for f in &r.files {
                outln!("  {f}");
            }
            if let Some(n) = &r.note {
                outln!("note: {n}");
            }
            Outcome::Ok
        }
        Err(onsa_driver::BuildError::Usage(m)) => cannot_work(m),
        Err(onsa_driver::BuildError::Diagnostics { sources, diagnostics }) => {
            print_diagnostics(Form::Text, &sources, &diagnostics, Outcome::Problems)
        }
        Err(onsa_driver::BuildError::Internal { sources, error }) => internal(&sources, &error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exit_codes_of_spec_18_2() {
        let codes: Vec<u8> =
            [Outcome::Ok, Outcome::Problems, Outcome::CannotWork, Outcome::Internal].iter().map(|o| o.code()).collect();
        assert_eq!(codes, [0, 1, 2, 101]);
    }
}
