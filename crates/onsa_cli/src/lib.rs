//! The commands of `onsa` (spec §18.2). M0: `check` and `explain`; M1: `fmt`.
//!
//! The binary (`src/bin/onsa.rs`) reads its arguments ([`Cli`]) and runs
//! [`run_command`] on the file system ([`Disk`]), the standard output and the
//! standard error. `onsa_cases --serve` runs the same function on texts and
//! buffers (W4-18 U10c, X-16, X-20), so the gate's tools see what the
//! command prints without a file and a process for each input.

use std::io::Write;
use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand};
use onsa_diag::{Code, Diagnostic, SourceMap, Stage};

/// What `onsa --version` shows after `onsa `: the compiler's version and, on
/// its own line, the embedded std's: two lines, `onsa <version>` and
/// `std <version>` (spec §15.3, §18.2, S-160, S-626).
static VERSION: std::sync::LazyLock<String> =
    std::sync::LazyLock::new(|| format!("{}\nstd {}", env!("CARGO_PKG_VERSION"), onsa_driver::STD_VERSION));

#[derive(Parser)]
#[command(name = "onsa", version = VERSION.as_str(), about = "Onsa compiler")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

/// The path of a command that reads a package (§15.1, §18.2, S-323): the
/// last argument, which may be omitted. One place for its form; the count
/// is [`one_path`]'s, so that two paths are refused in the words of §15.1.
#[derive(clap::Args)]
pub struct PackagePath {
    /// One path: a `.onsa` file, a package directory or `onsa.toml` (the
    /// package above the working directory when omitted, §15.1)
    #[arg(value_name = "PATH")]
    paths: Vec<PathBuf>,
}

#[derive(Subcommand)]
pub enum Command {
    /// Check types, effects, rt, flow and policy
    Check {
        /// Print diagnostics as JSON (spec §18.1)
        #[arg(long)]
        json: bool,
        #[command(flatten)]
        path: PackagePath,
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
        /// `--core`: the path of a package, as `check` takes it; `--cst` and `--levels`: one file
        #[arg(value_name = "PATH")]
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
        #[command(flatten)]
        path: PackagePath,
    },
    /// Public signatures, kinds, sizes, @param and flow APIs (spec §18.2)
    Interface {
        /// Emit JSON
        #[arg(long)]
        json: bool,
        #[command(flatten)]
        path: PackagePath,
    },
    /// Signal graph of a flow as DOT (spec §18.2)
    Graph {
        /// Render to SVG with Graphviz `dot`
        #[arg(long)]
        svg: bool,
        /// Flow name (`voice` or `dsp.voice`)
        flow: String,
        #[command(flatten)]
        path: PackagePath,
    },
    /// Build a target of the manifest: C sources, headers, and a static library on the host (spec §15.3)
    Build {
        /// Target name from `[targets.<name>]`
        #[arg(long)]
        target: String,
        /// Output directory (default `target/<name>/` next to the manifest)
        #[arg(long)]
        out: Option<PathBuf>,
        /// One path: a package directory or `onsa.toml` (the package above
        /// the working directory when omitted, §15.1); not a file
        #[arg(value_name = "PATH")]
        paths: Vec<PathBuf>,
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
    /// The outcome of the diagnostics a command reports (§18.2): one that
    /// points into `onsa.toml` (`Stage::Manifest`) is 2, the others 1.
    fn of(diagnostics: &[Diagnostic]) -> Outcome {
        if diagnostics.iter().any(|d| d.stage == Stage::Manifest) {
            Outcome::CannotWork
        } else if diagnostics.is_empty() {
            Outcome::Ok
        } else {
            Outcome::Problems
        }
    }

    fn code(self) -> u8 {
        match self {
            Outcome::Ok => 0,
            Outcome::Problems => 1,
            Outcome::CannotWork => 2,
            Outcome::Internal => 101,
        }
    }
}

/// Standard output is written through [`Io::out`]: a failure to write
/// (a closed pipe) is an input and output error of the command (exit 2), not
/// a panic of the compiler.
macro_rules! out {
    ($io:expr, $($t:tt)*) => { $io.out(&format!($($t)*)) };
}

macro_rules! outln {
    ($io:expr, $($t:tt)*) => { $io.out(&format!("{}\n", format!($($t)*))) };
}

/// Standard error, as `eprintln!` writes it ([`Io::err`]).
macro_rules! errln {
    ($io:expr, $($t:tt)*) => { $io.err(&format!("{}\n", format!($($t)*))) };
}

/// Where a command reads its files and writes its outputs: for `onsa`, the
/// file system and the standard output and error; for `onsa_cases --serve`,
/// texts and buffers.
pub struct Io<'a> {
    out: &'a mut (dyn Write + Send),
    err: &'a mut (dyn Write + Send),
    files: &'a (dyn Files + Sync),
    /// The first failure to write to the standard output: the command goes
    /// on, and ends in 2 unless it ends in an internal error.
    out_error: Option<String>,
}

impl<'a> Io<'a> {
    pub fn new(
        out: &'a mut (dyn Write + Send),
        err: &'a mut (dyn Write + Send),
        files: &'a (dyn Files + Sync),
    ) -> Io<'a> {
        Io { out, err, files, out_error: None }
    }

    /// Write and flush `text` to the standard output; the first failure is kept.
    fn out(&mut self, text: &str) {
        if let Err(e) = self.out.write_all(text.as_bytes()).and_then(|()| self.out.flush()) {
            self.out_error.get_or_insert_with(|| e.to_string());
        }
    }

    /// Write `text` to the standard error; a failure panics with the message of `eprint!`.
    fn err(&mut self, text: &str) {
        if let Err(e) = self.err.write_all(text.as_bytes()) {
            panic!("failed printing to stderr: {e}");
        }
    }
}

/// The files the commands read (and `fmt` replaces), but those of `build`,
/// which the driver reads itself.
pub trait Files {
    /// The text of the file `path`, as `std::fs::read_to_string` reads it.
    fn read(&self, path: &Path) -> std::io::Result<String>;
    /// The name of the file `path` that two paths of one file share
    /// (`std::fs::canonicalize`, or `path` when it cannot be had).
    fn canonical(&self, path: &Path) -> PathBuf;
    /// The package of the one path of a command (`onsa_driver::load`).
    fn load(&self, path: Option<&Path>) -> Result<onsa_driver::Loaded, String>;
    /// Write `text` as the new text of the file `path` (`fmt`).
    fn replace(&self, path: &Path, text: &str) -> std::io::Result<()>;
}

/// The file system: the files of `onsa`.
pub struct Disk;

impl Files for Disk {
    fn read(&self, path: &Path) -> std::io::Result<String> {
        std::fs::read_to_string(path)
    }

    fn canonical(&self, path: &Path) -> PathBuf {
        std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
    }

    fn load(&self, path: Option<&Path>) -> Result<onsa_driver::Loaded, String> {
        onsa_driver::load(path)
    }

    fn replace(&self, path: &Path, text: &str) -> std::io::Result<()> {
        write_replacing(path, text)
    }
}

/// Run `command` and return its exit code (spec §18.2). The command runs on a
/// thread with the stack of the test runner, so both reach the same depth
/// (`onsa_diag::stack`). A panic outside the driver's stages (printing, the
/// file system) is still an internal error (S-67).
pub fn run_command(command: Command, io: &mut Io<'_>) -> u8 {
    let joined = std::thread::scope(|s| {
        onsa_diag::stack::spawn_scoped(s, "onsa", || onsa_driver::guard(|| run(command, io))).map(|t| t.join())
    });
    let outcome = match joined {
        Ok(Ok(Ok(outcome))) => outcome,
        Ok(Ok(Err(e))) => internal(io, &SourceMap::default(), &e),
        Ok(Err(_)) => {
            errln!(io, "onsa: internal error: the command's thread ended abnormally");
            Outcome::Internal
        }
        Err(e) => cannot_work(io, format!("cannot start the command: {e}")),
    };
    let outcome = match io.out_error.take() {
        Some(e) if outcome != Outcome::Internal => cannot_work(io, format!("cannot write to standard output: {e}")),
        _ => outcome,
    };
    outcome.code()
}

/// What a command ends with: its outcome, also the one it stops at early
/// (`Err`, which `?` passes up).
type Done = Result<Outcome, Outcome>;

fn run(command: Command, io: &mut Io<'_>) -> Outcome {
    let done = match command {
        Command::Check { json, path } => check(io, json, &path.paths),
        Command::Fmt { check, paths } => Ok(fmt(io, check, &paths)),
        Command::Diff { ast, old, new } => Ok(diff(io, ast, &old, &new)),
        Command::Dump { core, cst, tree, levels, paths } => {
            if levels {
                dump_levels(io, &paths)
            } else if cst {
                dump_cst(io, tree, &paths)
            } else {
                dump(io, core, &paths)
            }
        }
        Command::Test { json, filter, path } => test(io, json, filter, &path.paths),
        Command::Interface { json, path } => interface(io, json, &path.paths),
        Command::Graph { svg, flow, path } => graph(io, svg, &flow, &path.paths),
        Command::Build { target, out, paths } => build(io, &target, out, &paths),
        Command::Explain { code } => Ok(explain(io, &code)),
    };
    done.unwrap_or_else(|o| o)
}

/// Report an internal error (S-67): standard error only, exit 101.
// Spec §18.2 (S-182): with `--json` too, nothing goes to standard output; the text goes to standard error.
fn internal(io: &mut Io<'_>, sources: &SourceMap, e: &onsa_driver::InternalError) -> Outcome {
    io.err(&format!("onsa: {}", e.render(sources)));
    Outcome::Internal
}

fn cannot_work(io: &mut Io<'_>, message: impl std::fmt::Display) -> Outcome {
    errln!(io, "onsa: {message}");
    Outcome::CannotWork
}

/// How diagnostics are printed. Every form has the one order of
/// `onsa_diag` (§18.1, S-234).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// The text of `spec/tools.md` §4.
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
fn render(
    io: &mut Io<'_>,
    form: Form,
    sources: &SourceMap,
    diagnostics: &[onsa_diag::Diagnostic],
) -> Result<String, Outcome> {
    onsa_driver::guard(|| match form {
        Form::Text => onsa_diag::to_text(sources, diagnostics),
        Form::Json => format!("{}\n", onsa_diag::to_json(sources, diagnostics)),
        Form::TestJson => format!("{}\n", onsa_driver::TestReport::default().render_json(sources, diagnostics)),
    })
    .map_err(|e| internal(io, sources, &e))
}

/// Print diagnostics on standard output; `then` is the outcome when they print.
fn print_diagnostics(
    io: &mut Io<'_>,
    form: Form,
    sources: &SourceMap,
    diagnostics: &[onsa_diag::Diagnostic],
    then: Outcome,
) -> Outcome {
    match render(io, form, sources, diagnostics) {
        Ok(text) => {
            out!(io, "{text}");
            then
        }
        Err(o) => o,
    }
}

/// The line of `onsa fmt` for the file `path` it cannot read, which names a
/// directory as one, also when the error is another (a directory that may
/// not be read): fmt takes files (`spec/tools.md` §3.1, S-599).
pub fn fmt_cannot_read(path: &Path, e: &std::io::Error) -> String {
    let directory = std::fs::metadata(path).is_ok_and(|m| m.is_dir());
    if directory || e.kind() == std::io::ErrorKind::IsADirectory {
        format!("onsa: {} is a directory; onsa fmt takes files", path.display())
    } else {
        format!("onsa: cannot read {}: {e}", path.display())
    }
}

/// `onsa fmt [--check] <path...>`: every file is processed, also after one
/// that cannot be read or has a syntax diagnostic; only the files without one
/// are written (`spec/tools.md` §3.1). On the standard output: `would
/// reformat <path>` for each file `--check` would change, in the order of the
/// files, then the syntax diagnostics of every file at once, in the order of
/// the diagnostics (§4, S-232). The exit code is 2 if a file could not be
/// taken (a syntax diagnostic, a read or a write), else 1 for `--check` with
/// a file to rewrite, else 0. An internal error stops at once.
// SPEC-GAP(S-261): with several files, 2 wins over 1, and the list of the
// files to reformat is a result of the command, on the standard output.
fn fmt(io: &mut Io<'_>, check: bool, paths: &[PathBuf]) -> Outcome {
    let mut changed = false;
    let mut failed = false;
    let mut sources = SourceMap::default();
    let mut report = Vec::new();
    // A file named twice is processed once (its diagnostics are not repeated).
    let mut seen = std::collections::HashSet::new();
    for path in paths {
        if !seen.insert(io.files.canonical(path)) {
            continue;
        }
        let text = match io.files.read(path) {
            Ok(t) => t,
            Err(e) => {
                errln!(io, "{}", fmt_cannot_read(path, &e));
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
            // An internal error (the check before writing failed, §3.5) stops
            // at once: the files before it stay written, the files after it
            // are not taken, and the syntax diagnostics of the files before
            // it are not printed (`spec/tools.md` §3.1, S-533).
            Err(e) => return internal(io, &sources, &e),
        };
        if out == text {
            continue;
        }
        changed = true;
        if check {
            outln!(io, "would reformat {}", path.display());
        } else if let Err(e) = io.files.replace(path, &out) {
            errln!(io, "onsa: cannot write {}: {e}", path.display());
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
    if report.is_empty() { then } else { print_diagnostics(io, Form::Text, &sources, &report, then) }
}

/// The bytes of the name of the file that the name of the temporary file of
/// [`write_replacing`] keeps (with the process, a number and the rest, well
/// below the 255 bytes of `NAME_MAX`).
const TEMPORARY_NAME_BYTES: usize = 64;

/// Write `text` as the new text of the file `path` (plan S-56): to a
/// temporary file in its directory, then renamed over it, so that the file
/// is the old text or the new one, never half written. A link is followed
/// (the file it names is replaced, the link stays); a file that cannot be
/// written is not replaced; the mode bits of the file are kept, its owner
/// and extended attributes are not; another name of the file (a hard link)
/// keeps the old text. The temporary file is removed whatever step fails.
/// It has the mode of the file before the text is written (made with no
/// rights for others first), and its name keeps the first bytes of the name
/// of the file only, so that it is a name the system takes (`NAME_MAX`).
// `spec/tools.md` §3.6: the link is followed, a read-only file and a
// directory where no temporary file can be made are errors of input and
// output (exit code 2), a hard link keeps the old text.
fn write_replacing(path: &std::path::Path, text: &str) -> std::io::Result<()> {
    use std::io::Write;
    let target = std::fs::canonicalize(path)?;
    // Opened to write without truncating, and closed: the permissions (and an ACL) let it be written.
    std::fs::OpenOptions::new().write(true).open(&target)?;
    let mode = std::fs::metadata(&target)?.permissions();
    let (Some(dir), Some(name)) = (target.parent(), target.file_name()) else {
        return Err(std::io::Error::other("not a file in a directory"));
    };
    let name = name.to_string_lossy();
    let cut = (0..=name.len().min(TEMPORARY_NAME_BYTES)).rev().find(|&i| name.is_char_boundary(i)).unwrap_or(0);
    let name = &name[..cut];
    let mut made = None;
    for n in 0..100 {
        let tmp = dir.join(format!(".{name}.onsa-fmt-{}-{n}.tmp", std::process::id()));
        let mut open = std::fs::OpenOptions::new();
        #[cfg(unix)]
        std::os::unix::fs::OpenOptionsExt::mode(&mut open, 0o600);
        match open.write(true).create_new(true).open(&tmp) {
            Ok(file) => {
                made = Some((tmp, file));
                break;
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
    let Some((tmp, mut file)) = made else {
        return Err(std::io::Error::other("no free name for a temporary file"));
    };
    let written = std::fs::set_permissions(&tmp, mode)
        .and_then(|()| file.write_all(text.as_bytes()))
        .and_then(|()| file.sync_all())
        .and_then(|()| std::fs::rename(&tmp, &target));
    drop(file);
    match written {
        Ok(()) => Ok(()),
        Err(e) => match std::fs::remove_file(&tmp) {
            Ok(()) => Err(e),
            Err(left) => {
                Err(std::io::Error::other(format!("{e} (the temporary file {} is left: {left})", tmp.display())))
            }
        },
    }
}

/// The one path a command that reads a package takes (§15.1, §18.2; S-312):
/// two or more is a usage error (a run handles one package), none is the
/// working directory (`None`).
fn one_path<'p>(io: &mut Io<'_>, paths: &'p [PathBuf]) -> Result<Option<&'p Path>, Outcome> {
    match paths {
        [] => Ok(None),
        [p] => Ok(Some(p.as_path())),
        _ => Err(cannot_work(
            io,
            format!(
                "a command that reads a package takes one path (a `.onsa` file, a package directory or \
             `onsa.toml`), not {}: a run handles one package",
                paths.len()
            ),
        )),
    }
}

/// Load the package of the one path of `paths` ([`one_path`]). The
/// diagnostics of its manifest stop the command before the sources are read
/// (§18.1): printed in `form`, exit 2.
fn load(io: &mut Io<'_>, form: Form, paths: &[PathBuf]) -> Result<onsa_driver::Loaded, Outcome> {
    let path = one_path(io, paths)?;
    let loaded = io.files.load(path).map_err(|e| cannot_work(io, e))?;
    let diagnostics = loaded.manifest_diagnostics();
    if !diagnostics.is_empty() {
        return Err(print_diagnostics(io, form, &loaded.sources, diagnostics, Outcome::of(diagnostics)));
    }
    Ok(loaded)
}

fn check(io: &mut Io<'_>, json: bool, paths: &[PathBuf]) -> Done {
    let mut loaded = load(io, Form::json(json), paths)?;
    let result = onsa_driver::check_loaded(&mut loaded).map_err(|e| internal(io, &loaded.sources, &e))?;
    Ok(print_diagnostics(io, Form::json(json), &loaded.sources, &result.diagnostics, Outcome::of(&result.diagnostics)))
}

fn explain(io: &mut Io<'_>, code: &str) -> Outcome {
    let Some(code) = Code::parse(code) else {
        return cannot_work(io, format!("unknown diagnostic code `{code}`"));
    };
    match code.explain() {
        Some(text) => out!(io, "{text}"),
        None => outln!(io, "# {}: {}\n\n(No long explanation written yet.)", code.as_str(), code.title()),
    }
    Outcome::Ok
}

/// `onsa diff --ast old new`: items added / removed / changed, ignoring trivia (`spec/tools.md` §3.5).
fn diff(io: &mut Io<'_>, ast: bool, old_path: &PathBuf, new_path: &PathBuf) -> Outcome {
    if !ast {
        return cannot_work(io, "`diff` needs `--ast` (textual diff is what `git diff` is for)");
    }
    let mut sources = SourceMap::default();
    let mut files = Vec::new();
    for path in [old_path, new_path] {
        let text = match io.files.read(path) {
            Ok(t) => t,
            Err(e) => return cannot_work(io, format!("cannot read {}: {e}", path.display())),
        };
        // The same file on both sides is one file (its diagnostics once).
        if files.len() == 1 && io.files.canonical(old_path) == io.files.canonical(new_path) {
            files.push(files[0]);
            continue;
        }
        files.push(sources.add(onsa_driver::slash_path(path), text));
    }
    let diffs = match onsa_driver::diff_ast(&sources, files[0], files[1]) {
        Ok(onsa_driver::AstDiff::Items(d)) => d,
        Ok(onsa_driver::AstDiff::Syntax(diagnostics)) => {
            return print_diagnostics(io, Form::Text, &sources, &diagnostics, Outcome::CannotWork);
        }
        Err(e) => return internal(io, &sources, &e),
    };
    let line = |span: Option<onsa_diag::Span>| span.map(|s| sources.file(s.file).line_col(s.start).line).unwrap_or(0);
    for d in &diffs {
        use onsa_syntax::diff::Change;
        match d.change {
            Change::Added => outln!(io, "+ {}  (new:{})", d.key, line(d.new)),
            Change::Removed => outln!(io, "- {}  (old:{})", d.key, line(d.old)),
            Change::Changed => {
                outln!(
                    io,
                    "~ {}  (old:{} new:{}; first change at new:{})",
                    d.key,
                    line(d.old),
                    line(d.new),
                    line(d.first)
                )
            }
        }
    }
    if diffs.is_empty() { Outcome::Ok } else { Outcome::Problems }
}

/// Load and analyze one package; print the diagnostics and return the
/// outcome when it does not check.
fn analyzed(
    io: &mut Io<'_>,
    form: Form,
    paths: &[PathBuf],
) -> Result<(onsa_driver::Loaded, onsa_driver::Analyzed), Outcome> {
    let mut loaded = load(io, form, paths)?;
    let analyzed = match onsa_driver::analyze_loaded(&mut loaded) {
        Ok(a) => a,
        Err(e) => return Err(internal(io, &loaded.sources, &e)),
    };
    if !analyzed.diagnostics.is_empty() {
        return Err(print_diagnostics(io, form, &loaded.sources, &analyzed.diagnostics, Outcome::Problems));
    }
    Ok((loaded, analyzed))
}

/// Lower to Core; print its diagnostics and return the outcome when it does not lower.
fn lowered(
    io: &mut Io<'_>,
    form: Form,
    loaded: &onsa_driver::Loaded,
    analyzed: &onsa_driver::Analyzed,
) -> Result<onsa_core::Module, Outcome> {
    match onsa_driver::lower_core(analyzed) {
        Ok(m) => Ok(m),
        Err(onsa_driver::LowerError::Diagnostics(diags)) => {
            Err(print_diagnostics(io, form, &loaded.sources, &diags, Outcome::Problems))
        }
        Err(onsa_driver::LowerError::Internal(e)) => Err(internal(io, &loaded.sources, &e)),
    }
}

/// `onsa dump --cst [--tree] <file>`: the CST of one file (R-86). Exit 0
/// also when the file has syntax errors (the CST is complete); the syntax
/// diagnostics are not printed.
fn dump_cst(io: &mut Io<'_>, tree: bool, paths: &[PathBuf]) -> Done {
    let (sources, file) = read_one(io, paths, "dump --cst")?;
    let out = onsa_driver::cst_dump(&sources, file, tree).map_err(|e| internal(io, &sources, &e))?;
    out!(io, "{out}");
    Ok(Outcome::Ok)
}

/// `onsa dump --levels`: the levels of each declaration of one file (the fmt properties).
fn dump_levels(io: &mut Io<'_>, paths: &[PathBuf]) -> Done {
    let (sources, file) = read_one(io, paths, "dump --levels")?;
    let out = onsa_driver::levels_dump(&sources, file).map_err(|e| internal(io, &sources, &e))?;
    out!(io, "{out}");
    Ok(Outcome::Ok)
}

/// The one file a command of one file (`command`) takes, read into its sources.
fn read_one(io: &mut Io<'_>, paths: &[PathBuf], command: &str) -> Result<(SourceMap, onsa_diag::FileId), Outcome> {
    let [path] = paths else {
        return Err(cannot_work(io, format!("`{command}` takes one file")));
    };
    let text = io.files.read(path).map_err(|e| cannot_work(io, format!("cannot read {}: {e}", path.display())))?;
    let mut sources = SourceMap::default();
    let file = sources.add(onsa_driver::slash_path(path), text);
    Ok((sources, file))
}

/// `onsa dump --core`: the Core IR of a package (after `check` passes). The
/// path is that of `check`; a file inside a package does not narrow the
/// Core, which is the whole program after monomorphization (`dump` is an
/// internal tool, outside the table of §18.2).
fn dump(io: &mut Io<'_>, core: bool, paths: &[PathBuf]) -> Done {
    if !core {
        return Err(cannot_work(io, "`dump` needs `--core`"));
    }
    let (loaded, analyzed) = analyzed(io, Form::Text, paths)?;
    let module = lowered(io, Form::Text, &loaded, &analyzed)?;
    out!(io, "{}", onsa_core::dump(&module));
    Ok(Outcome::Ok)
}

/// `onsa interface [--json] [<path>]` (T3-11). With `--json`, diagnostics
/// are the document of `check --json` (§18.1). A file inside a package
/// narrows the output to its module (§15.1); the diagnostics that stop the
/// command are not narrowed (only `check` narrows its diagnostics).
// SPEC-GAP(S-657): with a file passed inside a package, the diagnostics
// that stop `interface` and `graph` are all those of the package (exit 1),
// also those of the other modules; only the results are narrowed.
fn interface(io: &mut Io<'_>, json: bool, paths: &[PathBuf]) -> Done {
    let (loaded, analyzed) = analyzed(io, Form::json(json), paths)?;
    let narrowed = onsa_driver::interface(&analyzed).and_then(|mut iface| {
        let narrowed = onsa_driver::guard(|| {
            if let Some(module) = loaded.focus_module() {
                iface.narrow(&module);
            }
            iface
        });
        Ok(narrowed?)
    });
    let iface = match narrowed {
        Ok(iface) => iface,
        Err(onsa_driver::LowerError::Diagnostics(d)) => {
            return Ok(print_diagnostics(io, Form::json(json), &loaded.sources, &d, Outcome::Problems));
        }
        Err(onsa_driver::LowerError::Internal(e)) => return Err(internal(io, &loaded.sources, &e)),
    };
    if json {
        outln!(io, "{}", onsa_driver::render_json(&iface));
    } else {
        out!(io, "{}", onsa_driver::render_text(&iface));
    }
    Ok(Outcome::Ok)
}

/// `onsa graph [--svg] <flow> [<path>]` (T3-12, §18.2): the flow is named in
/// the module of a file passed inside a package, else in the package.
// SPEC-GAP(S-657): the diagnostics that stop it are not narrowed, as for `interface`.
fn graph(io: &mut Io<'_>, svg: bool, flow: &str, paths: &[PathBuf]) -> Done {
    let (loaded, analyzed) = analyzed(io, Form::Text, paths)?;
    let scope = onsa_driver::guard(|| loaded.focus_module()).map_err(|e| internal(io, &loaded.sources, &e))?;
    let dot = onsa_driver::graph(&analyzed, flow, scope.as_deref()).map_err(|e| match e {
        onsa_driver::GraphError::Usage(e) => cannot_work(io, e),
        onsa_driver::GraphError::Internal(e) => internal(io, &loaded.sources, &e),
    })?;
    if svg {
        let svg = onsa_driver::graph::to_svg(&dot).map_err(|e| cannot_work(io, e))?;
        out!(io, "{svg}");
    } else {
        out!(io, "{dot}");
    }
    Ok(Outcome::Ok)
}

/// `onsa test <paths> [--json] [--filter <text>]` (T3-8, §18.2): check, lower,
/// match `--filter`, run the selected tests. The checks and the E0200 of
/// lowering stop the run before the filter is matched; a filter that selects
/// no test of the package is a usage error (exit 2, nothing on the standard
/// output). A file passed inside a package selects the tests of its module
/// (S-286); the filter is still matched on the whole package (S-311), and
/// the diagnostics that stop the run are all those of the package.
fn test(io: &mut Io<'_>, json: bool, filter: Option<String>, paths: &[PathBuf]) -> Done {
    let form = if json { Form::TestJson } else { Form::Text };
    let (loaded, analyzed) = analyzed(io, form, paths)?;
    let module = lowered(io, form, &loaded, &analyzed)?;
    let focus = onsa_driver::guard(|| loaded.focus_module()).map_err(|e| internal(io, &loaded.sources, &e))?;
    let opts = onsa_driver::TestOptions { filter, module: focus };
    let report = match onsa_driver::run_tests(&loaded.sources, &module, &opts) {
        Ok(onsa_driver::TestRun::Ran(r)) => r,
        Ok(onsa_driver::TestRun::NoMatch) => {
            let filter = opts.filter.as_deref().unwrap_or_default();
            return Err(cannot_work(io, format!("`--filter {filter:?}` matches no test")));
        }
        // E0200, as those of lowering: no test ran (S-224).
        Ok(onsa_driver::TestRun::Unsupported(diags)) => {
            return Err(print_diagnostics(io, form, &loaded.sources, &diags, Outcome::Problems));
        }
        Err(e) => return Err(internal(io, &loaded.sources, &e)),
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
    let text = text.map_err(|e| internal(io, &loaded.sources, &e))?;
    out!(io, "{text}");
    Ok(if report.failed() == 0 { Outcome::Ok } else { Outcome::Problems })
}

/// `onsa build --target <name> [--out <dir>] [<path>]` (T4-5, §18.2).
fn build(io: &mut Io<'_>, target: &str, out: Option<PathBuf>, paths: &[PathBuf]) -> Done {
    let opts = onsa_driver::BuildOptions { target: target.to_string(), out };
    let path = one_path(io, paths)?;
    Ok(match onsa_driver::build(path, &opts) {
        Ok(r) => {
            let platform = onsa_driver::manifest::shown(&r.platform);
            outln!(io, "built `{}` for {platform} ({}) in {}", r.target, r.kind, r.out_dir.display());
            for f in &r.files {
                outln!(io, "  {f}");
            }
            if let Some(n) = &r.note {
                outln!(io, "note: {}", onsa_driver::manifest::shown(n));
            }
            Outcome::Ok
        }
        Err(onsa_driver::BuildError::Usage(m)) => cannot_work(io, m),
        Err(
            onsa_driver::BuildError::Diagnostics { sources, diagnostics }
            | onsa_driver::BuildError::Manifest { sources, diagnostics, .. },
        ) => print_diagnostics(io, Form::Text, &sources, &diagnostics, Outcome::of(&diagnostics)),
        Err(onsa_driver::BuildError::Internal { sources, error }) => internal(io, &sources, &error),
    })
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

    /// Run `args` (after `onsa`) with buffers for the outputs: (exit code, stdout, stderr).
    fn run_with(args: &[&str], out: &mut (dyn Write + Send)) -> (u8, String) {
        let cli = Cli::try_parse_from(std::iter::once("onsa").chain(args.iter().copied())).unwrap();
        let mut err = Vec::new();
        let code = run_command(cli.command, &mut Io::new(out, &mut err, &Disk));
        (code, String::from_utf8(err).unwrap())
    }

    #[test]
    fn a_command_writes_to_the_outputs_it_is_given() {
        let mut out = Vec::new();
        assert_eq!(run_with(&["explain", "E0811"], &mut out), (0, String::new()));
        assert!(String::from_utf8(out).unwrap().contains("E0811"));
        let mut out = Vec::new();
        assert_eq!(run_with(&["explain", "E99"], &mut out), (2, "onsa: unknown diagnostic code `E99`\n".into()));
        assert!(out.is_empty());
    }

    /// A failure to write the standard output is exit 2 with its message on the standard error, once.
    #[test]
    fn a_failed_write_to_the_standard_output_is_exit_2() {
        struct Closed;
        impl Write for Closed {
            fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("closed"))
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let (code, err) = run_with(&["explain", "E0811"], &mut Closed);
        assert_eq!((code, err.as_str()), (2, "onsa: cannot write to standard output: closed\n"));
    }
}
