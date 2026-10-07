//! The checks of the generated C (Q-07, W1-06, plan D-16 6): the C
//! compilers and their settings, as one table ([`ITEMS`]), and the compile
//! steps they share.
//!
//! Each row is a gate item (`tools/gate_steps.py`) that `onsa_cases --c
//! <item>` runs over every build of the cases ([`crate::ccheck`]):
//!
//! ```text
//! c-clang          clang   -Wall -Wextra -Werror -pedantic, the target's flags; conformance
//! c-gcc            gcc-15  the same, without the warnings of [`GCC_KNOWN_OFF`]
//! c-gcc-strict     gcc-15  the same with every warning
//! c-sanitize       clang   as c-clang with ASan and UBSan; conformance under the sanitizers
//! c-x86            clang   as c-clang with -arch x86_64; conformance under Rosetta
//! c-header         the public headers alone in C11 (clang; gcc-15 without [`GCC_KNOWN_OFF`])
//! c-header-strict  the public headers alone in C99 (clang, gcc-15) and C++11 (clang++, g++-15)
//! ```
//!
//! A check that waits for a later work is split so that a new error never
//! hides behind the known one: the item that runs every warning (`-strict`)
//! is the one the pending list holds as a whole; its pair switches off only
//! the warnings of the known causes, one table each ([`GCC_KNOWN_OFF`]), and
//! is never pending.
//!
//! A compiler that is not on the PATH fails the item: nothing is skipped
//! silently (R-113 3).
//!
//! No run may end by a signal (a crash report on macOS): the conformance
//! driver turns a panic of the generated code into exit code
//! [`PANIC_EXIT`] through `ONSA_PANIC_HANDLER` (the trap is never reached),
//! catches the fatal signals into [`SIGNAL_EXIT`] on an alternate stack, and
//! the sanitizers stop with an exit code ([`sanitizer_env`]), never by `abort`.

use std::io::{Read as _, Write as _};
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use onsa_backend_c::CUnit;

/// `onsa_voice.h` etc. joined into one golden file.
pub fn join_headers(unit: &CUnit) -> String {
    let mut s = String::new();
    for (name, text) in &unit.headers {
        s.push_str(&format!("/* ==== {name} ==== */\n"));
        s.push_str(text);
    }
    s
}

/// The warnings every compile of generated C uses (spec §13.4: no warning
/// under `-Wall -Wextra -pedantic`, so a host may build with `-Werror`).
pub const WARNINGS: &[&str] = &["-Wall", "-Wextra", "-Werror", "-pedantic"];

/// The flags of a compile outside a target's settings (the end-to-end tests):
/// the host target's flags (spec §13.4) and [`WARNINGS`].
pub const CFLAGS: &[&str] =
    &["-std=c11", "-ffp-contract=off", "-fno-fast-math", "-Wall", "-Wextra", "-Werror", "-pedantic"];

/// The exit code of the conformance driver when `init` or `process` returns
/// an error (other than a panic, which never returns).
pub const API_ERROR_EXIT: i32 = 3;
/// The exit code of the conformance driver when it cannot read its input.
pub const INPUT_EXIT: i32 = 4;
/// The exit code of the conformance driver when it cannot install its signal handlers.
pub const SETUP_EXIT: i32 = 5;
/// The exit code of the conformance driver when the generated code panics.
pub const PANIC_EXIT: i32 = 75;
/// The exit code of the conformance driver on a fatal signal.
pub const SIGNAL_EXIT: i32 = 76;
/// The exit code of the sanitizers (ASan and UBSan share the runtime, so one code).
pub const SANITIZER_EXIT: i32 = 86;
/// The exit code of a driver that cannot write its standard output (the host steps).
pub const OUTPUT_EXIT: i32 = 8;
/// The exit code of a driver called with the wrong arguments (the host steps, [`crate::host`]).
pub const ARGS_EXIT: i32 = 6;
/// The exit code of the host-steps driver when `panic = "reset"` calls the firmware's hook.
pub const RESET_HOOK_EXIT: i32 = 77;
/// How long one run of a driver program may take.
pub const RUN_TIMEOUT: Duration = Duration::from_secs(60);
/// Defined when a driver runs under the sanitizers ([`Runner::Sanitized`]): it
/// leaves the signals to them.
pub const SANITIZED_DEFINE: &str = "ONSA_DRIVER_SANITIZED";

/// The start of a driver program of the generated C, shared by the
/// conformance harness and the host steps: the headers, a fatal signal turned
/// into [`SIGNAL_EXIT`] on its own stack (a stack overflow too; never a crash
/// report), and `onsa_driver_read`, which reads `n` bytes of the standard input.
pub fn driver_preamble(headers: &[&str]) -> String {
    let mut d = String::from("#define _XOPEN_SOURCE 700\n");
    // sigaction and sigaltstack are POSIX (XSI), outside ISO C.
    for h in headers {
        d.push_str(&format!("#include \"{h}\"\n"));
    }
    d.push_str("#include <signal.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n\n");
    d.push_str(&format!(
        "#ifndef {SANITIZED_DEFINE}\n\
         static void onsa_driver_signal(int sig) {{ (void)sig; _Exit({SIGNAL_EXIT}); }}\n\
         static char onsa_driver_altstack[65536];\n\
         static int onsa_driver_signals(void) {{\n  \
         stack_t ss;\n  memset(&ss, 0, sizeof ss);\n  ss.ss_sp = onsa_driver_altstack;\n  \
         ss.ss_size = sizeof onsa_driver_altstack;\n  if (sigaltstack(&ss, NULL) != 0) return 0;\n  \
         struct sigaction sa;\n  memset(&sa, 0, sizeof sa);\n  sa.sa_handler = onsa_driver_signal;\n  \
         sigemptyset(&sa.sa_mask);\n  sa.sa_flags = SA_ONSTACK;\n  \
         const int sigs[] = {{ SIGSEGV, SIGILL, SIGFPE, SIGABRT, SIGBUS, SIGTRAP }};\n  \
         for (size_t i = 0; i < sizeof sigs / sizeof sigs[0]; i++)\n    \
         if (sigaction(sigs[i], &sa, NULL) != 0) return 0;\n  return 1;\n}}\n\
         #else\n\
         static int onsa_driver_signals(void) {{ return 1; }}\n\
         #endif\n"
    ));
    d.push_str("static int onsa_driver_read(void* p, size_t n) { return n == 0 || fread(p, 1, n, stdin) == n; }\n");
    d
}

/// A driver program that ended (or was stopped).
#[derive(Debug)]
pub struct Finished {
    /// `None`: it ran longer than the timeout and was killed (SIGKILL: no crash report).
    pub status: Option<ExitStatus>,
    pub stdout: Vec<u8>,
    pub stderr: String,
}

/// Run a driver program with `args` and `input` on its standard input, within
/// `timeout`, the way `runner` says.
pub fn run_program(
    exe: &Path,
    args: &[String],
    runner: Runner,
    input: Vec<u8>,
    timeout: Duration,
) -> Result<Finished, String> {
    let mut cmd = match runner {
        Runner::Rosetta => {
            let mut c = Command::new("arch");
            c.arg("-x86_64").arg(exe);
            c
        }
        _ => Command::new(exe),
    };
    cmd.args(args);
    if runner == Runner::Sanitized {
        cmd.envs(sanitizer_env());
    }
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    let mut stdin = child.stdin.take().expect("piped stdin");
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let mut stdout = child.stdout.take().expect("piped stdout");
    let reader = std::thread::spawn(move || {
        let mut b = Vec::new();
        stdout.read_to_end(&mut b).map(|_| b)
    });
    let mut stderr = child.stderr.take().expect("piped stderr");
    let err_reader = std::thread::spawn(move || {
        let mut b = Vec::new();
        stderr.read_to_end(&mut b).map(|_| b)
    });
    let start = Instant::now();
    let status = loop {
        if let Some(s) = child.try_wait().map_err(|e| e.to_string())? {
            break Some(s);
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    // A program that stops reading early closes the pipe: not an error of the run.
    let _ = writer.join();
    let stdout = reader
        .join()
        .map_err(|_| "the reader of the program's stdout failed".to_string())?
        .map_err(|e| format!("cannot read the program's stdout: {e}"))?;
    let stderr = err_reader
        .join()
        .map_err(|_| "the reader of the program's stderr failed".to_string())?
        .map_err(|e| format!("cannot read the program's stderr: {e}"))?;
    let stderr = String::from_utf8_lossy(&stderr).trim_end().to_string();
    Ok(Finished { status, stdout, stderr })
}

/// The driver programs, each with the exit codes it returns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriverKind {
    /// The conformance harness ([`crate::conformance`]).
    Conformance,
    /// The host steps ([`crate::host`]).
    Host,
}

/// What an exit code of a driver program of `kind` means (the codes of
/// [`driver_preamble`], the driver's own, the sanitizers'); `None` for a
/// code that driver does not return.
pub fn exit_meaning(kind: DriverKind, code: i32) -> Option<&'static str> {
    use DriverKind::{Conformance, Host};
    Some(match (kind, code) {
        (_, INPUT_EXIT) => "the program could not read its input",
        (_, SETUP_EXIT) => "the program could not install its signal handlers",
        (_, SIGNAL_EXIT) => "a fatal signal (caught)",
        (_, SANITIZER_EXIT) => "a sanitizer (ASan or UBSan) reported an error",
        (Conformance, API_ERROR_EXIT) => "`init` or `process` returned an error",
        (Conformance, PANIC_EXIT) => "the generated code panicked",
        (Host, OUTPUT_EXIT) => "the program could not write its output",
        (Host, ARGS_EXIT) => "the program was called with wrong arguments",
        (Host, RESET_HOOK_EXIT) => "the reset hook was called (`panic = \"reset\"`)",
        _ => return None,
    })
}

/// The environment of a sanitized run: the sanitizers report and exit with
/// [`SANITIZER_EXIT`]; they never `abort` (macOS writes a crash report for a
/// process that ends by a signal).
pub fn sanitizer_env() -> Vec<(&'static str, String)> {
    vec![
        (
            "ASAN_OPTIONS",
            format!(
                "abort_on_error=0:exitcode={SANITIZER_EXIT}:halt_on_error=1:detect_leaks=0:handle_abort=1:\
                 handle_sigill=1:handle_sigtrap=1:handle_segv=1:handle_sigbus=1:handle_sigfpe=1"
            ),
        ),
        ("UBSAN_OPTIONS", format!("halt_on_error=1:abort_on_error=0:exitcode={SANITIZER_EXIT}:print_stacktrace=1")),
    ]
}

/// How a conformance program runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Runner {
    /// Directly.
    Native,
    /// Directly, with [`sanitizer_env`]; the driver leaves the signals to the sanitizers.
    Sanitized,
    /// Under Rosetta (`arch -x86_64`): another 64-bit architecture on this machine.
    Rosetta,
}

/// The warnings `c-gcc` and the C11 header check of gcc-15 switch off, each
/// for a known cause that a later work removes; `c-gcc-strict` and
/// `c-header-strict` keep them. W2-09 (R-67, S-54) removes both causes and
/// this table: GCC does not know `#pragma STDC FP_CONTRACT`
/// (`-Wunknown-pragmas`), and the integer helpers of `onsa.h` compare an
/// unsigned value with 0 (`-Wtype-limits`).
pub const GCC_KNOWN_OFF: &[&str] = &["-Wno-unknown-pragmas", "-Wno-type-limits"];

/// A compiler and the flags it adds to the target's.
#[derive(Debug, Clone, Copy)]
pub struct Toolchain {
    pub cc: &'static str,
    /// After the target's flags and [`WARNINGS`].
    pub flags: &'static [&'static str],
    /// Warnings switched off for a known cause (last: they win), [`GCC_KNOWN_OFF`].
    pub off: &'static [&'static str],
    pub runner: Runner,
}

/// One compiler of the header check.
#[derive(Debug, Clone, Copy)]
pub struct HeaderCompiler {
    /// The name in the case IDs (`c99-gcc-15`).
    pub label: &'static str,
    pub cc: &'static str,
    pub flags: &'static [&'static str],
    /// Warnings switched off for a known cause, [`GCC_KNOWN_OFF`].
    pub off: &'static [&'static str],
    /// The extension of the file that includes the headers (`c`, `cpp`).
    pub ext: &'static str,
}

#[derive(Debug, Clone, Copy)]
pub enum Check {
    /// Compile the C of every build; run the conformance of the builds that declare it.
    Unit(Toolchain),
    /// Compile the public headers of every build alone, with each compiler.
    Headers(&'static [HeaderCompiler]),
}

/// A gate item of the C checks.
#[derive(Debug, Clone, Copy)]
pub struct Item {
    pub name: &'static str,
    pub check: Check,
}

impl Item {
    /// The programs the item needs on the PATH.
    pub fn programs(&self) -> Vec<&'static str> {
        let mut v: Vec<&'static str> = match self.check {
            Check::Unit(t) => vec![t.cc],
            Check::Headers(cs) => cs.iter().map(|c| c.cc).collect(),
        };
        if matches!(self.check, Check::Unit(Toolchain { runner: Runner::Rosetta, .. })) {
            v.push("arch");
        }
        v.dedup();
        v
    }

    /// Why the item cannot run on this machine (a program missing, no way to
    /// run x86_64 code): errors of the item, never of a case.
    pub fn cannot_run(&self) -> Vec<String> {
        let mut errors: Vec<String> = self.programs().into_iter().filter_map(|p| require(p).err()).collect();
        if errors.is_empty() && matches!(self.check, Check::Unit(Toolchain { runner: Runner::Rosetta, .. })) {
            errors.extend(require_x86_64().err());
        }
        errors
    }
}

/// Whether this machine runs x86_64 code (Rosetta on Apple silicon):
/// `arch -x86_64 /usr/bin/true`.
pub fn require_x86_64() -> Result<(), String> {
    match Command::new("arch").args(["-x86_64", "/usr/bin/true"]).output() {
        Ok(o) if o.status.success() => Ok(()),
        Ok(o) => Err(format!(
            "`arch -x86_64 /usr/bin/true` failed ({}): {}; c-x86 needs Rosetta",
            o.status,
            String::from_utf8_lossy(&o.stderr).trim()
        )),
        Err(e) => Err(format!("cannot run `arch -x86_64 /usr/bin/true`: {e}; c-x86 needs Rosetta")),
    }
}

pub const SANITIZE: &[&str] =
    &["-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer", "-g", "-O1"];

const HEADER_C11: &[&str] = &["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fsyntax-only"];
const HEADER_C99: &[&str] = &["-std=c99", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fsyntax-only"];
const HEADER_CXX11: &[&str] = &["-std=c++11", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fsyntax-only"];

const fn unit(cc: &'static str, flags: &'static [&'static str], off: &'static [&'static str], runner: Runner) -> Check {
    Check::Unit(Toolchain { cc, flags, off, runner })
}

const fn header(
    label: &'static str,
    cc: &'static str,
    flags: &'static [&'static str],
    off: &'static [&'static str],
    ext: &'static str,
) -> HeaderCompiler {
    HeaderCompiler { label, cc, flags, off, ext }
}

/// The C checks, one gate item each (Q-07).
pub const ITEMS: &[Item] = &[
    Item { name: "c-clang", check: unit("clang", &[], &[], Runner::Native) },
    Item { name: "c-gcc", check: unit("gcc-15", &[], GCC_KNOWN_OFF, Runner::Native) },
    Item { name: "c-gcc-strict", check: unit("gcc-15", &[], &[], Runner::Native) },
    Item { name: "c-sanitize", check: unit("clang", SANITIZE, &[], Runner::Sanitized) },
    Item { name: "c-x86", check: unit("clang", &["-arch", "x86_64"], &[], Runner::Rosetta) },
    Item {
        name: "c-header",
        check: Check::Headers(&[
            header("c11-clang", "clang", HEADER_C11, &[], "c"),
            header("c11-gcc-15", "gcc-15", HEADER_C11, GCC_KNOWN_OFF, "c"),
        ]),
    },
    Item {
        name: "c-header-strict",
        check: Check::Headers(&[
            header("c99-clang", "clang", HEADER_C99, &[], "c"),
            header("c99-gcc-15", "gcc-15", HEADER_C99, &[], "c"),
            header("c++11-clang++", "clang++", HEADER_CXX11, &[], "cpp"),
            header("c++11-g++-15", "g++-15", HEADER_CXX11, &[], "cpp"),
        ]),
    },
];

pub fn item(name: &str) -> Option<&'static Item> {
    ITEMS.iter().find(|i| i.name == name)
}

/// Whether `program` runs (`<program> --version`); the error when it does not.
pub fn require(program: &str) -> Result<(), String> {
    // `arch` takes no `--version`; alone, it prints the machine's architecture.
    let args: &[&str] = if program == "arch" { &[] } else { &["--version"] };
    match Command::new(program).args(args).output() {
        Ok(o) if o.status.success() => Ok(()),
        Ok(o) => Err(format!(
            "`{program} {}` failed ({}): {}",
            args.join(" "),
            o.status,
            String::from_utf8_lossy(&o.stderr).trim()
        )),
        Err(e) => Err(format!("`{program}` is not on the PATH ({e}); the C checks need it (Q-07)")),
    }
}

/// Write the files of a build into `dir`.
pub fn write_files(dir: &Path, files: &[(String, String)]) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    for (name, text) in files {
        std::fs::write(dir.join(name), text).map_err(|e| format!("cannot write {name}: {e}"))?;
    }
    Ok(())
}

/// Run a compiler; its diagnostics when it fails.
pub fn compile(cmd: &mut Command, what: &str) -> Result<(), String> {
    let out = cmd.output().map_err(|e| format!("cannot run the compiler for {what}: {e}"))?;
    if !out.status.success() {
        return Err(format!("{what} failed ({}):\n{}", out.status, head(&String::from_utf8_lossy(&out.stderr))));
    }
    Ok(())
}

/// The lines of a compiler's report that the summary shows.
const HEAD_LINES: usize = 12;

/// The first lines of `text`, and how many more there are.
pub fn head(text: &str) -> String {
    let lines: Vec<&str> = text.trim_end().lines().collect();
    if lines.len() <= HEAD_LINES {
        return lines.join("\n");
    }
    let errors = lines.iter().filter(|l| l.contains("error:")).count();
    format!(
        "{}\n... {} more lines ({errors} lines with `error:` in all)",
        lines[..HEAD_LINES].join("\n"),
        lines.len() - HEAD_LINES
    )
}

/// The compile command of a toolchain over the target's flags.
pub fn command(t: &Toolchain, target_flags: &[String], dir: &Path) -> Command {
    let mut c = Command::new(t.cc);
    c.args(target_flags).args(WARNINGS).args(t.flags).args(t.off).arg("-I").arg(dir);
    c
}

/// Compile the C source of a build to an object in `dir` (the files must be written there).
pub fn compile_object(t: &Toolchain, target_flags: &[String], dir: &Path, source_name: &str) -> Result<(), String> {
    let mut c = command(t, target_flags, dir);
    c.arg("-c").arg(dir.join(source_name)).arg("-o").arg(dir.join("out.o"));
    compile(&mut c, &format!("{} -c {source_name}", t.cc))
}

/// Compile a file that includes one public header (written in `dir`) twice,
/// with one compiler: the first include checks that the header stands alone,
/// the second its include guard.
pub fn compile_header(h: &HeaderCompiler, dir: &Path, header: &str) -> Result<(), String> {
    let text = format!(
        "#include \"{header}\"\n#include \"{header}\"\nint onsa_header_check(void);\nint onsa_header_check(void) {{ return 0; }}\n"
    );
    let stem: String = header.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
    let file = dir.join(format!("include_{stem}_{}.{}", h.label.replace('+', "x"), h.ext));
    std::fs::write(&file, text).map_err(|e| format!("cannot write {}: {e}", file.display()))?;
    let mut c = Command::new(h.cc);
    c.args(h.flags).args(h.off).arg("-I").arg(dir).arg(&file);
    let what = [h.cc].iter().chain(h.flags).chain(h.off).copied().collect::<Vec<_>>().join(" ");
    compile(&mut c, &format!("{what} (`{header}` included twice)"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sanitizers are on, and stop with [`SANITIZER_EXIT`], never by a
    /// signal: undefined behaviour and a heap overflow, built with
    /// [`SANITIZE`] and run with [`sanitizer_env`].
    #[test]
    fn sanitizers_stop_with_their_exit_code() {
        require("clang").unwrap();
        let dir = std::env::temp_dir().join(format!("onsa_sanitize_test_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let cases = [
            (
                "ub",
                "#include <limits.h>\nint main(int argc, char** argv) {\n  (void)argv;\n  int x = INT_MAX;\n  return x + argc > 0;\n}\n",
            ),
            (
                "heap",
                "#include <stdlib.h>\nint main(int argc, char** argv) {\n  (void)argv;\n  int* p = malloc(4 * sizeof *p);\n  \
                 if (!p) return 2;\n  p[3 + argc] = 1;\n  int r = p[0];\n  free(p);\n  return r;\n}\n",
            ),
        ];
        for (name, text) in cases {
            let src = dir.join(format!("{name}.c"));
            std::fs::write(&src, text).unwrap();
            let exe = dir.join(name);
            let mut cc = Command::new("clang");
            cc.args(["-std=c11"]).args(SANITIZE).arg(&src).arg("-o").arg(&exe);
            compile(&mut cc, name).unwrap();
            let out = Command::new(&exe).envs(sanitizer_env()).output().unwrap();
            assert_eq!(out.status.code(), Some(SANITIZER_EXIT), "{name}: {}", String::from_utf8_lossy(&out.stderr));
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An item that switches warnings off has a `-strict` pair that runs the
    /// same compilers with every warning (a new error never hides).
    #[test]
    fn relaxed_items_have_a_strict_pair() {
        let offs = |i: &Item| -> Vec<&'static [&'static str]> {
            match i.check {
                Check::Unit(t) => vec![t.off],
                Check::Headers(cs) => cs.iter().map(|h| h.off).collect(),
            }
        };
        let relaxed: Vec<&Item> = ITEMS.iter().filter(|i| offs(i).iter().any(|o| !o.is_empty())).collect();
        assert_eq!(relaxed.iter().map(|i| i.name).collect::<Vec<_>>(), ["c-gcc", "c-header"]);
        for i in relaxed {
            let strict =
                item(&format!("{}-strict", i.name)).unwrap_or_else(|| panic!("{} has no -strict pair", i.name));
            assert!(offs(strict).iter().all(|o| o.is_empty()), "{}", strict.name);
            let mut a = i.programs();
            a.sort();
            let mut b = strict.programs();
            b.sort();
            assert!(a.iter().all(|p| b.contains(p)), "{}: {a:?} vs {b:?}", i.name);
        }
        for i in ITEMS {
            assert!(i.name.ends_with("-strict") || offs(i).iter().all(|o| o.is_empty() || *o == GCC_KNOWN_OFF));
        }
    }
}
