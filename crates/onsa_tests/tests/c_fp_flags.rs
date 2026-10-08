//! The floating-point flags and the warnings of the generated C, the public and the internal runtime
//! header (spec §13.4, §14.2, §15.5, §9.2; W2-09/t: R-67, S-54, S-53, R-142, R-145, S-207, R-167).
//!
//! Written from the spec before the implementation (plan §8.5): the expected values are the ones the
//! spec fixes, never an output of the compiler. What the spec fixes, and so what is checked here:
//!
//! - the runtime is split: `onsa.h` and the header of the package are the public headers a host
//!   reads (C99 and C++11, `-pedantic`, no warning, whatever the mode or the float flags of the
//!   host); `onsa__runtime.h` is the internal header that only the generated `.c` reads, and it
//!   holds the `#error` checks (§14.2). A build with `kind = "source"` writes both (§14.2);
//! - the generated `.c` stops at compile time when a flag it needs is not kept (§13.4, `#error`):
//!   GCC in the GNU mode without `ONSA_FP_CONTRACT_OFF`, `__FAST_MATH__`, `__FINITE_MATH_ONLY__`,
//!   `FLT_EVAL_METHOD` not 0. The message names the flag. `ONSA_ALLOW_INEXACT_FP` removes all of
//!   them. The ISO mode of GCC (`__STRICT_ANSI__`) needs no define;
//! - the STDC pragma is written for the compilers that know it and not for GCC; the first comment
//!   of the `.c` lists the flags of the target;
//! - the generated C compiles without a warning under `-Wall -Wextra -pedantic` with GCC and Clang
//!   (R-67 `-Wunknown-pragmas`, `-Wtype-limits`; R-142 `-Wparentheses-equality`; R-145
//!   `-Wsometimes-uninitialized`, `-Wsign-compare`; R-167 `-Wclobbered` of the poison wrapper);
//! - the results do not depend on a fused multiply-add for any supported flag set, and a function
//!   with `@fp(relaxed)` gets no GCC reassociation (S-207, §13.4).
//!
//! Not written here, because the spec does not say: how `@fp(relaxed)` reaches a function that a
//! relaxed function calls or that calls it (reported as a gap); the exact text of the `#error`
//! messages (only the flags they name); the attribute or pragma that a relaxed function gets
//! (§13.4 says only "関数ごとの緩和"); MSVC (`_M_FP_FAST`, `/fp:fast`), which §13.4 says is not
//! checked in this version.
//!
//! Tests that the implementation does not pass yet carry `#[ignore = "<work>"]` naming the work that
//! fixes their cause. Every test needs `gcc-15`, `clang`, `g++-15` and `clang++` on the PATH and fails
//! without them (Q-07).

use std::path::{Path, PathBuf};
use std::process::Command;

use onsa_tests::c;

/// The warnings every compile of generated C has (spec §13.4).
const STRICT: &[&str] = &["-Wall", "-Wextra", "-Werror", "-pedantic"];
const GCC: &str = "gcc-15";
const CLANG: &str = "clang";

fn need(programs: &[&str]) {
    for p in programs {
        c::require(p).unwrap_or_else(|e| panic!("{e}"));
    }
}

// ---------------------------------------------------------------------------------------------
// Packages
// ---------------------------------------------------------------------------------------------

/// A package that `onsa build` has written for the target `host`.
struct Built {
    out: PathBuf,
    files: Vec<String>,
}

impl Built {
    fn text(&self, name: &str) -> String {
        std::fs::read_to_string(self.out.join(name)).unwrap_or_else(|e| panic!("cannot read {name}: {e}"))
    }

    fn has(&self, name: &str) -> bool {
        self.files.iter().any(|f| f == name)
    }

    /// The name of the one `.c` file of the build.
    fn c_name(&self) -> String {
        let cs: Vec<&String> = self.files.iter().filter(|f| f.ends_with(".c")).collect();
        assert_eq!(cs.len(), 1, "one .c file expected in {:?}", self.files);
        cs[0].clone()
    }

    /// The public header of the package (`<prefix><package>.h`): the only `.h` that is neither
    /// `onsa.h` nor `onsa__runtime.h`.
    fn package_header(&self) -> String {
        let hs: Vec<&String> =
            self.files.iter().filter(|f| f.ends_with(".h") && *f != "onsa.h" && *f != "onsa__runtime.h").collect();
        assert_eq!(hs.len(), 1, "one package header expected in {:?}", self.files);
        hs[0].clone()
    }

    /// The compiler flags that `onsa build` reports for the target (`onsa_build.json`).
    fn cflags(&self) -> Vec<String> {
        let v: serde_json::Value = serde_json::from_str(&self.text("onsa_build.json")).unwrap();
        v["cflags"].as_array().expect("cflags").iter().map(|s| s.as_str().unwrap().to_string()).collect()
    }
}

fn build_dir(work: &Path, target: &str) -> Built {
    let out = work.join("out");
    let opts = onsa_driver::BuildOptions { target: target.into(), out: Some(out.clone()) };
    let report = match onsa_driver::build(work, &opts) {
        Ok(r) => r,
        Err(onsa_driver::BuildError::Usage(m)) => panic!("build: {m}"),
        Err(onsa_driver::BuildError::Diagnostics { sources, diagnostics }) => {
            panic!("build: {}", onsa_diag::to_text(&sources, &diagnostics))
        }
        Err(onsa_driver::BuildError::Internal { sources, error }) => panic!("build: {}", error.render(&sources)),
    };
    Built { out, files: report.files.clone() }
}

/// A package made of `files` (`onsa.toml` among them), built for `target`.
fn inline_package(tag: &str, files: &[(&str, &str)], target: &str) -> Built {
    let work = c::scratch_dir("onsa_test", tag);
    std::fs::create_dir_all(&work).unwrap();
    for (name, text) in files {
        std::fs::write(work.join(name), text).unwrap();
    }
    build_dir(&work, target)
}

/// The manifest of the `// onsa.toml` fragment at the head of a case file, without the tables of the
/// test (`[test]`, `[[test.host]]`).
fn fragment_manifest(text: &str) -> String {
    let mut lines = text.lines();
    assert_eq!(lines.next(), Some("// onsa.toml"), "a case file starts with the fragment");
    let mut keep = true;
    let mut out = String::new();
    for l in lines {
        let Some(rest) = l.strip_prefix("//") else { break };
        let body = rest.strip_prefix(' ').unwrap_or(rest);
        let t = body.trim();
        if t.starts_with('[') {
            keep = !(t == "[test]" || t.starts_with("[[test.") || t.starts_with("[test."));
        }
        if keep {
            out.push_str(body);
            out.push('\n');
        }
    }
    out
}

/// The case file (or package) `rel` of the repository, built for `target`.
fn case_package(tag: &str, rel: &str, target: &str) -> Built {
    let path = onsa_tests::case::repo_root().join(rel);
    if path.is_dir() {
        let out = c::scratch_dir("onsa_test", tag).join("out");
        let opts = onsa_driver::BuildOptions { target: target.into(), out: Some(out.clone()) };
        let report = match onsa_driver::build(&path, &opts) {
            Ok(r) => r,
            Err(onsa_driver::BuildError::Diagnostics { sources, diagnostics }) => {
                panic!("build: {}", onsa_diag::to_text(&sources, &diagnostics))
            }
            Err(_) => panic!("build of {rel} failed"),
        };
        return Built { out, files: report.files.clone() };
    }
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {rel}: {e}"));
    let manifest = fragment_manifest(&text);
    let name = manifest
        .lines()
        .find_map(|l| l.trim().strip_prefix("name = \"").and_then(|r| r.strip_suffix('"')))
        .expect("a package name")
        .to_string();
    let source_name = format!("{name}.onsa");
    inline_package(tag, &[("onsa.toml", manifest.as_str()), (source_name.as_str(), text.as_str())], target)
}

// ---------------------------------------------------------------------------------------------
// Compilers
// ---------------------------------------------------------------------------------------------

struct Run {
    ok: bool,
    stdout: String,
    stderr: String,
}

fn run(program: &str, args: &[&str], dir: &Path) -> Run {
    let o = Command::new(program)
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap_or_else(|e| panic!("cannot run {program}: {e}"));
    Run {
        ok: o.status.success(),
        stdout: String::from_utf8_lossy(&o.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&o.stderr).into_owned(),
    }
}

/// `program` on the `.c` of the build with `flags`, as a syntax check, under the warnings of §13.4.
fn syntax(b: &Built, program: &str, flags: &[&str]) -> Run {
    let c_name = b.c_name();
    let mut args: Vec<&str> = flags.to_vec();
    args.extend_from_slice(STRICT);
    args.extend_from_slice(&["-I.", "-fsyntax-only", &c_name]);
    run(program, &args, &b.out)
}

fn describe(program: &str, flags: &[&str], r: &Run) -> String {
    format!("{program} {}:\n{}", flags.join(" "), c::head(&r.stderr))
}

fn assert_compiles(b: &Built, program: &str, flags: &[&str]) {
    let r = syntax(b, program, flags);
    assert!(r.ok, "expected to compile: {}", describe(program, flags, &r));
}

/// The compile stops, and the message names every flag in `names`.
fn assert_stops(b: &Built, program: &str, flags: &[&str], names: &[&str]) {
    let r = syntax(b, program, flags);
    assert!(!r.ok, "expected an #error, but it compiled: {program} {}", flags.join(" "));
    for n in names {
        assert!(
            r.stderr.contains(n),
            "the message of {program} {} does not name `{n}`:\n{}",
            flags.join(" "),
            c::head(&r.stderr)
        );
    }
}

/// A directory with a `float.h` that sets `FLT_EVAL_METHOD` to `value` after the real one (the pragma keeps
/// `-pedantic` quiet about the GCC extension `#include_next`).
fn eval_method_shim(tag: &str, value: i32) -> PathBuf {
    let dir = c::scratch_dir("onsa_test", tag);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("float.h"),
        format!("#pragma GCC system_header\n#include_next <float.h>\n#undef FLT_EVAL_METHOD\n#define FLT_EVAL_METHOD ({value})\n"),
    )
    .unwrap();
    dir
}

// ---------------------------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------------------------

fn manifest(name: &str, prefix: &str, fns: &str, target: &str, panic: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nedition = \"2026\"\n\n[export]\nprefix = \"{prefix}\"\nfns = [{fns}]\n\n\
         [targets.{target}]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"{panic}\"\nprovides = []\n"
    )
}

/// One exported F32 function, a product and a sum.
fn fixture(tag: &str) -> Built {
    let m = manifest("fx", "fx_", "\"fx.add\"", "host", "poison");
    inline_package(
        tag,
        &[("onsa.toml", &m), ("fx.onsa", "pub fn add(a: F32, b: F32) -> F32 {\n  let p = a * b\n  p + a\n}\n")],
        "host",
    )
}

// ---------------------------------------------------------------------------------------------
// The public and the internal header (§14.2, S-53 split in W2-09)
// ---------------------------------------------------------------------------------------------

#[test]
fn a_source_build_writes_the_public_and_the_internal_runtime_headers() {
    let b = fixture("hdr_files");
    assert!(b.has("onsa.h"), "{:?}", b.files);
    assert!(b.has("onsa__runtime.h"), "the internal runtime header is written for kind = \"source\": {:?}", b.files);
    assert!(b.text(&b.c_name()).contains("onsa__runtime.h"), "the generated .c reads the internal header");
    for public in ["onsa.h".to_string(), b.package_header()] {
        let t = b.text(&public);
        assert!(!t.contains("onsa__runtime.h"), "{public} (a header of the host) must not read the internal header");
    }
}

#[test]
fn onsa_h_does_not_depend_on_the_package_or_the_target() {
    let a = fixture("hdr_same_a");
    let m = manifest("other", "zz_", "\"other.f\"", "fw", "reset");
    let b = inline_package(
        "hdr_same_b",
        &[("onsa.toml", &m), ("other.onsa", "pub fn f(x: U32) -> U32 {\n  x + 1\n}\n")],
        "fw",
    );
    assert_eq!(a.text("onsa.h"), b.text("onsa.h"), "onsa.h is the same for every package and target (§14.2)");
}

#[test]
fn onsa_h_holds_what_a_host_uses_and_nothing_of_the_runtime() {
    let b = fixture("hdr_content");
    let t = b.text("onsa.h");
    assert!(t.contains("ONSA_ABI_VERSION"), "the ABI version is public");
    assert!(t.contains("onsa_param_info"), "the parameter info type is public");
    // §14.2: the internal runtime (helpers, setjmp, the FLT_EVAL_METHOD check, the C11 syntax) is in the
    // internal header, which only the generated .c reads.
    for internal in [
        "setjmp",
        "FLT_EVAL_METHOD",
        "__FAST_MATH__",
        "__FINITE_MATH_ONLY__",
        "#pragma",
        "_Static_assert",
        "_Noreturn",
        "_Thread_local",
        "_Generic",
        "_Atomic",
    ] {
        assert!(!t.contains(internal), "onsa.h must not hold `{internal}` (§14.2)");
    }
    let r = b.text("onsa__runtime.h");
    assert!(r.contains("FLT_EVAL_METHOD"), "the internal header holds the FLT_EVAL_METHOD check (§13.4)");
    assert!(r.contains("__FAST_MATH__") && r.contains("__FINITE_MATH_ONLY__"), "and the fast-math checks");
    assert!(
        r.contains("ONSA_ALLOW_INEXACT_FP") && r.contains("ONSA_FP_CONTRACT_OFF"),
        "and the two defines of the host"
    );
}

/// A host that reads the public headers only builds in every mode and with every float flag: the
/// `#error` checks are not in them (S-54: the reason for the split).
#[test]
fn a_host_that_reads_the_public_headers_only_builds_in_every_mode() {
    need(&[GCC, CLANG, "g++-15", "clang++"]);
    let b = fixture("hdr_host");
    std::fs::write(
        b.out.join("host.c"),
        "#include \"fx_fx.h\"\nfloat host_call(float a, float b) { return fx_add(a, b); }\n",
    )
    .unwrap();
    std::fs::write(
        b.out.join("host.cpp"),
        "#include \"fx_fx.h\"\nfloat host_call(float a, float b) { return fx_add(a, b); }\n",
    )
    .unwrap();
    let c_flags: &[&[&str]] = &[
        &["-std=gnu11"],
        &["-std=gnu99", "-ffast-math"],
        &["-std=c99"],
        &["-std=c11", "-ffinite-math-only"],
        &["-std=gnu11", "-O2"],
    ];
    for cc in [GCC, CLANG] {
        for flags in c_flags {
            let mut args: Vec<&str> = flags.to_vec();
            args.extend_from_slice(STRICT);
            args.extend_from_slice(&["-I.", "-fsyntax-only", "host.c"]);
            let r = run(cc, &args, &b.out);
            assert!(r.ok, "host.c must build: {}", describe(cc, flags, &r));
        }
    }
    let cxx_flags: &[&[&str]] =
        &[&["-std=c++11"], &["-std=gnu++14", "-ffast-math"], &["-std=c++17", "-ffinite-math-only"]];
    for cxx in ["g++-15", "clang++"] {
        for flags in cxx_flags {
            let mut args: Vec<&str> = flags.to_vec();
            args.extend_from_slice(STRICT);
            args.extend_from_slice(&["-I.", "-fsyntax-only", "host.cpp"]);
            let r = run(cxx, &args, &b.out);
            assert!(r.ok, "host.cpp must build: {}", describe(cxx, flags, &r));
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The #error checks (§13.4, S-54)
// ---------------------------------------------------------------------------------------------

/// `-std=c11`, `-ffp-contract=off` and `-fno-fast-math` are the flags `onsa build` passes (§13.4): the
/// positive control of every check below.
const OK_FLAGS: &[&str] = &["-std=c11", "-ffp-contract=off", "-fno-fast-math"];

#[test]
fn the_flags_that_onsa_build_passes_compile_without_a_warning() {
    need(&[GCC, CLANG]);
    let b = fixture("err_control");
    assert_compiles(&b, GCC, OK_FLAGS);
    assert_compiles(&b, CLANG, OK_FLAGS);
    assert_compiles(&b, GCC, &["-std=c11", "-O2"]);
    assert_compiles(&b, GCC, &["-std=c17"]);
    assert_compiles(&b, CLANG, &["-std=c11", "-O2"]);
}

#[test]
fn gcc_in_the_gnu_mode_without_the_define_is_an_error() {
    need(&[GCC]);
    let b = fixture("err_gnu");
    for std in ["-std=gnu11", "-std=gnu17"] {
        assert_stops(&b, GCC, &[std], &["ONSA_FP_CONTRACT_OFF", "-ffp-contract=off"]);
        // the flag alone is not enough: GCC defines nothing for it, the define says the host passed it
        assert_stops(&b, GCC, &[std, "-ffp-contract=off"], &["ONSA_FP_CONTRACT_OFF"]);
        assert_stops(&b, GCC, &[std, "-O2"], &["ONSA_FP_CONTRACT_OFF"]);
    }
}

#[test]
fn gcc_in_the_gnu_mode_with_the_define_compiles() {
    need(&[GCC]);
    let b = fixture("err_gnu_define");
    assert_compiles(&b, GCC, &["-std=gnu11", "-ffp-contract=off", "-DONSA_FP_CONTRACT_OFF"]);
    assert_compiles(&b, GCC, &["-std=gnu17", "-ffp-contract=off", "-DONSA_FP_CONTRACT_OFF", "-O2"]);
}

#[test]
fn gcc_in_an_iso_mode_needs_no_define() {
    need(&[GCC]);
    let b = fixture("err_iso");
    for std in ["-std=c11", "-std=c17", "-std=c2x"] {
        assert_compiles(&b, GCC, &[std]);
        assert_compiles(&b, GCC, &[std, "-O2"]);
    }
}

#[test]
fn clang_in_the_gnu_mode_compiles_because_the_pragma_works() {
    need(&[CLANG]);
    let b = fixture("err_clang_gnu");
    assert_compiles(&b, CLANG, &["-std=gnu11"]);
    assert_compiles(&b, CLANG, &["-std=gnu17", "-O2"]);
}

#[test]
fn fast_math_is_an_error() {
    need(&[GCC, CLANG]);
    let b = fixture("err_fast");
    for cc in [GCC, CLANG] {
        assert_stops(&b, cc, &["-std=c11", "-ffast-math"], &["-fno-fast-math"]);
        // the fast-math check does not hide behind the contraction check
        assert_stops(
            &b,
            cc,
            &["-std=gnu11", "-ffp-contract=off", "-DONSA_FP_CONTRACT_OFF", "-ffast-math"],
            &["-fno-fast-math"],
        );
    }
    assert_stops(&b, GCC, &["-std=c11", "-Ofast"], &["-fno-fast-math"]);
}

#[test]
fn finite_math_only_is_an_error() {
    need(&[GCC, CLANG]);
    let b = fixture("err_finite");
    for cc in [GCC, CLANG] {
        let r = syntax(&b, cc, &["-std=c11", "-ffinite-math-only"]);
        assert!(!r.ok, "{cc} -ffinite-math-only must stop");
        assert!(
            r.stderr.contains("-fno-finite-math-only") || r.stderr.contains("-fno-fast-math"),
            "the message of {cc} names the flag to keep:\n{}",
            c::head(&r.stderr)
        );
    }
}

#[test]
fn an_evaluation_method_that_is_not_zero_is_an_error() {
    need(&[GCC, CLANG]);
    let b = fixture("err_eval");
    for value in [1, 2, -1] {
        let shim = eval_method_shim(&format!("err_eval_shim_{}", value + 1), value);
        let dir = shim.to_string_lossy().into_owned();
        for cc in [GCC, CLANG] {
            let flags = ["-std=c11", "-ffp-contract=off", "-I", &dir];
            let r = syntax(&b, cc, &flags);
            assert!(!r.ok, "FLT_EVAL_METHOD {value} must stop {cc}");
            assert!(r.stderr.contains("FLT_EVAL_METHOD"), "the message names FLT_EVAL_METHOD:\n{}", c::head(&r.stderr));
            assert!(
                r.stderr.to_lowercase().contains("sse"),
                "the message names the SSE flags (§13.4):\n{}",
                c::head(&r.stderr)
            );
        }
    }
    // the same shim with 0 is the real value: the control
    let shim = eval_method_shim("err_eval_shim_zero", 0);
    let dir = shim.to_string_lossy().into_owned();
    for cc in [GCC, CLANG] {
        assert_compiles(&b, cc, &["-std=c11", "-ffp-contract=off", "-I", &dir]);
    }
}

#[test]
fn the_allow_define_removes_every_check() {
    need(&[GCC, CLANG]);
    let b = fixture("err_allow");
    let dir = eval_method_shim("err_allow_shim", 2).to_string_lossy().into_owned();
    // S-289 (decided 2026-10-08): the promise of no warning is for the builds with the flags of §13.4; a build
    // with ONSA_ALLOW_INEXACT_FP is promised to compile (no error), and may warn (under -ffast-math Clang warns
    // about the NaN and the infinity that the runtime names, -Wnan-infinity-disabled). So both compilers are
    // run without -Werror, each condition alone and all of them at once.
    let each: &[&[&str]] = &[
        &["-std=gnu11"],
        &["-std=c11", "-ffast-math"],
        &["-std=c11", "-ffinite-math-only"],
        &["-std=c11", "-I", &dir],
        &["-std=gnu11", "-Ofast", "-I", &dir],
    ];
    let clang_each: &[&[&str]] = &[
        &["-std=gnu11"],
        &["-std=c11", "-ffast-math"],
        &["-std=c11", "-ffinite-math-only"],
        &["-std=c11", "-I", &dir],
    ];
    for (cc, flags) in each.iter().map(|f| (GCC, f)).chain(clang_each.iter().map(|f| (CLANG, f))) {
        let c_name = b.c_name();
        let mut args: Vec<&str> = flags.to_vec();
        args.extend_from_slice(&[
            "-DONSA_ALLOW_INEXACT_FP",
            "-Wall",
            "-Wextra",
            "-pedantic",
            "-I.",
            "-fsyntax-only",
            &c_name,
        ]);
        let r = run(cc, &args, &b.out);
        assert!(r.ok, "the define removes the checks: {}", describe(cc, flags, &r));
    }
}

// ---------------------------------------------------------------------------------------------
// The pragma, and the comment of the flags
// ---------------------------------------------------------------------------------------------

#[test]
fn gcc_is_given_no_stdc_pragma() {
    need(&[GCC]);
    let b = fixture("pragma_gcc");
    let c_name = b.c_name();
    let modes: &[&[&str]] = &[
        &["-std=c11"],
        &["-std=gnu11", "-ffp-contract=off", "-DONSA_FP_CONTRACT_OFF"],
        &["-std=gnu11", "-ffast-math", "-DONSA_ALLOW_INEXACT_FP"],
    ];
    for flags in modes {
        let mut args: Vec<&str> = flags.to_vec();
        args.extend_from_slice(&["-I.", "-E", &c_name]);
        let r = run(GCC, &args, &b.out);
        assert!(r.ok, "{}", describe(GCC, flags, &r));
        assert!(
            !r.stdout.contains("#pragma STDC"),
            "GCC ignores the STDC pragma and warns about it (-Wunknown-pragmas): {flags:?}"
        );
        assert!(!r.stdout.contains("FP_CONTRACT"), "no FP_CONTRACT pragma for GCC: {flags:?}");
    }
    // and with the warning on, nothing is reported
    assert_compiles(&b, GCC, &["-std=c11", "-Wunknown-pragmas"]);
}

#[test]
fn clang_is_given_the_stdc_pragma() {
    need(&[CLANG]);
    let b = fixture("pragma_clang");
    let c_name = b.c_name();
    let r = run(CLANG, &["-std=c11", "-I.", "-E", &c_name], &b.out);
    assert!(r.ok, "{}", c::head(&r.stderr));
    assert!(
        r.stdout.contains("#pragma STDC FP_CONTRACT OFF"),
        "Clang knows the STDC pragma, and S-54 withholds it from GCC only"
    );
}

/// The text of the comments at the head of a C file, before its first token.
fn leading_comments(text: &str) -> String {
    let mut rest = text;
    let mut out = String::new();
    loop {
        rest = rest.trim_start();
        if let Some(r) = rest.strip_prefix("/*") {
            let end = r.find("*/").expect("a block comment is closed");
            out.push_str(&r[..end]);
            out.push('\n');
            rest = &r[end + 2..];
        } else if let Some(r) = rest.strip_prefix("//") {
            let end = r.find('\n').unwrap_or(r.len());
            out.push_str(&r[..end]);
            out.push('\n');
            rest = &r[end..];
        } else {
            return out;
        }
    }
}

#[test]
fn the_leading_comment_helper_reads_both_comment_forms() {
    let t = "/* one\n * two -std=c11 */\n// three\n\n#define X 1 /* not leading */\n";
    let h = leading_comments(t);
    assert!(h.contains("one") && h.contains("-std=c11") && h.contains("three"), "{h}");
    assert!(!h.contains("not leading"), "{h}");
}

#[test]
fn the_generated_c_starts_with_the_flags_it_needs() {
    let b = fixture("flags_comment");
    let text = b.text(&b.c_name());
    // the leading comments: every comment (block or line) before the first token of the file
    let head = leading_comments(&text);
    assert!(!head.is_empty(), "the file starts with a comment");
    for flag in ["-std=c11", "-ffp-contract=off", "-fno-fast-math"] {
        assert!(head.contains(flag), "the first comment of the .c must list `{flag}` (§13.4):\n{head}");
        assert!(b.cflags().iter().any(|f| f == flag), "onsa build passes `{flag}`: {:?}", b.cflags());
    }
}

// ---------------------------------------------------------------------------------------------
// Warnings
// ---------------------------------------------------------------------------------------------

#[test]
fn the_vector_fixture_compiles_without_a_warning_at_every_level() {
    need(&[GCC, CLANG]);
    // The package of the test vectors holds every integer and float operation and every conversion:
    // the `narrow_*` range checks (R-145), the `match` of every `Option` (R-145), the helpers of the
    // runtime (`-Wtype-limits`, R-67), the comparisons (R-142).
    let b = case_package("warn_vectors", "tests/vectors/fixture/scalar", "host");
    let c_name = b.c_name();
    let obj = b.out.join("w.o");
    let obj = obj.to_string_lossy().into_owned();
    for (cc, levels) in [(GCC, ["-O0", "-O2", "-O3"]), (CLANG, ["-O0", "-O1", "-O2"])] {
        for level in levels {
            let mut args: Vec<&str> = vec!["-std=c11", "-ffp-contract=off", "-fno-fast-math", level];
            args.extend_from_slice(STRICT);
            args.extend_from_slice(&[
                "-Wtype-limits",
                "-Wunknown-pragmas",
                "-Wsign-compare",
                "-I.",
                "-c",
                &c_name,
                "-o",
                &obj,
            ]);
            let r = run(cc, &args, &b.out);
            assert!(r.ok, "{cc} {level} on the vector fixture:\n{}", c::head(&r.stderr));
        }
    }
}

/// Whether a condition `if (…)` / `while (…)` of `text` is wrapped by a second pair of parentheses.
fn doubly_wrapped_conditions(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    for kw in ["if (", "while ("] {
        let mut from = 0;
        while let Some(pos) = text[from..].find(kw) {
            let start = from + pos;
            from = start + kw.len();
            // a keyword, not the end of an identifier such as `elif (` or `onsa_if (`
            if start > 0 {
                let prev = bytes[start - 1];
                if prev.is_ascii_alphanumeric() || prev == b'_' {
                    continue;
                }
            }
            let open = start + kw.len() - 1;
            let Some(close) = matching(bytes, open) else { continue };
            let inner = &text[open + 1..close];
            if inner.starts_with('(') && matching(inner.as_bytes(), 0) == Some(inner.len() - 1) {
                found.push(text[start..=close].lines().next().unwrap_or("").to_string());
            }
        }
    }
    found
}

fn matching(bytes: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (i, &ch) in bytes.iter().enumerate().skip(open) {
        match ch {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

#[test]
fn the_condition_helper_finds_a_second_pair() {
    assert_eq!(doubly_wrapped_conditions("  if ((a == b)) {\n"), vec!["if ((a == b))".to_string()]);
    assert_eq!(doubly_wrapped_conditions("  while ((y != UINT32_C(0))) {\n").len(), 1);
    assert!(doubly_wrapped_conditions("  if ((a == b) && (c == d)) {\n").is_empty());
    assert!(doubly_wrapped_conditions("  if ((uint8_t)x) {\n").is_empty());
    assert!(doubly_wrapped_conditions("  if (a == b) {\n").is_empty());
    assert!(doubly_wrapped_conditions("  } else if (onsa_x) {\n").is_empty());
}

#[test]
fn a_condition_has_no_second_pair_of_parentheses() {
    need(&[CLANG]);
    let m = manifest(
        "cond",
        "cd_",
        "\"cond.eq\", \"cond.ne\", \"cond.lt\", \"cond.both\", \"cond.count\"",
        "host",
        "poison",
    );
    let src = "\
pub fn eq(a: I32, b: I32) -> I32 {
  if a == b {
    1
  } else {
    0
  }
}

pub fn ne(a: U8, b: U8) -> U8 {
  if a != b {
    a
  } else {
    b
  }
}

pub fn lt(a: I64, b: I64) -> I64 {
  if a < b {
    b
  } else if a == b {
    0
  } else {
    a
  }
}

pub fn both(a: I32, b: I32, c: I32, d: I32) -> I32 {
  if (a == b) && (c == d) {
    1
  } else {
    0
  }
}

pub fn count(a: I32, stop: I32) -> I32 {
  var x: I32 = a
  var n: I32 = 0
  while x != stop {
    x = x + 1
    n = n + 1
  }
  n
}
";
    let b = inline_package("cond", &[("onsa.toml", &m), ("cond.onsa", src)], "host");
    let text = b.text(&b.c_name());
    let bad = doubly_wrapped_conditions(&text);
    assert!(
        bad.is_empty(),
        "a condition with a second pair of parentheses (clang -Wparentheses-equality, R-142): {bad:?}"
    );
    // the larger sample: the vector fixture
    let v = case_package("cond_vectors", "tests/vectors/fixture/scalar", "host");
    let bad = doubly_wrapped_conditions(&v.text(&v.c_name()));
    assert!(bad.is_empty(), "{} conditions with a second pair, the first: {:?}", bad.len(), bad.first());
    let c_name = b.c_name();
    let r = run(
        CLANG,
        &["-std=c11", "-Wparentheses", "-Wparentheses-equality", "-Werror", "-I.", "-fsyntax-only", &c_name],
        &b.out,
    );
    assert!(r.ok, "{}", c::head(&r.stderr));
}

#[test]
fn a_poison_export_wrapper_has_no_wclobbered_at_any_level() {
    need(&[GCC]);
    // loops and variables of every width inlined into the wrapper that calls setjmp (R-167)
    let b = case_package("clobber", "tests/spec/c_runtime/c_clobber.onsa", "host");
    let c_name = b.c_name();
    let obj = b.out.join("w.o");
    let obj = obj.to_string_lossy().into_owned();
    for level in ["-O0", "-O1", "-O2", "-O3", "-Os", "-Og"] {
        // Only the clobber warning is looked for, so that the other causes the other tests name (the
        // pragma, the type limits) do not hide it: no -Werror here, the report is read.
        let args = [
            "-std=c11",
            "-ffp-contract=off",
            "-fno-fast-math",
            level,
            "-Wall",
            "-Wextra",
            "-pedantic",
            "-Wclobbered",
            "-I.",
            "-c",
            &c_name,
            "-o",
            &obj,
        ];
        let r = run(GCC, &args, &b.out);
        assert!(r.ok, "gcc {level}:\n{}", c::head(&r.stderr));
        let clobbered: Vec<&str> = r.stderr.lines().filter(|l| l.contains("clobbered")).collect();
        assert!(
            clobbered.is_empty(),
            "gcc {level}: a poison wrapper keeps a variable across longjmp (R-167): {} warnings, the first: {}",
            clobbered.len(),
            clobbered[0]
        );
    }
}

// ---------------------------------------------------------------------------------------------
// The results (§13.4: no fused multiply-add; §15.5; S-207)
// ---------------------------------------------------------------------------------------------

/// Compile the `.c` of the build with `driver` (a C file) under `flags`, run it, and give its lines.
fn run_driver(b: &Built, driver: &str, program: &str, flags: &[&str]) -> Vec<String> {
    std::fs::write(b.out.join("driver.c"), driver).unwrap();
    let c_name = b.c_name();
    let mut args: Vec<&str> = flags.to_vec();
    args.extend_from_slice(&["-I.", "driver.c", &c_name, "-lm", "-o", "driver"]);
    let r = run(program, &args, &b.out);
    assert!(r.ok, "{}", describe(program, flags, &r));
    let o = Command::new(b.out.join("driver")).current_dir(&b.out).output().unwrap();
    assert!(o.status.success(), "driver ({program} {}) ended with {}", flags.join(" "), o.status);
    String::from_utf8_lossy(&o.stdout).lines().map(str::to_string).collect()
}

/// The driver of c_fp_contract.onsa: the bits of each result. With a = 1 + 2^-13, p = 1 + 2^-12 and
/// c = -p, the product a * a is 1 + 2^-12 + 2^-26 and rounds to p in F32, so every row is +0.0 when the
/// product is rounded first and 2^-26 (or -2^-26) when a fused multiply-add computes it.
const CONTRACT_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "cfc_c_fp_contract.h"
static uint32_t bits32(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static uint64_t bits64(double f) { uint64_t u; memcpy(&u, &f, 8); return u; }
int main(void) {
  float x = 1.0001220703125f, p = 1.000244140625f;
  double y = 1.0000000074505806, q = 1.0000000149011612;
  printf("muladd %08x\n", (unsigned)bits32(cfc_muladd_f32(x, x, -p)));
  printf("mulsub %08x\n", (unsigned)bits32(cfc_mulsub_f32(x, x, p)));
  printf("nmuladd %08x\n", (unsigned)bits32(cfc_nmuladd_f32(x, x, p)));
  printf("negmul_add %08x\n", (unsigned)bits32(cfc_negmul_add_f32(x, x, p)));
  printf("dot2 %08x\n", (unsigned)bits32(cfc_dot2_f32(x, x, -p, 1.0f)));
  printf("via_helper %08x\n", (unsigned)bits32(cfc_via_helper_f32(x, x, -p)));
  printf("mac_loop %08x\n", (unsigned)bits32(cfc_mac_loop_f32(x, x, -p, 1)));
  printf("zero_sign %08x\n", (unsigned)cfc_zero_sign_bits_f32(8.271806125530277e-25f, -8.271806125530277e-25f));
  printf("muladd64 %016llx\n", (unsigned long long)bits64(cfc_muladd_f64(y, y, -q)));
  printf("mulsub64 %016llx\n", (unsigned long long)bits64(cfc_mulsub_f64(y, y, q)));
  return 0;
}
"#;

const CONTRACT_NAMES: [&str; 10] = [
    "muladd",
    "mulsub",
    "nmuladd",
    "negmul_add",
    "dot2",
    "via_helper",
    "mac_loop",
    "zero_sign",
    "muladd64",
    "mulsub64",
];

/// The flag sets under which the spec promises the two-rounding results (§13.4): the ISO mode of GCC
/// needs nothing, the GNU mode needs the flag and the define, and Clang is held by the pragma.
fn strict_flag_sets() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        (GCC, vec!["-std=c11", "-O2"]),
        (GCC, vec!["-std=c17", "-O3"]),
        (GCC, vec!["-std=gnu11", "-O2", "-ffp-contract=off", "-DONSA_FP_CONTRACT_OFF"]),
        (GCC, vec!["-std=c11", "-O3", "-ffp-contract=off", "-fno-fast-math"]),
        (CLANG, vec!["-std=c11", "-O2"]),
        (CLANG, vec!["-std=gnu11", "-O2"]),
        (CLANG, vec!["-std=c11", "-O3", "-ffp-contract=off"]),
    ]
}

#[test]
fn the_results_are_the_two_rounding_results_under_every_supported_flag_set() {
    need(&[GCC, CLANG]);
    let b = case_package("fma_strict", "tests/spec/c_runtime/c_fp_contract.onsa", "host");
    for (cc, flags) in strict_flag_sets() {
        let lines = run_driver(&b, CONTRACT_DRIVER, cc, &flags);
        assert_eq!(lines.len(), CONTRACT_NAMES.len(), "{lines:?}");
        for (line, name) in lines.iter().zip(CONTRACT_NAMES) {
            let (n, value) = line.split_once(' ').unwrap();
            assert_eq!(n, name);
            let zero = if name.ends_with("64") { "0000000000000000" } else { "00000000" };
            assert_eq!(
                value,
                zero,
                "{name} under {cc} {}: a fused multiply-add changed the result (expected +0.0)",
                flags.join(" ")
            );
        }
    }
}

/// c_fp_relaxed.onsa: the strict functions around the relaxed ones.
const RELAXED_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "cfr_c_fp_relaxed.h"
static uint32_t bits32(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static uint64_t bits64(double f) { uint64_t u; memcpy(&u, &f, 8); return u; }
int main(void) {
  float x = 1.0001220703125f, p = 1.000244140625f;
  double y = 1.0000000074505806, q = 1.0000000149011612;
  printf("before %08x\n", (unsigned)bits32(cfr_strict_before_f32(x, x, -p)));
  printf("after %08x\n", (unsigned)bits32(cfr_strict_after_f32(x, x, -p)));
  printf("loop_after %08x\n", (unsigned)bits32(cfr_strict_loop_after_f32(x, x, -p, 1)));
  printf("after64 %016llx\n", (unsigned long long)bits64(cfr_strict_after_f64(y, y, -q)));
  /* the relaxed functions: values that every allowed rewriting leaves alone */
  printf("rel %08x\n", (unsigned)bits32(cfr_rel_muladd_f32(2.0f, 3.0f, 1.0f)));
  return 0;
}
"#;

#[test]
fn a_relaxed_function_does_not_loosen_the_strict_functions_around_it() {
    need(&[GCC, CLANG]);
    let b = case_package("fma_relaxed", "tests/spec/c_runtime/c_fp_relaxed.onsa", "host");
    for (cc, flags) in strict_flag_sets() {
        let lines = run_driver(&b, RELAXED_DRIVER, cc, &flags);
        let want =
            ["before 00000000", "after 00000000", "loop_after 00000000", "after64 0000000000000000", "rel 40e00000"];
        assert_eq!(lines, want, "under {cc} {}", flags.join(" "));
    }
}

/// S-207: GCC reassociation in a function (`optimize("associative-math")`) also removes `x + 0.0` and
/// `(a + b) - b`, which §15.5 does not allow, so GCC gets the contraction only. The results of these
/// functions under GCC are the strict ones.
const REASSOC_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "ra_reassoc.h"
static uint32_t bits32(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
int main(void) {
  /* (1.0 + 1e8) - 1e8: 1e8 + 1 rounds to 1e8 in F32 (the spacing there is 8), so the strict result is 0.0 */
  printf("sub_back %08x\n", (unsigned)bits32(ra_rel_sub_back(1.0f, 100000000.0f)));
  /* -0.0 + 0.0 is +0.0 */
  printf("add_zero %08x\n", (unsigned)ra_rel_add_zero_bits(-0.0f));
  /* ((1e8 + 1) + -1e8) + 1: 1e8 + 1 = 1e8, 1e8 + -1e8 = 0, 0 + 1 = 1.0; a reassociation gives 2.0 */
  printf("sum4 %08x\n", (unsigned)bits32(ra_rel_sum4(100000000.0f, 1.0f, -100000000.0f, 1.0f)));
  /* the same shapes in a strict function: the control */
  printf("strict_sub_back %08x\n", (unsigned)bits32(ra_strict_sub_back(1.0f, 100000000.0f)));
  return 0;
}
"#;

const REASSOC_SRC: &str = "\
@fp(relaxed)
pub fn rel_sub_back(a: F32, b: F32) -> F32 {
  (a + b) - b
}

@fp(relaxed)
pub fn rel_add_zero_bits(x: F32) -> U32 {
  (x + 0.0).to_bits()
}

@fp(relaxed)
pub fn rel_sum4(a: F32, b: F32, c: F32, d: F32) -> F32 {
  ((a + b) + c) + d
}

pub fn strict_sub_back(a: F32, b: F32) -> F32 {
  (a + b) - b
}
";

fn reassoc_package(tag: &str) -> Built {
    let m = manifest(
        "reassoc",
        "ra_",
        "\"reassoc.rel_sub_back\", \"reassoc.rel_add_zero_bits\", \"reassoc.rel_sum4\", \"reassoc.strict_sub_back\"",
        "host",
        "poison",
    );
    inline_package(tag, &[("onsa.toml", &m), ("reassoc.onsa", REASSOC_SRC)], "host")
}

#[test]
fn gcc_does_not_reassociate_in_a_relaxed_function() {
    need(&[GCC]);
    let b = reassoc_package("reassoc_gcc");
    // the flags that `onsa build` reports, at -O3, and the ISO mode without them
    let mut build_flags: Vec<String> = b.cflags();
    build_flags.push("-O3".into());
    let build_flags: Vec<&str> = build_flags.iter().map(String::as_str).collect();
    for flags in [build_flags, vec!["-std=c11", "-O3"], vec!["-std=c11", "-O2", "-ffp-contract=off"]] {
        let lines = run_driver(&b, REASSOC_DRIVER, GCC, &flags);
        let want = ["sub_back 00000000", "add_zero 00000000", "sum4 3f800000", "strict_sub_back 00000000"];
        assert_eq!(lines, want, "gcc {} (S-207: GCC gets the contraction only)", flags.join(" "));
    }
}

/// The attribute or pragma of a relaxed function is not fixed by the spec; what it must not be is
/// fixed: no GCC reassociation, no assumption about NaN, infinity or the sign of zero (§15.5, S-207).
/// Read: every line of the generated files that holds `optimize`, `pragma` or `__attribute__`, but the
/// `#error` lines; a `no-` form of a flag is the safe direction and is taken out first.
#[test]
fn a_relaxed_function_gets_no_flag_beyond_the_contraction() {
    let b = reassoc_package("reassoc_text");
    let mut lines: Vec<String> = Vec::new();
    for f in b.files.iter().filter(|f| f.ends_with(".c") || f.ends_with(".h")) {
        for l in b.text(f).lines() {
            if (l.contains("optimize") || l.contains("pragma") || l.contains("__attribute__")) && !l.contains("#error")
            {
                lines.push(l.to_string());
            }
        }
    }
    for line in lines {
        let mut l = line.clone();
        for safe in [
            "no-associative-math",
            "no-unsafe-math-optimizations",
            "no-reciprocal-math",
            "no-fast-math",
            "no-finite-math-only",
            "signed-zeros=",
        ] {
            l = l.replace(safe, "");
        }
        for banned in [
            "associative-math",
            "unsafe-math",
            "reciprocal-math",
            "no-signed-zeros",
            "finite-math-only",
            "Ofast",
            "cx-limited-range",
            "fast-math",
        ] {
            assert!(!l.contains(banned), "`{banned}` in a function attribute or pragma of the generated C: {line}");
        }
        // Clang's own pragma for a relaxed function names reassociation (S-54); GCC's text must not
        if l.contains("optimize") {
            assert!(!l.contains("reassoc"), "GCC reassociation in an optimize attribute or pragma: {line}");
        }
    }
}

/// With the define the build may be fused (`-ffp-contract=fast`); the program still runs and gives one
/// of the two numbers (the guarantee of the bits does not apply, §13.4).
#[test]
fn a_build_with_the_allow_define_runs() {
    need(&[GCC]);
    let b = case_package("fma_allow", "tests/spec/c_runtime/c_fp_contract.onsa", "host");
    let lines = run_driver(&b, CONTRACT_DRIVER, GCC, &["-std=gnu11", "-Ofast", "-DONSA_ALLOW_INEXACT_FP"]);
    assert_eq!(lines.len(), CONTRACT_NAMES.len());
    let first = lines[0].split_once(' ').unwrap().1;
    assert!(first == "00000000" || first == "32800000", "muladd is +0.0 or 2^-26 (0x32800000): {first}");
}

// ---------------------------------------------------------------------------------------------
// A guard on the fixtures this file builds
// ---------------------------------------------------------------------------------------------

#[test]
fn the_fragment_helper_keeps_the_package_and_drops_the_test_tables() {
    let t = "// onsa.toml\n// [package]\n// name = \"x\"\n// edition = \"2026\"\n//\n// [export]\n// fns = [\n//   \"x.f\",\n// ]\n//\n// [targets.host]\n// kind = \"source\"\n//\n// [test]\n// mode = \"test\"\n//\n// [[test.host]]\n// name = \"n\"\n// steps = [\n//   { call = \"fn\" },\n// ]\n\npub fn f() -> U32 { 1 }\n";
    let m = fragment_manifest(t);
    assert!(m.contains("[package]") && m.contains("[export]") && m.contains("[targets.host]"), "{m}");
    assert!(m.contains("\"x.f\","), "{m}");
    assert!(!m.contains("[test]") && !m.contains("test.host") && !m.contains("steps"), "{m}");
    let parsed: toml::Value = toml::from_str(&m).unwrap();
    assert_eq!(parsed["package"]["name"].as_str(), Some("x"));
}
