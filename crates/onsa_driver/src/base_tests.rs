//! W5-18: an analysis that continues the base of std is the fresh analysis of
//! the package (the diagnostics in their order, the defs, the exports and the
//! Core), on cases drawn with a fixed seed and on inputs made for the borders
//! of the stages; and a check continues the base, but where it falls back.

use std::path::{Path, PathBuf};
use std::time::Instant;

use super::*;

/// The cases drawn from `tests/spec`.
const DRAWN: usize = 40;
const SEED: u64 = 0x5eed_0518;

const MANIFEST: &str = "[package]\nname = \"p\"\nedition = \"2026\"\n";

/// A made input: its name, its files (path, text) and whether it continues.
type Made = (&'static str, &'static [(&'static str, &'static str)], bool);

/// Inputs made for the borders: a name, its files, and whether the check
/// continues the base (it falls back where it writes in std's tables).
const MADE: &[Made] = &[
    (
        "impl of a builtin type",
        &[(
            "m.onsa",
            "impl I32 {\n  pub fn twice(self) -> I32 {\n    self * 2\n  }\n}\n\npub fn f() -> I32 {\n  let x: I32 = 3\n  x.twice()\n}\n",
        )],
        false,
    ),
    (
        "impl of std's type through an alias",
        &[(
            "m.onsa",
            "use std.test.{Gen}\n\ntype G = Gen[I32]\n\nimpl G {\n  pub fn n(self) -> I32 {\n    1\n  }\n}\n",
        )],
        false,
    ),
    (
        "a flow",
        &[(
            "m.onsa",
            "pub flow gain(x: F32 at sample, g: F32 at block) -> F32 at sample {\n  let y = prev~(x)\n  (x + y) * g\n}\n",
        )],
        true,
    ),
    (
        "E0311 through std's generic type",
        &[(
            "m.onsa",
            "use std.test.{Gen}\n\npub struct S {\n  g: Gen[S],\n}\n\npub struct T {\n  t: Option[T],\n}\n\npub struct U {\n  u: U,\n}\n",
        )],
        true,
    ),
    (
        "E0310",
        &[
            ("a.onsa", "use b\n\npub fn f() -> I32 {\n  b.g()\n}\n"),
            ("b.onsa", "use a\n\npub fn g() -> I32 {\n  a.f()\n}\n"),
        ],
        true,
    ),
    (
        "E0320 and its uses",
        &[("m.onsa", "pub const small: I32 = 1\n\npub fn f() -> I32 {\n  small + I32.MAX\n}\n")],
        true,
    ),
    ("a target of the user", &[("m.onsa", "target fn t(x: F32) -> F32\n\npub fn f() -> F32 {\n  t(1.0)\n}\n")], true),
    (
        "R-360",
        &[(
            "m.onsa",
            "use std.core.Result.{map_err}\n\nuse std.core.Option.{nothing}\n\npub fn f() -> I32 {\n  1\n}\n",
        )],
        true,
    ),
    (
        "a candidate of a use through std",
        &[("m.onsa", "use std.math\n\nuse math.{sin}\n\npub fn f() -> I32 {\n  1\n}\n")],
        true,
    ),
    (
        "E0304 of a name of std.core",
        &[("m.onsa", "pub struct Show {\n  x: I32,\n}\n\npub fn panic() -> I32 {\n  1\n}\n")],
        true,
    ),
    (
        "a constant that reads std's",
        &[("m.onsa", "pub const TAU: F32 = F32.PI * 2.0\n\npub fn f() -> F32 {\n  TAU + F32.EPSILON\n}\n")],
        true,
    ),
    (
        "std's functions in a body",
        &[(
            "m.onsa",
            "use std.math.{sqrt}\n\npub fn f(x: F32) -> F32 {\n  let r: Result[F32, I32] = Ok(sqrt(x))\n  match r {\n    Ok(v) => v,\n    Err(_) => 0.0,\n  }\n}\n",
        )],
        true,
    ),
];

/// The package of `files` (one file is a single-file input), as a check
/// reads it, and its sources.
fn made(files: &[(&str, &str)]) -> (Package, SourceMap) {
    let mut input = PackageInput {
        files: files.iter().map(|(p, t)| SourceFile { path: (*p).into(), text: (*t).into() }).collect(),
        ..Default::default()
    };
    if files.len() > 1 {
        let text = MANIFEST.to_string();
        input.manifest = Some(ManifestSource { path: "onsa.toml".into(), text, form: ManifestForm::File });
    }
    let mut loaded = Loaded::from_input(input).expect("the input loads");
    let (name, modules) = (loaded.name.clone(), loaded.modules.clone());
    let pkg = user_package(&mut loaded.sources, &name, &modules);
    (pkg, loaded.sources)
}

/// One module of the package `pkg`, parsed.
fn module(sources: &mut SourceMap, pkg: &str, path: &str, src: &str) -> Module {
    let file = sources.add(format!("{pkg}/{path}.onsa"), src);
    Module::new(vec![path.into()], file, src.into(), parse_file(file, src))
}

/// The Core of `a`, printed, or why there is none.
fn core_text(pkg: &Package, a: &onsa_sema::Analysis) -> String {
    match guard(|| onsa_core::lower(pkg, a)) {
        Ok(Ok(m)) => onsa_core::dump(&m),
        other => format!("{other:?}"),
    }
}

/// `pkg` analyzed fresh and continuing the base give the same; whether it
/// continued.
fn compare(what: &str, pkg: &Package) -> bool {
    let fresh = onsa_sema::analyze(pkg);
    let on = onsa_sema::analyze_on(pkg, &std_parsed().base);
    let shown = |a: &onsa_sema::Analysis| (format!("{:?}", a.diagnostics), format!("{:?}", a.path_diagnostics));
    assert_eq!(shown(&fresh), shown(&on), "{what}: the diagnostics");
    assert_eq!(fresh.defs.len(), on.defs.len(), "{what}: the defs");
    assert_eq!(fresh.exports(), on.exports(), "{what}: the exports");
    let parsed = pkg.modules.iter().all(|m| m.parsed.diagnostics.is_empty());
    if parsed && fresh.diagnostics.is_empty() && fresh.path_diagnostics.is_empty() {
        assert_eq!(core_text(pkg, &fresh), core_text(pkg, &on), "{what}: the Core");
    }
    on.continues()
}

/// Every `.onsa` under `dir`, sorted.
fn onsa_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).expect("the directory reads") {
            let p = e.expect("the entry reads").path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "onsa") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

/// `n` of `all`, drawn with `seed` (xorshift), each once.
fn draw(all: Vec<PathBuf>, n: usize, mut seed: u64) -> Vec<PathBuf> {
    let mut left = all;
    let mut out = Vec::new();
    while out.len() < n && !left.is_empty() {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        out.push(left.swap_remove((seed % left.len() as u64) as usize));
    }
    out
}

/// The cases drawn from `tests/spec`, each as the package a check reads.
fn drawn() -> Vec<(String, Package)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let drawn = draw(onsa_files(&root.join("tests/spec")), DRAWN, SEED);
    assert_eq!(drawn.len(), DRAWN);
    let read = |p: &PathBuf| {
        let text = std::fs::read_to_string(p).expect("the case reads");
        let name = p.file_name().and_then(|n| n.to_str()).expect("a file name");
        (p.display().to_string(), made(&[(name, &text)]).0)
    };
    drawn.iter().map(read).collect()
}

#[test]
fn a_continued_analysis_is_the_fresh_one() {
    let started = Instant::now();
    // The cases nest deeper than the default stack of a test thread.
    onsa_diag::stack::run(|| {
        let mut continued = 0;
        for (what, pkg) in &drawn() {
            continued += usize::from(compare(what, pkg));
        }
        // Those that fall back are the few that write in std's tables.
        assert!(continued * 10 >= DRAWN * 9, "{continued} of {DRAWN} continued");
        for (what, files, continues) in MADE {
            let (pkg, _) = made(files);
            assert_eq!(compare(what, &pkg), *continues, "{what}: continues");
        }
        // std, a package on it, and the user's package on both.
        let mut sources = SourceMap::default();
        let std = std_package(&mut sources);
        let mid = module(
            &mut sources,
            "mid",
            "m",
            "use std.math.{sqrt}\n\npub fn half(x: F32) -> F32 {\n  sqrt(x) * 0.5\n}\n",
        );
        let mid = Arc::new(Package::new("mid", vec![mid], vec![std.clone()]));
        let user = module(&mut sources, "user", "u", "use mid.m.{half}\n\npub fn g(x: F32) -> F32 {\n  half(x)\n}\n");
        assert!(compare("three packages", &Package::new("user", vec![user], vec![std, mid])));
        // A package with no std is analyzed fresh.
        let alone = module(&mut sources, "alone", "a", "pub fn f() -> I32 {\n  1\n}\n");
        assert!(!compare("no std", &Package::new("alone", vec![alone], Vec::new())));
    });
    eprintln!("a_continued_analysis_is_the_fresh_one: {:?}", started.elapsed());
}

/// A check continues the base, which is there (std alone has no
/// diagnostic: else every check would be fresh, and slower with no sign).
#[test]
fn a_check_continues_the_base() {
    assert!(std_parsed().base.lock().unwrap_or_else(std::sync::PoisonError::into_inner).usable());
    let input = PackageInput::single_file("m.onsa", "pub fn f() -> I32 {\n  1\n}\n");
    let mut loaded = Loaded::from_input(input).expect("the input loads");
    assert!(analyze_loaded(&mut loaded).expect("no internal error").analysis.continues());
    let (_, files, _) = MADE[0];
    let input = PackageInput::single_file(files[0].0, files[0].1);
    let mut loaded = Loaded::from_input(input).expect("the input loads");
    let analyzed = analyze_loaded(&mut loaded).expect("no internal error");
    assert!(!analyzed.analysis.continues());
    let fresh = onsa_sema::analyze(&analyzed.pkg);
    assert_eq!(format!("{:?}", analyzed.analysis.diagnostics), format!("{:?}", fresh.diagnostics));
}

/// The seed of the hash of sema's tables (W5-18 B1, `onsa_diag::hash`)
/// leaves the output: the diagnostics in their order, and the Core of a
/// package with none, on the drawn cases and the made inputs. The analyses
/// are fresh, so that each table is made under the seed (the base of the
/// process keeps the seed of the process).
#[test]
fn the_seed_of_the_tables_leaves_the_output() {
    let started = Instant::now();
    onsa_diag::stack::run(|| {
        let mut pkgs = drawn();
        pkgs.extend(MADE.iter().map(|(what, files, _)| (what.to_string(), made(files).0)));
        let mut cores = 0;
        for (what, pkg) in &pkgs {
            let parsed = pkg.modules.iter().all(|m| m.parsed.diagnostics.is_empty());
            let output = |k| {
                onsa_diag::hash::with_seed(k, || {
                    let a = onsa_sema::analyze(pkg);
                    let clean = parsed && a.diagnostics.is_empty() && a.path_diagnostics.is_empty();
                    let core = clean.then(|| core_text(pkg, &a));
                    (format!("{:?}", a.diagnostics), format!("{:?}", a.path_diagnostics), core)
                })
            };
            let first = output(0);
            for k in [0x9e37_79b9_7f4a_7c15, 12345] {
                assert_eq!(first, output(k), "{what}: seed {k}");
            }
            cores += usize::from(first.2.is_some());
        }
        // Not a pass with nothing compared.
        assert_eq!(pkgs.len(), DRAWN + MADE.len());
        assert!(cores > 0, "no Core compared");
    });
    eprintln!("the_seed_of_the_tables_leaves_the_output: {:?}", started.elapsed());
}

/// The codes a check of the single file `src` reports.
fn reported(src: &str) -> Vec<onsa_diag::Code> {
    let mut loaded = Loaded::from_input(PackageInput::single_file("m.onsa", src)).expect("the input loads");
    check_loaded(&mut loaded).expect("no internal error").diagnostics.iter().map(|d| d.code).collect()
}

/// A user's `impl` of `Option` with a member of the name of a variant
/// (W5-03 U4): the E0307 of the orphan rule alone (§6.3), the E0304 with the
/// variant (S-737) and the E0320 of the name in its unit (§18.1, S-748). The
/// parser reports the E0320 too, so a case cannot mark it.
#[test]
fn a_member_of_the_name_of_a_variant_of_std_is_in_the_unit_of_the_e0307() {
    assert_eq!(reported("impl[T] Option[T] {\n  pub const None: U8 = 1\n}\n"), vec![onsa_diag::Code::E0307]);
}

/// A user's member of the name of one of std (S-748) comes after it whatever
/// the name of its file (`a.onsa` sorts before `core/num.onsa`): the E0304 is
/// of the user's member, in the unit of its E0307, and std has no diagnostic,
/// though its own member is no name to its bodies either (§18.1).
#[test]
fn a_member_of_the_name_of_one_of_std_leaves_std_with_no_diagnostic() {
    let src = "impl F32 {\n  pub const PI: F32 = 3.0\n  pub fn to_bits(self) -> U32 { 1 }\n}\n";
    assert_eq!(reported(src), vec![onsa_diag::Code::E0307]);
    let (pkg, _) = made(&[("a.onsa", src), ("b.onsa", src), ("main.onsa", "use a\n\nuse b\n")]);
    let a = onsa_sema::analyze(&pkg);
    assert!(a.diagnostics.iter().all(|d| pkg.modules.iter().any(|m| m.file == d.span.file)), "{:?}", a.diagnostics);
}
