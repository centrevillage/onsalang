//! The limits of the instances through the commands (§4.4, §4.5, S-290):
//! lowering reports them, so `check` passes and the commands that go on to
//! lowering stop, whatever `--filter` chooses (the roots are the package).

use crate::test_support::{Dir, onsa};

const MANIFEST: &str = "[package]\nname = \"demo\"\nedition = \"2026\"\n\n[export]\nprefix = \"d_\"\n\n\
    [targets.host]\nkind = \"source\"\nlang = \"c\"\nplatform = \"host\"\npanic = \"trap\"\nprovides = []\n";

const MAIN: &str = "fn g[T](x: T, n: U32) -> U32 {\n  if n == 0 {\n    return 0\n  }\n  g(Some(x), n - 1)\n}\n\n\
    pub fn grows() -> U32 {\n  g(1, 3)\n}\n\n@export\npub fn anchor() -> U32 {\n  1\n}\n\n\
    test \"plain\" {\n  assert(anchor() == 1)\n}\n";

fn package() -> Dir {
    let d = Dir::pkg("instance_limits");
    d.write("onsa.toml", MANIFEST);
    d.write("main.onsa", MAIN);
    d
}

/// The exit code and what the command wrote on its standard error.
fn run(args: &[&str]) -> (i32, String) {
    let out = onsa(args);
    let code = out.status.code().unwrap_or_else(|| panic!("onsa {args:?} ended by a signal: {out:?}"));
    (code, format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)))
}

#[test]
fn check_passes_and_the_commands_that_lower_report_the_limit() {
    let d = package();
    let root = d.arg();
    let out = d.path("out");
    assert_eq!(run(&["check", &root]).0, 0);
    for args in [
        vec!["test", &root],
        vec!["test", "--filter", "plain", &root],
        vec!["build", "--target", "host", "--out", &out, &root],
        vec!["interface", &root],
    ] {
        let (code, text) = run(&args);
        assert_eq!(code, 1, "onsa {args:?}: {text}");
        assert!(text.contains("E0422"), "onsa {args:?}: {text}");
        assert!(text.contains("the type is deeper than 256 levels (§4.4)"), "onsa {args:?}: {text}");
        assert!(!text.contains("Option[Option"), "the type is not written out: {text}");
        let path = text.matches("the type arguments come through here").count();
        assert!((1..=3).contains(&path), "the path: {text}");
    }
}
