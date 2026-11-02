#!/usr/bin/env python3
"""Self-tests of tools/ignores.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_ignores.py
"""
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ignores  # noqa: E402
from selftest_support import quiet, TempRepo  # noqa: E402


RUST = '''\
//! A comment that names `#[ignore]` and `#[ignore = "x"]`.
const S: &str = "#[ignore] in a string";

macro_rules! out {
    ($($t:tt)*) => { println!($($t)*) };
}

#[test]
#[ignore = "W3-11 U3c: a \\"quoted\\" reason"]
fn direct_with_reason() {}

#[test]
/// A doc comment.
#[ignore]
fn direct_bare() {}

#[test]
fn not_ignored() {}

macro_rules! one {
    ($name:ident, $v:expr) => {
        #[test]
        fn $name() {}
    };
    ($name:ident, $v:expr, $why:literal) => {
        #[test]
        #[ignore = $why]
        fn $name() {}
    };
}

one!(one_plain, 1);
one!(
    one_multi,
    2,
    "W4-02"
);
one!(
    one_multi_plain,
    3
);

macro_rules! two {
    ($a:ident, $b:ident) => {
        #[test]
        fn $a() {}
        #[test]
        fn $b() {}
    };
    ($a:ident, $b:ident, second: $w:expr) => {
        #[test]
        fn $a() {}
        #[test]
        #[ignore = $w]
        fn $b() {}
    };
    ($a:ident, $b:ident, $w:expr) => {
        #[test]
        #[ignore = $w]
        fn $a() {}
        #[test]
        #[ignore = $w]
        fn $b() {}
    };
}

two!(both_a, both_b, "W3-04");
'''


class Ignores(unittest.TestCase):
    """tools/ignores.py: the ignored tests of the Rust sources, and taking the marks off and on."""

    def marks(self, text):
        tests, problems = ignores.scan(text)
        self.assertEqual(problems, [])
        return {t.name: (t.ignored, t.reason) for t in tests}

    def test_list(self):
        tests, problems = ignores.scan(RUST)
        self.assertEqual(problems, [])
        got = [(t.name, t.line, t.reason) for t in tests if t.ignored]
        line = RUST.splitlines().index
        self.assertEqual(sorted(got), sorted([
            ("direct_with_reason", line("fn direct_with_reason() {}") + 1, 'W3-11 U3c: a "quoted" reason'),
            ("direct_bare", line("fn direct_bare() {}") + 1, None), ("one_multi", line("    one_multi,") + 1, "W4-02"),
            ("both_a", line('two!(both_a, both_b, "W3-04");') + 1, "W3-04"),
            ("both_b", line('two!(both_a, both_b, "W3-04");') + 1, "W3-04"),
        ]))
        self.assertEqual({t.name for t in tests if not t.ignored}, {"not_ignored", "one_plain", "one_multi_plain"})

    def test_forms_not_read_are_named(self):
        cases = {
            "#[ignore]\nfn helper() {}\n": "1: an `#[ignore`",
            "#[test]\n#[ignore = \"a\"] // why\nfn t() {}\n": "2: an `#[ignore`",
            RUST + "const W: &str = \"x\";\none!(by_const, 4, W);\n": "the reason `W` is not a string literal",
            RUST + "two!(x, y, z, w);\n": "no arm of `two!` fits",
            "macro_rules! r {\n    ($($n:ident),*) => { $(#[test] #[ignore] fn $n() {})* };\n}\n": "the macro `r`",
        }
        for text, needle in cases.items():
            problems = ignores.scan(text)[1]
            self.assertTrue(any(needle in p for p in problems), (text, problems))

    def test_direct_edits_keep_the_rest(self):
        out = ignores.edit(RUST, "direct_bare", False)
        self.assertEqual(out, RUST.replace("/// A doc comment.\n#[ignore]\n", "/// A doc comment.\n"))
        out = ignores.edit(out, "not_ignored", True, "W5-08")
        self.assertIn('#[test]\n#[ignore = "W5-08"]\nfn not_ignored()', out)
        out = ignores.edit(out, "direct_with_reason", True, 'new "one"')
        self.assertIn('#[ignore = "new \\"one\\""]\nfn direct_with_reason()', out)
        self.assertEqual(self.marks(out)["direct_with_reason"], (True, 'new "one"'))
        self.assertEqual(ignores.edit(out, "direct_with_reason", True, 'new "one"'), out)

    def test_macro_edits(self):
        out = ignores.edit(RUST, "one_multi", False)
        self.assertEqual(out, RUST.replace('    2,\n    "W4-02"\n);', "    2\n);"))
        out = ignores.edit(out, "one_multi_plain", True, "W9-01")
        self.assertIn('    one_multi_plain,\n    3,\n    "W9-01"\n);', out)
        out = ignores.edit(out, "one_plain", True, "W9-02")
        self.assertIn('one!(one_plain, 1, "W9-02");', out)
        out = ignores.edit(out, "both_a", False)
        self.assertIn('two!(both_a, both_b, second: "W3-04");', out)
        self.assertEqual(self.marks(out)["both_b"], (True, "W3-04"))
        out = ignores.edit(out, "both_b", False)
        self.assertIn("two!(both_a, both_b);", out)
        with self.assertRaises(ignores.Unreadable):  # no arm ignores only the first test
            ignores.edit(out, "both_a", True, "W1-01")

    def test_cli_writes_all_or_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "t.rs"
            f.write_text(RUST, encoding="utf-8")
            self.assertEqual(quiet(ignores.main, ["remove", str(f), "direct_bare", "no_such_test"]), 1)
            self.assertEqual(f.read_text(encoding="utf-8"), RUST)
            self.assertEqual(quiet(ignores.main, ["remove", str(f), "direct_bare", "both_a", "both_b"]), 0)
            self.assertEqual({n for n, (i, _) in self.marks(f.read_text(encoding="utf-8")).items() if i},
                             {"direct_with_reason", "one_multi"})
            (Path(tmp) / "bad.rs").write_text("#[ignore]\nfn helper() {}\n", encoding="utf-8")
            self.assertEqual(quiet(ignores.main, ["list", tmp, "--reason", "W3-11"]), 1)

    def test_passing_against_cargo(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "crates" / "c" / "tests").mkdir(parents=True)
            (Path(tmp) / "crates" / "c" / "tests" / "t.rs").write_text(RUST, encoding="utf-8")
            out = "\n".join([
                "     Running tests/t.rs (target/debug/deps/t-0)", "test direct_with_reason ... ok",
                "test direct_bare ... FAILED", "test both_a ... ok", "test stray ... ok",
            ])
            done = subprocess.CompletedProcess([], 101, stdout=out)
            with mock.patch.object(ignores, "ROOT", Path(tmp)), mock.patch.object(ignores.subprocess, "run",
                                                                                   return_value=done) as run:
                buf = io.StringIO()
                with mock.patch.object(sys, "stdout", buf):
                    code = ignores.main(["passing", "-p", "c", "--reason", "W"])
            self.assertIn("--ignored", run.call_args.args[0])
            self.assertEqual(run.call_args.kwargs["timeout"], 540)
            lines = buf.getvalue().splitlines()
            self.assertEqual(code, 1)  # `stray` ran but the files do not show it
            self.assertTrue(any(x.startswith("pass\t") and "direct_with_reason" in x for x in lines), lines)
            self.assertTrue(any(x.startswith("not run\t") and "\tboth_b\t" in x for x in lines), lines)
            self.assertFalse(any("direct_bare" in x for x in lines), lines)  # no reason, so `--reason` leaves it out
            self.assertTrue(any("`stray`" in x for x in lines), lines)

    def test_passing_against_a_target_of_module_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "crates" / "c" / "tests" / "cli").mkdir(parents=True)
            for m in ("m", "n"):
                (Path(tmp) / "crates" / "c" / "tests" / "cli" / f"{m}.rs").write_text(RUST, encoding="utf-8")
            out = "\n".join(["     Running tests/cli/main.rs (target/debug/deps/cli-0)", "m::direct_with_reason: test",
                             "n::both_a: test", "both_b: test"])
            done = subprocess.CompletedProcess([], 0, stdout=out)
            with mock.patch.object(ignores, "ROOT", Path(tmp)), mock.patch.object(ignores.subprocess, "run",
                                                                                   return_value=done) as run:
                buf = io.StringIO()
                with mock.patch.object(sys, "stdout", buf):
                    code = ignores.main(["passing", "-p", "c", "--test", "cli", "--list"])
            self.assertEqual(run.call_args.args[0][4:6], ["--test", "cli"])
            lines = buf.getvalue().splitlines()
            self.assertEqual(code, 1)  # `both_b` of `main.rs` itself: no file of the tests shows it
            self.assertTrue(any(x.startswith("listed\t") and "cli/m.rs" in x and "\tdirect_with_reason\t" in x
                                for x in lines), lines)
            self.assertTrue(any(x.startswith("not run\t") and "cli/n.rs" in x and "\tdirect_with_reason\t" in x
                                for x in lines), lines)
            self.assertTrue(any(x.startswith("listed\t") and "cli/n.rs" in x and "\tboth_a\t" in x for x in lines), lines)
            self.assertTrue(any("`both_b` of tests/cli/main.rs" in x for x in lines), lines)


class IgnoresStale(TempRepo):
    """tools/ignores.py stale (the gate item `ignores`, R-224): an ignore whose reason names a work done or unknown."""

    def stale(self, *argv):
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf), mock.patch.object(sys, "stderr", buf):
            code = ignores.main(["stale", "--root", str(self.repo.root), *argv])
        return code, buf.getvalue()

    def ignored(self, reason):
        return f'#[test]\n#[ignore = "{reason}"]\nfn t() {{}}\n'

    def check(self, reason, *argv):
        self.repo.write("crates/a/tests/t.rs", self.ignored(reason))
        return self.stale(*argv)

    def test_a_done_work_fails(self):
        for reason in ("W1-01", "W1-01 U2: why"):
            code, out = self.check(reason)
            self.assertEqual(code, 1, out)
            self.assertIn(f"crates/a/tests/t.rs:3\tt\t{reason}\n    the work {reason.split()[0]} is done", out)

    def test_a_work_not_done_passes(self):
        for reason in ("W3-07", "W3-08 U1: why", "W5-07"):
            code, out = self.check(reason)
            self.assertEqual(code, 0, out)
            self.assertIn("1 ignored test(s) in 1 file(s): 1 by a work, 0 for another reason", out)

    def test_an_id_not_in_the_tables_fails(self):
        # W9-99 has no file; W3-071 is not W3-07; a T is no work (the history, X-2 U6)
        for reason in ("W9-99", "W3-071: a typo", "T9-3", "T1-1 (S-45)", "T5-8"):
            code, out = self.check(reason)
            self.assertEqual(code, 1, out)
            self.assertIn("is no work of tasks/W/", out)

    def test_the_works_of_a_stage_fail_at_its_end(self):
        self.repo.write("crates/a/tests/t.rs", self.ignored("W3-07 U1") + self.ignored("W5-07").replace("t()", "u()"))
        code, out = self.stale("--stage-end", "W3")
        self.assertEqual(code, 1, out)
        self.assertIn("the work W3-07 is of W3, which ends here", out)
        self.assertNotIn("W5-07", out)
        self.assertEqual(self.stale("--stage-end", "W5")[0], 1)
        self.assertEqual(self.stale("--stage-end", "W1")[0], 0)
        self.assertEqual(self.stale("--stage-end", "M9")[1].count("which ends here"), 2)  # the end of the first phase
        code, out = self.stale("--stage-end", "W99")
        self.assertEqual(code, 2, out)
        self.assertIn("unknown stage", out)

    def test_a_reason_without_an_id_passes_and_is_counted(self):
        self.repo.write("crates/a/tests/t.rs", RUST.replace("W3-11 U3c", "slow").replace("W4-02", "flaky")
                        .replace('"W3-04"', '"see W1-01"'))  # fmt: skip
        code, out = self.stale()
        self.assertEqual(code, 0, out)
        self.assertIn("5 ignored test(s) in 1 file(s): 0 by a work, 5 for another reason", out)

    def test_nothing_to_read_fails(self):
        code, out = self.stale()  # no crates directory
        self.assertEqual(code, 1, out)
        self.assertIn("no such file or directory", out)
        self.repo.write("crates/a/README.md", "")
        code, out = self.stale()
        self.assertEqual(code, 1, out)
        self.assertIn("no `.rs` file found", out)
        self.repo.write("crates/a/src/lib.rs", "")
        self.assertEqual(self.stale(), (0, "0 ignored test(s) in 1 file(s): 0 by a work, 0 for another reason\n"))

    def test_a_form_not_read_fails(self):
        self.repo.write("crates/a/src/lib.rs", "#[ignore]\nfn helper() {}\n")
        code, out = self.stale()
        self.assertEqual(code, 1, out)
        self.assertIn("an `#[ignore` of a form this tool does not read", out)

    def test_the_paths_and_a_reason_through_a_macro(self):
        # the reason argument of a macro arm, as `stop_case!` of syntax_units.rs (the ignores of R-224)
        f = self.repo.write("crates/a/tests/m.rs", RUST.replace('"W3-04"', '"W1-01"'))
        self.repo.write("crates/b/tests/t.rs", self.ignored("W1-01"))
        code, out = self.stale(str(f))
        self.assertEqual(code, 1, out)
        self.assertEqual(out.count("the work W1-01 is done"), 2)  # both_a and both_b
        self.assertIn("\tboth_a\t", out)
        self.assertNotIn("crates/b", out)
        self.assertIn("is no work of tasks/W/", self.stale(str(f))[1])  # W3-11 and W4-02 have no file


if __name__ == "__main__":
    unittest.main(verbosity=1)
