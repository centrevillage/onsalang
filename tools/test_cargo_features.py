#!/usr/bin/env python3
"""Self-tests of tools/cargo_features.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_cargo_features.py
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cargo_features  # noqa: E402
from selftest_support import quiet_out  # noqa: E402


# The line of a member that depends on the hack crate.
HACK_DEP = f"{cargo_features.HACK}.workspace = true\n"


class CargoFeatures(unittest.TestCase):
    """tools/cargo_features.py: a member selected alone resolves the features of the workspace (X-22).

    A workspace of the members `m1`, `m2` and the hack crate, with a library `lib` (the features `a`, `b`) outside
    it: path dependencies only, so cargo needs no network."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.ws = Path(self.tmp.name) / "ws"
        lib = Path(self.tmp.name) / "lib"
        self.write(lib / "Cargo.toml", '[package]\nname = "lib"\nversion = "0.1.0"\nedition = "2021"\n\n'
                   '[features]\na = []\nb = []\n')  # fmt: skip
        self.write(lib / "src/lib.rs", "")
        self.write(self.ws / "Cargo.toml", '[workspace]\nresolver = "2"\nmembers = ["crates/*"]\n\n'
                   f'[workspace.dependencies]\nlib = {{ path = "{lib.as_posix()}" }}\n'
                   f'{cargo_features.HACK} = {{ path = "crates/{cargo_features.HACK}" }}\n')  # fmt: skip

    def write(self, path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def member(self, name, deps, dev=""):
        """A member with the [dependencies] `deps` and the [dev-dependencies] `dev` (lines of TOML)."""
        dev = f"\n[dev-dependencies]\n{dev}" if dev else ""
        self.write(self.ws / "crates" / name / "Cargo.toml",
                   f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\n{deps}{dev}')  # fmt: skip
        self.write(self.ws / "crates" / name / "src/lib.rs", "")

    def workspace(self, m1, m2, hack, m1_dev=""):
        self.member("m1", m1, m1_dev)
        self.member("m2", m2)
        self.member(cargo_features.HACK, hack)
        subprocess.run(["cargo", "generate-lockfile", "--offline", "-q"], cwd=self.ws, check=True)

    def test_a_member_with_fewer_features_and_one_without_the_hack_fail(self):
        self.workspace('lib = { workspace = true, features = ["a"] }\n',
                       'lib = { workspace = true, features = ["b"] }\n' + HACK_DEP,
                       'lib = { workspace = true, features = ["a"] }\n')  # fmt: skip
        problems, summary = cargo_features.check(self.ws)
        self.assertEqual(summary, "3 members, 2 forms (build, test)")
        self.assertEqual(len(problems), 2, problems)
        self.assertEqual(problems[0], f"m1 does not depend on {cargo_features.HACK}: add `{HACK_DEP.strip()}` to its "
                         "[dependencies]")  # fmt: skip
        # m1 and the hack crate alone do not see the `b` of m2; m2 alone sees the `a` of the hack crate
        self.assertRegex(problems[1], r"^lib v0\.1\.0 \(.*\) is resolved with \[a\] by 2 member\(s\) selected alone in "
                         r"the build and test \(m1, onsa_workspace_hack\): add the features \[b\] of lib to "
                         r"crates/onsa_workspace_hack/Cargo\.toml ")  # fmt: skip
        code, lines = quiet_out(cargo_features.main, [], self.ws)
        self.assertEqual((code, lines[-1]), (1, "2 problem(s) with the features of the cargo commands"))

    def test_the_hack_crate_gives_every_selection_the_features(self):
        self.workspace('lib = { workspace = true, features = ["a"] }\n' + HACK_DEP,
                       'lib = { workspace = true, features = ["b"] }\n' + HACK_DEP,
                       'lib = { workspace = true, features = ["a", "b"] }\n')  # fmt: skip
        self.assertEqual(cargo_features.check(self.ws)[0], [])
        code, lines = quiet_out(cargo_features.main, [], self.ws)
        self.assertEqual((code, lines[-1]), (0, "every member selected alone resolves the features of the workspace"))
        # `--locked`: a Cargo.lock not up to date fails, the check does not rewrite it
        self.member("m3", "lib.workspace = true\n" + HACK_DEP)
        code, lines = quiet_out(cargo_features.main, [], self.ws)
        self.assertEqual(code, 1)
        self.assertIn("--locked` failed", lines[0])

    def test_a_dev_dependency_counts_only_in_the_tests(self):
        # the `b` of the dev dependency of m1: the workspace's tests have it, m2 and the hack crate alone do not
        self.workspace(HACK_DEP, 'lib = { workspace = true, features = ["a"] }\n' + HACK_DEP,
                       'lib = { workspace = true, features = ["a"] }\n',
                       m1_dev='lib = { workspace = true, features = ["b"] }\n')  # fmt: skip
        problems = cargo_features.check(self.ws)[0]
        self.assertEqual(len(problems), 1, problems)
        self.assertRegex(problems[0], r"is resolved with \[a\] by 2 member\(s\) selected alone in the test "
                         r"\(m2, onsa_workspace_hack\): add the features \[b\] of lib")  # fmt: skip


if __name__ == "__main__":
    unittest.main(verbosity=1)
