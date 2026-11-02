#!/usr/bin/env python3
"""Self-tests of tools/ignored_files.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_ignored_files.py
"""
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ignored_files  # noqa: E402
import repo  # noqa: E402


class IgnoredFiles(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        self.write(".gitignore", "*.out\nbuild/\ntarget/\n")
        self.write("tests/spec/a.onsa")
        # a user's global excludes file that ignores everything Onsa
        self.home = Path(self.tmp.name) / "home"
        (self.home).mkdir()
        (self.home / "ignore").write_text("*.onsa\n*.rs\n")
        (self.home / "gitconfig").write_text(f"[core]\n\texcludesFile = {self.home / 'ignore'}\n")

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text="x\n"):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def check(self):
        out = io.StringIO()
        env = {"GIT_CONFIG_GLOBAL": str(self.home / "gitconfig")}
        with mock.patch("sys.stdout", out), mock.patch.dict(os.environ, env):
            code = ignored_files.main(["--root", str(self.root)])
        return code, out.getvalue()

    def test_clean(self):
        self.write("tests/pkg/onsa.toml")
        self.write("tests/pkg/target/host/x.c")  # the build output of a package
        self.write("crates/a/Cargo.toml")
        self.write("crates/a/target/debug/x")  # the build output of a crate
        self.write("target/debug/y")  # the build output at the root
        self.write("build/x")  # outside the scanned directories
        self.write("crates/a/src/lib.rs")  # the global excludes file ignores it; the check does not read it
        self.write(".git/info/exclude", "*.toml\n")
        self.write("std/math.onsa")
        code, out = self.check()
        self.assertEqual(code, 0, out)

    def test_ignored_files_fail(self):
        self.write("tests/build/case.onsa")
        self.write("tests/golden/c/x.out")
        self.write("tests/target/y.onsa")  # `target/` with no manifest beside it
        self.write("crates/a/src/target/m.rs")
        self.write("std/build/z.onsa")
        self.write("runtime/c/a.out")
        self.write("tools/build/t.py")
        code, out = self.check()
        self.assertEqual(code, 1)
        for p in ("tests/build/", "tests/golden/c/x.out", "tests/target/", "crates/a/src/target/", "std/build/",
                  "runtime/c/a.out", "tools/build/"):  # fmt: skip
            self.assertIn(f"{p}: the .gitignore ignores it", out)

    def test_tracked_but_matched_fails(self):
        self.write("tests/golden/c/kept.out")
        subprocess.run(["git", "add", "-f", "tests/golden/c/kept.out"], cwd=self.root, check=True)
        code, out = self.check()
        self.assertEqual(code, 1)
        self.assertIn("tests/golden/c/kept.out: committed, but a .gitignore pattern matches it", out)

    def test_not_a_repository(self):
        with tempfile.TemporaryDirectory() as d:
            out = io.StringIO()
            with mock.patch("sys.stdout", out):
                self.assertEqual(ignored_files.main(["--root", d]), 1)
            self.assertIn("cannot ask git", out.getvalue())

    def test_build_outputs(self):
        (self.root / "crates/a").mkdir(parents=True)
        (self.root / "crates/a/Cargo.toml").write_text("")
        for rel, out in (
            ("target/x", True),
            ("crates/a/target/x", True),
            ("crates/a/src/target/x", False),
            ("crates/target/x", False),
            ("tests/targets/x", False),
        ):
            self.assertEqual(repo.is_build_output(self.root, rel), out, rel)


if __name__ == "__main__":
    unittest.main(verbosity=1)
