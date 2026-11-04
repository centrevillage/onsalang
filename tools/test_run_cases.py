#!/usr/bin/env python3
"""Self-tests of tools/run_cases.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_run_cases.py
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402


FAKE_RUNNER = """#!{exe}
import json, os, sys
root = sys.argv[2]
paths = sorted(os.path.relpath(os.path.join(d, f), root) for d, _, fs in os.walk(root) for f in fs)
hosts = lambda p: ["one", "two"] if p.endswith("fix1") else []
print(json.dumps({{"cases": [{{"path": p, "problems": [], "host_names": hosts(p)}} for p in paths]}}))
"""


class RunCases(unittest.TestCase):
    """tools/run_cases.py (X-6 T2): `--work` is emptied only when it is an absolute path outside the tree and the
    repository; a relative one, one in the tree or holding it, and one in the repository are refused, nothing removed."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.top = Path(self.tmp.name).resolve()
        self.tree = self.top / "tree"
        (self.tree / "tests").mkdir(parents=True)
        (self.tree / "tests/a.onsa").write_text("")
        (self.tree / "tests/a.onsa.fix1").write_text("")
        self.runner = self.top / "runner"
        self.runner.write_text(FAKE_RUNNER.format(exe=sys.executable))
        self.runner.chmod(0o755)

    def run_cases(self, work, cwd=None):
        argv = ["--tree", str(self.tree), "--bin", str(self.runner), "--work", str(work), "a.onsa"]
        r = subprocess.run([sys.executable, "-B", str(repo.ROOT / "tools/run_cases.py"), *argv], cwd=cwd or self.top,
                           capture_output=True, text=True, timeout=60)  # fmt: skip
        return r.returncode, r.stdout.splitlines()

    def test_refused(self):
        tail = "; give an absolute path outside the tree and the repository (nothing removed)"
        inside = repo.ROOT / "tools/x-6-t2-none"  # a place in the repository (not read)
        (self.tree / "w").mkdir()
        (self.tree / "w/keep").write_text("")
        for work, why in (("tree/w", "not an absolute path"), (self.tree / "w", f"in {self.tree}"),
                          (self.tree, f"in {self.tree}"), (self.top, f"holds {self.tree}"),
                          (inside, f"in {inside.parents[1]}")):  # fmt: skip
            with self.subTest(work=work):
                self.assertEqual(self.run_cases(work), (1, [f"--work {work}: {why}{tail}"]))
        self.assertTrue((self.tree / "w/keep").exists())
        self.assertFalse(inside.exists())

    def test_outside(self):
        work = self.top / "out"
        work.mkdir()
        (work / "stale").write_text("")
        # a case with host sequences says that they did not run: its `ok` is not about them
        not_run = "(2 host sequence(s) not run: only `cargo test -p onsa_tests --test cases` runs them)"
        self.assertEqual(self.run_cases(work), (0, ["ok   tests/a.onsa", f"ok   tests/a.onsa.fix1 {not_run}"]))
        self.assertFalse((work / "stale").exists())


if __name__ == "__main__":
    unittest.main(verbosity=1)
