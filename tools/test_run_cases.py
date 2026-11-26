#!/usr/bin/env python3
"""Self-tests of tools/run_cases.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_run_cases.py
"""
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402


# A case runner: the list of the cases (`onsa_cases ROOT`) or their run (`--run`). A case whose text has `golden`
# declares the copies of GOLDEN and misses those not under ROOT; one whose text has `long` has a long problem.
# `--c-items` names two items; `--c ITEM ROOT` writes what it got to `c-argv` beside it and exits 1 when a case has
# `c1` in its text, 2 when one has `c2`, else 0.
GOLDEN = ("core/g.core", "c/g.host.c", "c/g.host.h", "graph/g.voice.dot")
FAKE_RUNNER = """#!{exe}
import json, os, sys
if sys.argv[1:] == ["--c-items"]:
    sys.exit(print(json.dumps(["c-clang", "c-gcc"])))
if sys.argv[1] == "--c":
    root = sys.argv[3]
    texts = "".join(open(os.path.join(d, f)).read() for d, _, fs in os.walk(os.path.join(root, "tests")) for f in fs)
    listed = os.path.join(root, "tests/pending.toml")
    got = [sys.argv[1:], open(listed).read() if os.path.exists(listed) else None]
    open(os.path.join(os.path.dirname(sys.argv[0]), "c-argv"), "w").write(json.dumps(got))
    code = 1 if "c1" in texts else 2 if "c2" in texts else 0
    print(f"PASS    tests/a.onsa[host]\\n{{sys.argv[2]}}: 1 cases: {{['PASS', 'FAIL', 'CANNOT RUN'][code]}}")
    sys.exit(code)
root, ran = sys.argv[-1], sys.argv[2:-1] == ["--hosts"]
paths = sorted(os.path.relpath(os.path.join(d, f), root) for d, _, fs in os.walk(root) for f in fs if "golden" not in d)
text = lambda p: open(os.path.join(root, p)).read()
if len(sys.argv) == 2:
    gold = {{"golden": ["core", "c"], "targets": ["host"], "golden_graph": ["voice"]}}
    print(json.dumps([dict(gold if "golden" in text(p) else {{}}, path=p, name=p.split("/")[-1].split(".")[0])
                      for p in paths]))
    sys.exit(0)
hosts = lambda p: ["one", "two"] if p.endswith("fix1") else []
outcomes = lambda p: [{{"name": n, "outcome": "passed" if n == "one" else "failed"}} for n in hosts(p)] if ran else []
missing = lambda p: [f"tests/golden/{{g}} is missing" for g in {golden} if "golden" in text(p)
                     and not os.path.exists(os.path.join(root, "tests/golden", g))]
problems = lambda p: (["two failed"] if ran and hosts(p) else []) + missing(p) + (["x" * 500 + "\\nend"] if "long" in text(p) else [])
print(json.dumps({{"cases": [{{"path": p, "problems": problems(p), "host_names": hosts(p), "hosts": outcomes(p)}}
                            for p in paths]}}))
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
        self.runner.write_text(FAKE_RUNNER.format(exe=sys.executable, golden=GOLDEN))
        self.runner.chmod(0o755)

    def run_cases(self, work, cwd=None, more=(), paths=("a.onsa",)):  # (exit code, lines of stdout)
        argv = ["--tree", str(self.tree), "--bin", str(self.runner), *more, "--work", str(work), *paths]
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
        not_run = "(2 host sequence(s) not run: pass --hosts, or `cargo test -p onsa_tests --test cases` runs them)"
        self.assertEqual(self.run_cases(work), (0, ["ok   tests/a.onsa", f"ok   tests/a.onsa.fix1 {not_run}"]))
        self.assertFalse((work / "stale").exists())

    def test_hosts(self):
        """W5-13 U9b: with `--hosts` the runner gets `--run --hosts`, and the line of a case says how many of its host
        sequences passed; one that failed is a problem of the case."""
        got = self.run_cases(self.top / "out", more=["--hosts"])
        self.assertEqual(got, (1, ["ok   tests/a.onsa", "FAIL tests/a.onsa.fix1 (1 of 2 host sequence(s) passed)",
                                   "      two failed"]))  # fmt: skip

    def test_golden(self):
        """W6-04 U11 (T2): the golden files a case declares are copied to the work directory, so it is compared
        (one missing in the tree is the only problem), and no other golden file; a long problem is printed whole,
        its lines indented."""
        for rel in [g for g in GOLDEN if g != "c/g.host.h"] + ["core/other.core"]:
            (self.tree / "tests/golden" / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.tree / "tests/golden" / rel).write_text("")
        (self.tree / "tests/g.onsa").write_text("golden")
        (self.tree / "tests/long.onsa").write_text("long")
        work = self.top / "out"
        self.assertEqual(self.run_cases(work, paths=["g.onsa", "long.onsa"]),
                         (1, ["FAIL tests/g.onsa", "      tests/golden/c/g.host.h is missing",
                              "FAIL tests/long.onsa", "      " + "x" * 500, "      end"]))  # fmt: skip
        copied = sorted(str(p.relative_to(work / "tests/golden")) for p in (work / "tests/golden").rglob("*.*"))
        self.assertEqual(copied, ["c/g.host.c", "core/g.core", "graph/g.voice.dot"])

    def test_c(self):
        """X-27 TU3: `--c ITEM` runs `onsa_cases --c ITEM <work>` on the cases copied, with an empty list of pending
        entries there, and prints its lines; its failure (1) and its not running (2) are exit 1. A name that is not
        of `--c-items`, and `--c` with `--hosts`, are usage errors."""
        work = self.top / "out"
        self.assertEqual(self.run_cases(work, more=["--c", "c-gcc"]),
                         (0, ["PASS    tests/a.onsa[host]", "c-gcc: 1 cases: PASS"]))  # fmt: skip
        self.assertEqual(json.loads((self.top / "c-argv").read_text()), [["--c", "c-gcc", str(work)], ""])
        for text, code, last in (("c1", 1, "FAIL"), ("c2", 1, "CANNOT RUN")):
            with self.subTest(text=text):
                (self.tree / "tests/a.onsa").write_text(text)
                self.assertEqual(self.run_cases(work, more=["--c", "c-clang"]),
                                 (code, ["PASS    tests/a.onsa[host]", f"c-clang: 1 cases: {last}"]))  # fmt: skip
        for more, why in ((["--c", "c-x"], "--c c-x: not an item of `onsa_cases --c-items` (c-clang, c-gcc)"),
                          (["--c", "c-gcc", "--hosts"], "not allowed with argument")):  # fmt: skip
            with self.subTest(more=more):
                argv = ["--tree", str(self.tree), "--bin", str(self.runner), *more, "--work", str(work), "a.onsa"]
                r = subprocess.run([sys.executable, "-B", str(repo.ROOT / "tools/run_cases.py"), *argv],
                                   capture_output=True, text=True, timeout=60)  # fmt: skip
                self.assertEqual((r.returncode, r.stdout), (2, ""))
                self.assertIn(why, r.stderr)

    def test_stale(self):
        """X-19 2: a runner older than a file of the code it is built from gets a line first, naming the newest; the
        run and its exit code are as without it. tools/, the tests of a crate and a name starting with `.` are not
        of that code."""
        t = self.runner.stat().st_mtime
        files = ("crates/x/src/a.rs", "crates/x/tests/t.rs", "crates/x/src/.a.swp", "tools/t.py", "std/s.onsa",
                 "Cargo.toml")  # fmt: skip
        for rel in files:
            (self.tree / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.tree / rel).write_text("")
            os.utime(self.tree / rel, (t - 100, t - 100))
        ok = ["ok   tests/a.onsa", "ok   tests/a.onsa.fix1 (2 host sequence(s) not run: pass --hosts, or "
              "`cargo test -p onsa_tests --test cases` runs them)"]  # fmt: skip
        work = self.top / "out"
        self.assertEqual(self.run_cases(work), (0, ok))
        for rel in ("crates/x/tests/t.rs", "crates/x/src/.a.swp", "tools/t.py"):
            os.utime(self.tree / rel, (t + 900, t + 900))
        self.assertEqual(self.run_cases(work), (0, ok))
        note = "`cargo build -p onsa_tests --bin onsa_cases` builds it; this run goes on"
        for rel, late in (("crates/x/src/a.rs", 300), ("Cargo.toml", 400), ("std/s.onsa", 7200)):
            with self.subTest(rel=rel):
                os.utime(self.tree / rel, (t + late, t + late))
                self.assertEqual(self.run_cases(work), (0, [
                    f"note: {self.runner} is older than {rel} by {late} s ({late / 3600:.1f} h): {note}", *ok]))
        (self.tree / "tests/a.onsa").write_text("c1")
        code, lines = self.run_cases(work, more=["--c", "c-gcc"])
        self.assertEqual((code, lines[0][:5], lines[1:]),
                         (1, "note:", ["PASS    tests/a.onsa[host]", "c-gcc: 1 cases: FAIL"]))  # fmt: skip


if __name__ == "__main__":
    unittest.main(verbosity=1)
