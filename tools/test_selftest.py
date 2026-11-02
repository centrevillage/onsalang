#!/usr/bin/env python3
"""Self-tests of tools/selftest.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_selftest.py
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402
import selftest  # noqa: E402

TOOLS = {
    "tools/a.py": "x = 1\n",
    "tools/b.py": "def f():\n    import a  # inside a function too\n",
    "tools/test_b.py": "import b\n",
    "tools/run.py": "x = 1\n",
    "tools/test_run.py": "import subprocess  # runs run.py, imports nothing of tools/\n",
    "tools/sub/c.py": "from b import f\n",
    "tools/sub/test_c.py": "import c\n",
    "tools/lone.py": "x = 1\n",
    "tools/data.txt": "x\n",
    "tools/selftest.py": "x = 1\n",
    "tools/t.toml": "x = 1\n",
}


class Pick(unittest.TestCase):
    """S2 (W4-18 U10b): the self-tests a diff reads, and every one when that cannot be told."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()
        for rel, text in TOOLS.items():
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text(text, encoding="utf-8")

    def pick(self, *changed):
        files, line = selftest.pick(self.root, changed, unread=("tools/t.toml",))
        return sorted(str(f.relative_to(self.root)) for f in files), line

    def test_the_self_tests_whose_imports_reach_a_change(self):
        self.assertEqual(self.pick("tools/a.py"), (["tools/sub/test_c.py", "tools/test_b.py"],
                         "self-tests: 2 of 3 files (the diff touches tools/a.py)"))  # fmt: skip
        self.assertEqual(self.pick("tools/sub/c.py")[0], ["tools/sub/test_c.py"])
        # its own tool, run without an import; a self-test itself; the places outside tools/ and the unread data
        self.assertEqual(self.pick("tools/run.py", "crates/x.rs", "tools/t.toml")[0], ["tools/test_run.py"])
        self.assertEqual(self.pick("tools/test_run.py")[0], ["tools/test_run.py"])

    def test_every_self_test_when_it_cannot_be_told(self):
        every = ["tools/sub/test_c.py", "tools/test_b.py", "tools/test_run.py"]
        for changed, why in (
            (("tools/selftest.py",), "the diff touches tools/selftest.py"),
            (("tools/a.py", "tools/data.txt"), "the diff touches tools/data.txt, not a module"),
            (("tools/gone.py",), "tools/gone.py is gone"),
            (("tools/lone.py",), "none reads tools/lone.py"),  # never none
            (("tools/t.toml",), "none reads the diff"),
        ):
            with self.subTest(changed=changed):
                self.assertEqual(self.pick(*changed), (every, f"self-tests: all 3 files ({why})"))
        (self.root / "tools/sub/a.py").write_text("x = 2\n", encoding="utf-8")
        self.assertEqual(self.pick("tools/run.py"), (every, "self-tests: all 3 files (two modules are named a)"))

    def test_none_run_fails(self):
        r = subprocess.run([sys.executable, "-B", str(Path(selftest.__file__)), "-k", "no_test_has_this_name"],
                           capture_output=True, text=True, timeout=120)  # fmt: skip
        self.assertEqual(r.returncode, 1, r.stderr[-500:])


class RealReads(unittest.TestCase):
    """(c) of W4-18 U10b: the self-tests read made-up inputs; the repository is the gate items'."""

    def test_no_self_test_reads_the_repository(self):
        here = Path(__file__).resolve()  # this file holds the forms as data (test_the_forms)
        files = [f for f in selftest.self_tests(repo.ROOT) if f != here]
        files.append(Path(selftest.__file__).with_name("selftest_support.py"))
        self.assertGreater(len(files), 20)
        found = [f"{f.name}:{line}: {why}" for f in files for line, why in selftest.real_reads(f.read_text("utf-8"))]
        self.assertEqual(found, [])

    def test_the_forms(self):
        text = "\n".join([
            "spec = repo.spec_text(repo.ROOT)", "tree = docs_tool.Tree(builtin_names.ROOT, [])",
            "shutil.copytree(gen.DATA, d)", "s = gen.spec_text()", "cmd = repo.CASES_CMD",
            "# repo.ROOT in a comment", 'tool = repo.ROOT / "tools/run_cases.py"', "x = 1",
        ])  # fmt: skip
        self.assertEqual(selftest.real_reads(text), [
            (1, "the root of the repository"), (2, "the root of the repository"), (3, "the committed test vectors"),
            (4, "the spec of the repository"), (5, "the onsa_cases of the repository")])  # fmt: skip


if __name__ == "__main__":
    unittest.main(verbosity=1)
