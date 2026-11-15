#!/usr/bin/env python3
"""Self-tests of tools/moved_only.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_moved_only.py
"""
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import moved_only  # noqa: E402
import repo  # noqa: E402
from selftest_support import git_in, quiet_out  # noqa: E402

A = "fn a() -> u32 {\n    1\n}\n"
B = "fn b(x: u32) -> u32 {\n    x + 2\n}\n"
C = "fn c() {}\n"


class MovedOnly(unittest.TestCase):
    """W6-04 U11 (T1): `split` checks the pieces of each original against it, the coverage of the new files over
    all the checks, and counts the lines that left their file; a reflow is compared after the visibility goes."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)

    def files(self, **texts):
        for name, text in texts.items():
            (self.root / f"{name}.rs").write_text(text)

    def split(self, checks, renames=(), more=()):
        (self.root / "t.json").write_text(json.dumps({"checks": checks, "renames": list(renames)}))
        return quiet_out(moved_only.main, ["split", "--root", str(self.root), *more, str(self.root / "t.json")])

    def check(self, orig, *segments):
        return quiet_out(moved_only.main, ["check", "--root", str(self.root), "--orig", orig, *segments])

    def test_moved(self):
        # (a) `orig.rs` split into `new.rs`, its rename, (a and c) and `b.rs` (b, with a `use` written): only allowed kinds
        self.files(orig=A + B + C, new=A + C, b="use crate::x;\n" + B)
        checks = [{"orig": "orig.rs", "pieces": ["new.rs:1-3", "b.rs", "new.rs:4-4"]}]
        code, lines = self.split(checks, renames=[["orig.rs", "new.rs"]])
        self.assertEqual(code, 0)
        self.assertIn("lines moved out of orig.rs (written lines not counted): 3", lines)
        self.assertEqual(lines[-3:], ["every line of the 2 new files is in one piece",
                                      "=== lines moved to another file in all: 3", "OK"])  # fmt: skip

    def test_orig_path(self):
        # an original copied elsewhere (a function taken out in place first, W6-04 U1) stands for the file
        # `orig_path` names: the lines that stay in that file are not moved
        self.files(step=A + B + C, new=A + C, b=B)
        checks = [{"orig": "step.rs", "pieces": ["new.rs:1-3", "b.rs", "new.rs:4-4"], "orig_path": "new.rs"}]
        code, lines = self.split(checks)
        self.assertEqual(code, 0, "\n".join(lines))
        self.assertIn("lines moved out of new.rs (written lines not counted): 3", lines)

    def test_changed(self):
        # (b) one line changed: NOT ALLOWED with the line, exit 1
        self.files(orig=A + B, new=A + B.replace("x + 2", "x + 3"))
        code, lines = self.split([{"orig": "orig.rs", "pieces": ["new.rs"]}])
        self.assertEqual(code, 1)
        bad = [x for x in lines if x.startswith("NOT ALLOWED")]
        self.assertEqual([x.split()[3:] for x in bad], [["orig:5", "x", "+", "2"], ["new.rs:5", "x", "+", "3"]])
        self.assertEqual(lines[-1], "FAIL")

    def test_two_originals(self):
        # (c) one new file gathers a piece of each of two originals, read at a commit (--rev); the rename of
        # `one.rs` to `all.rs` is not counted as moved
        self.files(one=A + C, two=B)
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", ".")
        git_in(self.root, "commit", "-q", "-m", "orig")
        (self.root / "one.rs").unlink()
        (self.root / "two.rs").write_text("")
        self.files(all=A + B, rest=C)
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-q", "-m", "new")
        (self.root / "all.rs").write_text("")  # the tree differs: --rev reads the commit
        checks = [{"orig": "HEAD~1:one.rs", "pieces": ["all.rs:1-3", "rest.rs"]},
                  {"orig": "HEAD~1:two.rs", "pieces": ["all.rs:4-6"]}]  # fmt: skip
        code, lines = self.split(checks, renames=[["one.rs", "all.rs"]], more=["--rev", "HEAD"])
        self.assertEqual(code, 0, "\n".join(lines))
        self.assertIn("lines moved out of one.rs (written lines not counted): 1", lines)
        self.assertIn("lines moved out of two.rs (written lines not counted): 3", lines)
        self.assertEqual(lines[-2:], ["=== lines moved to another file in all: 4", "OK"])
        # a line left out of every piece, or in two, fails the coverage
        code, lines = self.split(checks[:1], more=["--rev", "HEAD"])
        self.assertEqual((code, lines[-1]), (1, "FAIL"))
        self.assertIn("all.rs:4 is in 0 segments", lines)

    def test_reflow_prefix(self):
        # (d) a statement broken by rustfmt with a `pub(super) ` put before it is a reflow; (e) one that differs
        # in more than the prefix is not
        orig = "fn f(a: u32, b: u32) -> u32 {\n    a + b\n}\n"
        broken = "pub(super) fn f(\n    a: u32,\n    b: u32,\n) -> u32 {\n    a + b\n}\n"
        self.files(orig=orig, new=broken, other=broken.replace("b: u32,", "c: u32,"))
        code, lines = self.check("orig.rs", "new.rs")
        self.assertEqual(code, 0, "\n".join(lines))
        self.assertIn("  reflow: 1", lines)
        code, lines = self.check("orig.rs", "other.rs")
        self.assertEqual(code, 1)
        self.assertNotIn("  reflow: 1", lines)
        self.assertIn("FAIL: differences of a kind that is not allowed", lines)

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in moved_only.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^moved_only\.py {name}( |$)")
                code, lines = quiet_out(moved_only.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        self.assertEqual(list(moved_only.COMMANDS), ["check", "split"])
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf), mock.patch.object(sys, "stderr", buf), \
                self.assertRaises(SystemExit) as e:  # fmt: skip
            moved_only.main([])
        self.assertEqual(e.exception.code, 2)


if __name__ == "__main__":
    unittest.main(verbosity=1)
