#!/usr/bin/env python3
"""Self-tests of tools/gate_runs.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_gate_runs.py
"""
import io
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate  # noqa: E402
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import narrowing  # noqa: E402
from selftest_support import git_in  # noqa: E402


class SaveBase(unittest.TestCase):
    """`tools/gate.sh --save-base` (X-1 U2, M-3): the binaries of HEAD for `narrowing.resolve_base`."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve() / "main"
        self.target = Path(self.tmp.name).resolve() / "cargo-target"
        for rel, text in {".gitignore": "target/\n", "crates/c.rs": "fn c() {}\n", "docs/d.md": "d\n",
                          "Cargo.toml": "[workspace]\n"}.items():  # fmt: skip
            self.write(rel, text)
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        self.built = []

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def build(self, root, cases=False):
        self.built.append(cases)
        name = "onsa_cases" if cases else "onsa"
        (self.target / "debug").mkdir(parents=True, exist_ok=True)
        (self.target / "debug" / name).write_text(f"#!/bin/sh\necho {name} {len(self.built)}\n")
        (self.target / "debug" / name).chmod(0o755)
        return True

    def save(self, root=None, keep=2, build=None):
        lines = []
        code = gate_runs.save_base(root or self.root, keep, out=lines.append, build=build or self.build,
                                   target_directory=lambda r: self.target)  # fmt: skip
        return code, "\n".join(lines)

    def head(self):
        return git_in(self.root, "rev-parse", "HEAD").strip()

    def test_warns_of_a_big_debug_directory(self):
        (self.target / "debug" / "deps").mkdir(parents=True)
        (self.target / "debug" / "deps" / "x.o").write_bytes(b"\0" * 65536)
        self.assertIsNone(gate_runs.debug_dir_warning(self.target, 2**30))
        warning = gate_runs.debug_dir_warning(self.target, 1024)
        self.assertTrue(warning.startswith("warning: ") and "cargo clean --profile dev" in warning, warning)
        lines = []
        code = gate_runs.save_base(self.root, 2, out=lines.append, build=self.build,
                                   target_directory=lambda r: self.target, debug_limit=1024)  # fmt: skip
        self.assertEqual((code, lines[-1]), (0, gate_runs.debug_dir_warning(self.target, 1024)))
        self.assertTrue(lines[-2].startswith("save-base: "), lines)
        self.assertNotIn("warning", self.save()[1])  # no limit given, no warning

    def test_saves_what_the_reader_finds(self):
        code, out = self.save()
        self.assertEqual(code, 0, out)
        self.assertEqual(self.built, [False, True])
        d = self.root / "target" / "base" / self.head()[:7]
        self.assertEqual((d / "COMMIT").read_text(), self.head() + "\n")
        # the base of HEAD itself tells nothing apart (it would show the new classes too)
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))
        saved = narrowing.Base(self.head()[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),))
        self.write("crates/c.rs", "fn c() { 1 }\n")  # a change of the code: the base of HEAD differs
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), saved)
        self.write("crates/c.rs", "fn c() {}\n")
        self.write("docs/d.md", "changed\n")  # not the code
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))
        git_in(self.root, "commit", "-qam", "next")  # a work on top of dev
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), saved)
        git_in(self.root, "reset", "-q", "--hard", "HEAD~1")
        self.assertEqual(sorted(p.name for p in (self.root / "target" / "base").iterdir()), [self.head()[:7]])
        # again on the same commit: replaced
        self.assertEqual(self.save()[0], 0)
        self.assertIn("onsa 3", (d / "onsa").read_text())

    def test_the_base_of_an_ancestor_with_the_same_code(self):
        """A merge base with no base saved uses its nearest first-parent ancestor's of the same code (X-1 U4)."""
        self.save()
        a = self.head()
        d = self.root / "target" / "base" / a[:7]
        saved = narrowing.Base(a[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),))
        self.write("docs/d.md", "doc\n")
        git_in(self.root, "commit", "-qam", "doc")
        git_in(self.root, "branch", "-f", "dev", "HEAD")
        self.write("crates/c.rs", "fn c() { 1 }\n")  # a work on top of dev
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), saved)
        git_in(self.root, "checkout", "--", "crates/c.rs")
        self.write("rust-toolchain.toml", "[toolchain]\n")  # the toolchain makes other binaries
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "toolchain")
        git_in(self.root, "branch", "-f", "dev", "HEAD")
        self.write("crates/c.rs", "fn c() { 1 }\n")
        self.assertIn("nor of an ancestor with the same code (50 first-parent commits)",
                      narrowing.resolve_base(self.root, "auto"))
        self.assertEqual((gate_steps.BASES_KEPT, "rust-toolchain.toml" in narrowing.BUILT_FROM), (8, True))

    def test_the_code_before_head(self):
        """A run of the tree at HEAD with no change of the code compares with the code before HEAD (X-1 U6)."""
        self.save()
        c1 = self.head()
        self.write("crates/c.rs", "fn c() { 1 }\n")
        git_in(self.root, "commit", "-qam", "code")
        self.save()
        c2 = self.head()
        self.write("docs/d.md", "doc\n")
        git_in(self.root, "commit", "-qam", "doc")  # saves no base (X-1 U4)
        git_in(self.root, "branch", "-f", "dev", "HEAD")

        def base(c, before=True):
            d = self.root / "target" / "base" / c[:7]
            return narrowing.Base(c[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),), before)

        self.assertEqual(narrowing.resolve_base(self.root, "auto"), base(c1))  # HEAD: the documents on c2
        self.assertEqual(base(c1).shown, f"{c1[:7]} (the code before HEAD)")
        # a narrowed run asks about the work, which has no code: the merge base's own, here of the same code (X-1 U6b)
        self.assertEqual(narrowing.resolve_base(self.root, "auto", narrowed=True), base(c2, before=False))
        self.write("docs/d.md", "changed\n")  # not the code: the same
        self.write("docs/new.md", "new\n")  # untracked, outside BUILT_FROM: not the code either
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), base(c1))
        git_in(self.root, "checkout", "-q", "--", "docs/d.md")
        (self.root / "docs" / "new.md").unlink()
        self.write("crates/c.rs", "fn c() { 2 }\n")  # a change of the code: HEAD's base, as before
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), base(c2, before=False))
        git_in(self.root, "checkout", "-q", "--", "crates/c.rs")
        self.write("crates/new.rs", "fn n() {}\n")  # an untracked file of the code is a change too
        self.assertEqual(narrowing.code_changes(self.root), ["crates/new.rs"])
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), base(c2, before=False))
        (self.root / "crates" / "new.rs").unlink()
        git_in(self.root, "checkout", "-q", c2)  # HEAD at the code commit itself
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), base(c1))
        self.assertEqual(narrowing.resolve_base(self.root, "auto", narrowed=True), base(c2, before=False))
        git_in(self.root, "checkout", "-q", "dev")
        shutil.rmtree(self.root / "target" / "base" / c1[:7])  # no base of the code before
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))
        self.assertIn("and no base of the code before it (50 first-parent commits)",
                      narrowing.resolve_base(self.root, "auto"))

    def test_refuses_changes_of_what_builds_them(self):
        for rel in ("crates/c.rs", "Cargo.toml", "crates/new.rs"):  # the last untracked (X-1 U6b)
            with self.subTest(rel=rel):
                self.write(rel, "changed\n")
                code, out = self.save()
                self.assertEqual(code, 1)
                self.assertIn(f"refused: the files of the code have changes not committed: {rel}", out)
                if rel == "crates/new.rs":
                    (self.root / rel).unlink()
                else:
                    git_in(self.root, "checkout", "--", rel)
        self.assertFalse((self.root / "target" / "base").exists())
        self.assertEqual(self.built, [])
        # the files outside the code, untracked or not, do not refuse
        self.write("docs/new.md", "x\n")
        self.write("docs/d.md", "changed\n")
        self.assertEqual(self.save()[0], 0)

    def test_keeps_the_last(self):
        base = self.root / "target" / "base"
        (base / "notes").mkdir(parents=True)
        (base / "abcdef0").mkdir()  # no COMMIT: not a saved base
        saved = []
        for i in range(3):
            git_in(self.root, "commit", "-q", "--allow-empty", "-m", f"c{i}")
            self.assertEqual(self.save(keep=2)[0], 0)
            saved.append(self.head()[:7])
            os.utime(base / saved[-1] / "COMMIT", (1000 + i, 1000 + i))
        self.assertEqual(self.save(keep=2)[0], 0)  # the newest again: keeps its place
        self.assertEqual(sorted(p.name for p in base.iterdir()), sorted(["notes", "abcdef0"] + saved[1:]))

    def test_main_tree_only_and_failures(self):
        wt = Path(self.tmp.name).resolve() / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        self.assertEqual(self.save(wt)[0], 2)
        self.assertEqual(self.save(Path(self.tmp.name))[0], 2)
        self.assertEqual(self.save(build=lambda root, cases=False: False)[0], 1)
        self.assertEqual(self.built, [])
        self.assertFalse((self.root / "target" / "base").exists() and any((self.root / "target" / "base").iterdir()))
        # alone
        with mock.patch.object(sys, "stderr", io.StringIO()):
            self.assertEqual(gate.main(["--save-base", "--work", "W3-07"], root=self.root, out=io.StringIO()), 2)


class LastRan(unittest.TestCase):
    def test_the_last_clean_run_of_an_item(self):
        # X-1 (1): PASS or FAIL in a clean row of a sweep, the whole or the stage end; a skip, a dirty row, a
        # changed tree, a malformed row and a work check or `--only` (it may run a part, S2) are not runs
        sw = "sweep 0/2"
        rows = [{"commit": "a", "form": sw, "items": {"st": ["PASS", 1.0]}},
                {"commit": "b", "form": "whole", "items": {"st": ["FAIL", 1.0]}},
                {"commit": "c", "form": sw, "items": {"st": ["SKIPPED", 0.0]}},
                {"commit": "d", "form": sw, "dirty": True, "items": {"st": ["PASS", 1.0]}},
                {"commit": "e", "form": sw, "tree_changed": True, "items": {"st": ["PASS", 1.0]}},
                {"commit": "f", "form": sw, "items": {"st": "PASS"}}, {"commit": "g", "form": sw, "items": []},
                {"form": sw, "items": {"st": ["PASS", 1]}},
                {"commit": "h", "form": sw, "items": {"other": ["PASS", 1.0]}},
                {"commit": "i", "form": "work W1-01", "items": {"st": ["PASS", 1.0]}},
                {"commit": "j", "form": "only st", "items": {"st": ["PASS", 1.0]}},
                {"commit": "k", "items": {"st": ["PASS", 1.0]}}]  # fmt: skip
        self.assertEqual(gate_runs.last_ran(rows, "st")["commit"], "b")
        self.assertEqual(gate_runs.last_ran(rows[:1], "st")["commit"], "a")
        self.assertEqual(gate_runs.last_ran([*rows[:1], {**rows[0], "commit": "s", "form": "stage-end W4"}], "st")["commit"], "s")
        self.assertIsNone(gate_runs.last_ran(rows[2:], "st"))
        self.assertIsNone(gate_runs.last_ran([], "st"))


if __name__ == "__main__":
    unittest.main(verbosity=1)
