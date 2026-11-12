#!/usr/bin/env python3
"""Self-tests of tools/work.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_work.py
"""
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / "hooks"))
import claude_hook  # noqa: E402
import docs as docs_tool  # noqa: E402
import gate_runs  # noqa: E402
import handback  # noqa: E402
import narrowing  # noqa: E402
import repo  # noqa: E402
import work  # noqa: E402
from selftest_support import quiet, quiet_out, git_in, NOTHING, NEW_LAYOUT  # noqa: E402


class Take(unittest.TestCase):
    """tools/work.py (moved from take.py, X-9 U4): a patch of a worktree with a WIP commit, changes and new files, applied to a busy tree."""

    LINES = "".join(f"{i}\n" for i in range(1, 10))

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = Path(self.tmp.name)
        self.main, self.wt, self.patch = t / "main", t / "wt", t / "p.patch"
        self.main.mkdir()
        git_in(self.main, "init", "-q")
        for name in ("a.txt", "b.txt", "c.txt"):
            (self.main / name).write_text(self.LINES)
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "base")
        self.base = git_in(self.main, "rev-parse", "HEAD").strip()
        git_in(self.main, "worktree", "add", "-q", "-b", "work", str(self.wt))
        (self.wt / "a.txt").write_text(self.LINES.replace("2\n", "two\n"))
        git_in(self.wt, "commit", "-qam", "WIP")
        (self.wt / "b.txt").write_text(self.LINES.replace("2\n", "two\n"))
        (self.wt / "n.rs").write_text("fn n() {}\n")
        (self.wt / "tests").mkdir()
        (self.wt / "tests" / "x.rs").write_text("a\nb\n")

    def tearDown(self):
        self.tmp.cleanup()

    def take(self, *args):
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf):
            code = work.main(list(map(str, args)))
        return code, buf.getvalue()

    def make_patch(self):
        code, out = self.take("patch", self.wt, self.base, self.patch, "--main", self.main)
        self.assertEqual(code, 0, out)
        return out

    def test_patch(self):
        out = self.make_patch()
        self.assertEqual(git_in(self.wt, "diff", "--cached", "--name-only"), "")
        self.assertIn("4 file(s), +5 -2; without the tests and the data: +1 -0", out)
        self.assertIn("n.rs  (new)", out)
        text = self.patch.read_text()
        self.assertIn("+two", text)
        self.assertIn("b/tests/x.rs", text)
        self.assertTrue(all(map(work.is_code, ("tools/work.py", "std/core.onsa", "std/dsp/x.onsa", "examples/h/d.onsa"))))
        self.assertFalse(any(map(work.is_code, ("tools/test_gate.py", "crates/a/tests/t.rs", "crates/a/src/tests.rs",
                                                "crates/a/src/cst_tests.rs", "tests/pending.toml", "docs/x.md",
                                                "tests/spec/a.onsa", "issues/R/R-1/a.onsa", "decisions/S/S-1/a.onsa"))))
        other = git_in(self.main, "commit-tree", "-m", "x", git_in(self.main, "write-tree").strip()).strip()
        self.assertEqual(self.take("patch", self.wt, other, self.patch, "--main", self.main)[0], 1)

    RUST = "\n".join([
        "fn a() {}",
        "",
        "#[cfg(test)]",
        "#[allow(unused)]",
        "mod tests {",
        "    fn t<'a>(x: &'a str) {",
        '        let s = "fn f() {";',
        '        let r = r#"}"#;',
        "        let (c, d) = ('{', b\"}\");",
        "        /* } /* } */ } */ // }",
        "        assert_eq!(s.len(), 8);",
        "    }",
        "}",
        "",
    ])

    def test_the_test_modules_inside_a_rust_file_are_tests(self):
        # The braces in the strings, the character, the comments and the lifetime are not the block's.
        self.assertEqual(repo.test_lines(self.RUST), set(range(3, 14)))
        (self.wt / "m.rs").write_text(self.RUST)
        git_in(self.wt, "add", "m.rs")
        git_in(self.wt, "commit", "-qm", "m")
        base = git_in(self.wt, "rev-parse", "HEAD").strip()
        (self.wt / "m.rs").write_text(self.RUST.replace("fn a() {}", "fn a() { b() }\nfn b() {}")
                                      .replace("s.len(), 8);", "s.len(), 9);\n        let e = \"{{\";")
                                      + "fn after() {}\n")
        code, out = self.take("patch", self.wt, base, self.patch, "--main", self.main)
        self.assertEqual(code, 0, out)
        # m.rs: +3 -1 of code (fn a, fn b, fn after) and +2 -1 in its test module; n.rs: +1.
        self.assertIn("without the tests and the data: +4 -1 (the test modules inside 1 file(s), +2 -1, left out)", out)

    def test_plain_with_a_change_in_the_same_file(self):
        self.make_patch()
        (self.main / "b.txt").write_text(self.LINES.replace("8\n", "eight\n"))
        (self.main / "c.txt").write_text("other\n")
        code, out = self.take("check", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertIn("applies: plain", out)
        self.assertIn("b.txt: uncommitted change (M)", out)
        self.assertNotIn("c.txt", out)
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertEqual((self.main / "b.txt").read_text(), self.LINES.replace("2\n", "two\n").replace("8\n", "eight\n"))
        self.assertEqual(git_in(self.main, "diff", "--cached", "--name-only"), "")
        code, out = self.take("apply", self.patch, "--to", self.main)  # a second time: nothing to do
        self.assertEqual((code, out.splitlines()[0]), (0, f"applies: {work.ALREADY}"))

    def test_three_way_after_the_main_tree_moved(self):
        (self.main / "a.txt").write_text(self.LINES.replace("5\n", "five\n"))
        git_in(self.main, "commit", "-qam", "moved")
        (self.main / "c.txt").write_text("other\n")
        out = self.make_patch()
        self.assertIn("of the patch: a.txt", out)
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertIn("applies: 3way", out)
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES.replace("2\n", "two\n").replace("5\n", "five\n"))
        self.assertEqual(git_in(self.main, "diff", "--cached", "--name-only"), "")
        self.assertEqual((self.main / "c.txt").read_text(), "other\n")
        self.assertIn("?? n.rs", git_in(self.main, "status", "--porcelain"))

    def test_an_untracked_file_in_the_way(self):
        self.make_patch()
        (self.main / "n.rs").write_text("mine\n")
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 1)
        self.assertIn("n.rs: untracked, already there", out)
        self.assertEqual((self.main / "n.rs").read_text(), "mine\n")
        self.assertEqual((self.main / "b.txt").read_text(), self.LINES)

    def ran(self, form, verdict="PASS", tree=True, code=True):
        """A row of the worktree's history (`gate_runs.record`), on the tree as it is now (`code`: with
        its `code_tree`, as the gate writes since X-1 U5)."""
        (self.main / ".git" / "info").mkdir(exist_ok=True)
        (self.main / ".git" / "info" / "exclude").write_text("target/\n")
        now = repo.tree_hash(self.wt) if tree else None
        code_tree = repo.tree_hash(self.wt, narrowing.SWEPT) if code else None
        gate_runs.record(self.wt, form, [], {"fz": [verdict, 1.0]}, verdict, 1.0, now, not tree, code_tree=code_tree)

    def check_line(self):
        return self.make_patch().splitlines()[1]

    def test_the_line_of_the_work_check(self):
        """`work.py patch` says whether the parent need run the work check again (X-1 U3)."""
        again = "work check: run it again in the main tree: "
        self.assertEqual(self.check_line(), again + "no work check in the worktree")
        self.ran("quick")
        self.assertEqual(self.check_line(), again + "no work check in the worktree (only --quick)")
        self.ran("work X-3/U1", "FAIL")
        self.assertEqual(self.check_line(), again + "the last work check failed (work X-3/U1: fz)")
        self.ran("work X-3/U1", tree=False)
        self.assertEqual(self.check_line(), again + "the tree changed during the check (or could not be read)")
        self.ran("work X-3/U1")
        self.ran("quick")  # the same tree after the work check
        self.assertRegex(self.check_line(), r"^work check: no need to run it again \(work X-3/U1 PASS at .* on the "
                                            r"tree of the patch; base = the main tree's HEAD; applies plain\)$")  # fmt: skip
        (self.wt / "tests" / "x.rs").write_text("changed\n")  # the cases (outside them: the next test)
        self.assertEqual(self.check_line(), again + "the tree changed after the check")
        self.ran("work X-3/U1")
        # the main tree moved after the base: in documents only, then in the code
        (self.main / "d.md").write_text("d\n")
        git_in(self.main, "add", "d.md")
        git_in(self.main, "commit", "-qm", "doc")
        self.assertRegex(self.check_line(), r"^work check: no need to run the heavy items again; run tools/gate.sh "
                                            r"--only static \(the main tree moved in 1 file\(s\) outside the code and "
                                            rf"the cases after the base {self.base[:7]}; work X-3/U1 PASS at ")  # fmt: skip
        (self.main / "b.txt").write_text(self.LINES.replace("8\n", "eight\n"))  # it still applies plain
        self.assertEqual(self.check_line(), again + "the main tree has uncommitted changes in the files of the patch")
        git_in(self.main, "checkout", "--", "b.txt")
        (self.main / "tests").mkdir()
        (self.main / "tests" / "y.rs").write_text("y\n")
        git_in(self.main, "add", "tests")
        git_in(self.main, "commit", "-qm", "case")
        self.assertEqual(self.check_line(), again + "the main tree moved in the code or the cases after the base (tests/y.rs)")

    def test_the_worktree_changed_after_the_check(self):
        """X-1 U5: after the check, a change outside the code and the cases asks for `--only static`; one
        in them, or a row with no `code_tree` (before U5), for the whole check."""
        again = "work check: run it again in the main tree: "
        static = "work check: no need to run the heavy items again; "
        self.ran("work X-3/U1")
        (self.wt / "d.md").write_text("a decision\n")
        self.assertRegex(self.check_line(), r"^" + re.escape(static) + r"run tools/gate.sh --only static \(the worktree "
                         r"changed outside the code and the cases after the check; work X-3/U1 PASS at .* on its "
                         r"code and cases\)$")  # fmt: skip
        # with the main tree moved outside them too: both reasons
        (self.main / "e.md").write_text("e\n")
        git_in(self.main, "add", "e.md")
        git_in(self.main, "commit", "-qm", "doc")
        self.assertRegex(self.check_line(), r"\(the worktree changed outside the code and the cases after the check; "
                         r"the main tree moved in 1 file\(s\) outside the code and the cases after the base "
                         rf"{self.base[:7]}; work X-3/U1 PASS at .* on its code and cases\)$")  # fmt: skip
        self.ran("work X-3/U1", code=False)  # a row from before U5
        (self.wt / "d.md").write_text("changed again\n")
        self.assertEqual(self.check_line(), again + "the tree changed after the check")
        self.ran("work X-3/U1")
        (self.wt / "tests" / "x.rs").write_text("changed\n")  # the cases
        self.assertEqual(self.check_line(), again + "the tree changed after the check")

    def test_the_help_of_patch(self):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), self.assertRaises(SystemExit):
            work.main(["patch", "--help"])
        text = " ".join(out.getvalue().split())
        for part in ("work check: no need to run it again", "run tools/gate.sh --only static",
                     "or the worktree after the check", "the code or the cases of the worktree changed after it",
                     "the worktree whose work is taken", "the patch file to write", "example: tools/work.py patch"):
            self.assertIn(part, text)
        self.assertEqual(self.make_patch().splitlines()[2], "auto sweep: no sweep yet")  # the main tree's
        for part in ("fuzz inputs: none in the worktree", work.COMMANDS["patch"].purpose):
            self.assertIn(part, text)

    def test_the_fuzz_inputs_of_the_worktree(self):
        """X-1 U8: `patch` copies the inputs the worktree's fuzzing kept that the main tree has not, and
        overwrites none; the patch does not take them (target/ is ignored)."""
        (self.main / ".git" / "info").mkdir(exist_ok=True)
        (self.main / ".git" / "info" / "exclude").write_text("target/\n")
        line = lambda: self.make_patch().splitlines()[3]  # noqa: E731
        self.assertEqual(line(), "fuzz inputs: none in the worktree")
        src, dest = self.wt / "target" / "fuzz" / "new", self.main / "target" / "fuzz" / "new"
        src.mkdir(parents=True)
        dest.mkdir(parents=True)
        for name in ("1a2b3c4d.onsa", "5e6f7a8b.onsa", "notes.txt"):
            (src / name).write_text(f"fn {name[:4]}\n")
        (dest / "1a2b3c4d.onsa").write_text("the main tree's\n")
        self.assertEqual(line(), f"fuzz inputs: 1 copied from the worktree into {dest}/: 5e6f7a8b.onsa")
        self.assertEqual((dest / "1a2b3c4d.onsa").read_text(), "the main tree's\n")
        self.assertEqual((dest / "5e6f7a8b.onsa").read_text(), "fn 5e6f\n")
        self.assertFalse((dest / "notes.txt").exists())
        self.assertNotIn("target/", self.patch.read_text())
        self.assertEqual(line(), "fuzz inputs: 2 in the worktree, all in the main tree already")
        with mock.patch.object(work.fuzz, "target_directory", return_value=self.wt / "target"):  # one CARGO_TARGET_DIR
            self.assertEqual(line(), f"fuzz inputs: 2 in {src}/, which the worktree shares with the main tree; "
                                     "none copied")  # fmt: skip
        (dest / "1a2b3c4d.onsa").unlink()
        (dest / "5e6f7a8b.onsa").unlink()
        dest.rmdir()
        dest.write_text("not a directory\n")
        self.assertRegex(line(), rf"^fuzz inputs: 0 copied into {re.escape(str(dest))}/, then the copy failed \(")
        self.assertTrue(self.patch.read_text())  # the patch is made all the same


class Work(unittest.TestCase):
    """tools/work.py (X-9 U4): `new` from dev, `take` with its stops and `--go`, the record, the hook WorktreeCreate, and the help."""

    LINES = "".join(f"{i}\n" for i in range(1, 10))
    BUDGET = "実際の行数が見積もりの 3 倍を超え、かつ差が 100 行以上"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.main = Path(self.tmp.name).resolve() / "main"  # as git gives it (/private/var)
        git_in(self.tmp.name, "init", "-q", "-b", "dev", str(self.main))
        (self.main / ".git" / "info").mkdir(exist_ok=True)
        (self.main / ".git" / "info" / "exclude").write_text("target/\n.claude/\n")
        for rel in ("a.txt", *work.REGISTRIES):
            (self.main / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.main / rel).write_text(self.LINES)
        self.budget(self.BUDGET)
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "base")
        self.dev = self.head(self.main)

    def tearDown(self):
        self.tmp.cleanup()

    def budget(self, value, name=work.REFACTOR):
        (self.main / "rules").mkdir(exist_ok=True)
        (self.main / repo.BUDGETS).write_text(f"| 名前 | 値 |\n|---|---|\n| 他 | 2 倍を超え、かつ差が 1 行以上 |\n"
                                              f"| {name} | {value} |\n")  # fmt: skip

    def head(self, tree):
        return git_in(tree, "rev-parse", "HEAD").strip()

    def test_estimate_from_budgets(self):
        # X-9 U19: the ratio and the lines of the size to refactor are the row's of rules/budgets.md of the tree
        def judged(lines):
            return work.estimate_line(lines, 50, self.main).split("times; ")[1]

        size = "the size to refactor (rules/budgets.md: over {} times and {} lines more)"
        self.assertEqual((judged(150), judged(151)), (f"within {size.format(3, 100)}", f"over {size.format(3, 100)}"))
        self.budget("見積もりの 2 倍を超え、かつ差が 50 行以上")
        self.assertEqual((judged(100), judged(101)), (f"within {size.format(2, 50)}", f"over {size.format(2, 50)}"))
        for value, name, says in (("x", "他の行", "no row 「リファクタリングに入る大きさ」"),
                                  ("3 倍を超えるもの", work.REFACTOR, "the row 「リファクタリングに入る大きさ」 says no")):  # fmt: skip
            with self.subTest(says=says):
                self.budget(value, name)
                self.assertTrue(judged(150).startswith(f"not judged against the size to refactor (rules/budgets.md: "
                                                       f"{says}"), judged(150))  # fmt: skip
        # without rules/budgets.md in the main tree, take still applies, and the line says why it is not judged
        wt = self.worktree()
        gate_runs.record(wt, "work X-9/U19", [], {"fz": ["PASS", 1.0]}, "PASS", 1.0, repo.tree_hash(wt),
                         code_tree=repo.tree_hash(wt, narrowing.SWEPT))  # fmt: skip
        (self.main / repo.BUDGETS).unlink()
        code, lines = self.take("w1", "--estimate", 50)
        self.assertEqual(code, 0, lines)
        self.assertIn("estimate: +150 of the code (without the tests and the data) against 50: 3.00 times; not judged "
                      "against the size to refactor (rules/budgets.md: [Errno 2]", "\n".join(lines))  # fmt: skip
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES.replace("2\n", "two\n"))

    def test_new(self):
        code, lines = quiet_out(work.main, ["new", "a1", "--main", str(self.main)])
        wt = self.main / ".claude" / "worktrees" / "a1"
        self.assertEqual((code, lines[-1]), (0, str(wt)))
        self.assertEqual((git_in(wt, "branch", "--show-current").strip(), self.head(wt)), ("worktree-a1", self.dev))
        # from dev by name, not from the HEAD; from a worktree, in the main tree
        git_in(self.main, "checkout", "-q", "-b", "other")
        (self.main / "a.txt").write_text("other\n")
        git_in(self.main, "commit", "-qam", "other")
        self.assertEqual(work.new("a2", wt), self.main / ".claude" / "worktrees" / "a2")
        self.assertEqual(self.head(self.main / ".claude" / "worktrees" / "a2"), self.dev)
        # the same name stops: the branch and the path, the branch alone (the worktree removed), the path alone
        git_in(self.main, "worktree", "remove", str(self.main / ".claude" / "worktrees" / "a2"))
        (self.main / ".claude" / "worktrees" / "a3").mkdir()
        for name, says in (("a1", "the branch worktree-a1 is there already"), ("a2", "the branch worktree-a2 is there"),
                           ("a3", "/a3 is there already"), ("../x", "is not the name of a worktree")):  # fmt: skip
            with self.subTest(name=name):
                code, lines = quiet_out(work.main, ["new", name, "--main", str(self.main)])
                self.assertEqual(code, 1)
                self.assertIn(says, lines[-1])
        self.assertFalse(git_in(self.main, "branch", "--list", "worktree-a3").strip())

    def test_the_hook_worktree_create(self):
        def hook(text):
            out, err = io.StringIO(), io.StringIO()
            with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", err):
                code = claude_hook.main(["WorktreeCreate"], io.StringIO(text))
            return code, out.getvalue().splitlines(), err.getvalue().splitlines()

        event = json.dumps({"session_id": "s", "hook_event_name": "WorktreeCreate", "cwd": str(self.main), "name": "h1"})
        self.assertEqual(hook(event), (0, [str(self.main / ".claude" / "worktrees" / "h1")], []))
        code, out, err = hook(event)
        self.assertEqual((code, out), (1, []))
        self.assertRegex(err[0], r"^WorktreeCreate: Failed: the branch worktree-h1 is there already")
        self.assertEqual(hook("{}")[::2], (1, ["WorktreeCreate: KeyError: 'name'"]))

    def worktree(self):
        """The worktree `w1`: a WIP commit, then a change of tests/pending.toml and 150 lines of code."""
        wt = work.new("w1", self.main)
        (wt / "a.txt").write_text(self.LINES.replace("2\n", "two\n"))
        git_in(wt, "commit", "-qam", "WIP")
        (wt / work.PENDING).write_text(self.LINES.replace("2\n", "[[pending]]\n"))
        (wt / "c.py").write_text("x = 1\n" * 150)
        return wt

    def take(self, *argv):
        return quiet_out(work.main, ["take", *map(str, argv), "--main", str(self.main)])

    def reset(self):
        git_in(self.main, "checkout", "--", ".")
        (self.main / "c.py").unlink()

    def test_take(self):
        wt = self.worktree()
        code, lines = self.take("w1", "--estimate", 50)  # by name, no work check in the worktree
        self.assertEqual(code, 1, lines)
        self.assertEqual(lines[-2:], ["applies: plain", "take: not applied (the work check is to run again); read "
                                      "the above, then apply it with --go"])  # fmt: skip
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES)
        at = lines.index(f"the hunks of {work.PENDING}:")
        self.assertEqual(lines[at + 1:at + 8], ["@@ -1,5 +1,5 @@", " 1", "-2", "+[[pending]]", " 3", " 4", " 5"])
        self.assertNotIn("the hunks of tools/builtin_names.toml:", lines)
        self.assertIn("estimate: +150 of the code (without the tests and the data) against 50: 3.00 times; within the "
                      "size to refactor (rules/budgets.md: over 3 times and 100 lines more)", lines)  # fmt: skip
        gate_runs.record(wt, "work X-9/U4", [], {"fz": ["PASS", 1.0]}, "PASS", 1.0, repo.tree_hash(wt),
                         code_tree=repo.tree_hash(wt, narrowing.SWEPT))  # a work check on the tree: it applies
        code, lines = self.take(wt, "--estimate", 40)  # by path
        self.assertEqual(code, 0, lines)
        self.assertRegex(lines[1], r"^work check: no need to run it again")
        self.assertIn("3.75 times; over the size to refactor", "\n".join(lines))
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES.replace("2\n", "two\n"))
        rows = [json.loads(x) for x in (self.main / work.TAKEN).read_text().splitlines()]
        self.assertEqual([r["kind"] for r in rows], ["patch", "patch", "apply"])
        p, a = rows[1], rows[2]
        self.assertEqual({k: p[k] for k in ("worktree", "branch", "base", "tree")},
                         {"worktree": str(wt.resolve()), "branch": "worktree-w1", "base": self.dev,
                          "tree": repo.tree_hash(wt)})  # fmt: skip
        self.assertEqual((Path(p["patch"]).parent, Path(rows[0]["patch"]).is_file()), ((self.main / "target/work").resolve(), True))
        self.assertNotEqual(rows[0]["patch"], p["patch"])
        self.assertEqual((a["patch"], a["to"], a["head"]), (p["patch"], str(self.main.resolve()), self.dev))
        # an uncommitted change in a file of the patch: plain, but it stops; --go applies it
        self.reset()
        (self.main / "a.txt").write_text(self.LINES.replace("8\n", "eight\n"))
        code, lines = self.take("w1")
        self.assertEqual(code, 1, lines)
        self.assertIn("  a.txt: uncommitted change (M)", lines)
        self.assertRegex(lines[-1], r"^take: not applied \(the main tree has uncommitted changes in the files of the "
                                    r"patch; the work check is to run again\)")  # fmt: skip
        self.assertEqual(self.take("w1", "--go")[0], 0)
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES.replace("2\n", "two\n").replace("8\n", "eight\n"))
        # dev moved in tests/pending.toml: 3-way, the line of rules/leader.md 3.4; --go applies it
        self.reset()
        (self.main / work.PENDING).write_text(self.LINES.replace("5\n", "five\n"))
        git_in(self.main, "commit", "-qam", "dev moved")
        code, lines = self.take("w1")
        self.assertEqual(code, 1, lines)
        self.assertIn("applies: 3way", lines)
        self.assertIn(f"{work.PENDING} is in a patch that applies 3-way: rebuild it from dev's version "
                      "(rules/leader.md 3.4)", lines)  # fmt: skip
        self.assertRegex(lines[-1], r"^take: not applied \(it applies 3way; ")
        self.assertEqual(self.take("w1", "--go")[0], 0)
        self.assertEqual((self.main / work.PENDING).read_text(),
                         self.LINES.replace("2\n", "[[pending]]\n").replace("5\n", "five\n"))  # fmt: skip
        self.assertEqual(self.take("nosuch")[0], 1)

    # The cleaning up (X-9 U5): a made-up directory of Claude Code's records (`work.RECORDS_ENV`).

    def record(self, wt, session="s1", finished=False, agent=None):
        d = Path(self.tmp.name) / "records" / session / "subagents"
        d.mkdir(parents=True, exist_ok=True)
        meta = {"agentType": "onsa-impl", "worktreePath": str(wt), "worktreeBranch": work.branch_of(wt.name),
                **({"finished": True} if finished else {})}  # fmt: skip
        (d / f"agent-{agent or wt.name}.meta.json").write_text(json.dumps(meta))

    def clean(self, *argv):
        (Path(self.tmp.name) / "records").mkdir(exist_ok=True)
        with mock.patch.dict(os.environ, {work.RECORDS_ENV: str(Path(self.tmp.name) / "records")}):
            return quiet_out(work.main, [*map(str, argv), "--main", str(self.main)])

    def gone(self, wt):
        """Whether the worktree and its branch are gone."""
        return (wt.exists(), git_in(self.main, "branch", "--list", work.branch_of(wt.name)).strip()) == (False, "")

    def test_done_live_and_unreadable(self):
        wt = work.new("l1", self.main)
        self.record(wt)
        for argv in (["--session", "s1"], [], ["--session", "s1", "--discard"]):  # this session's, no session
            with self.subTest(argv=argv):
                code, lines = self.clean("done", "l1", *argv)
                self.assertEqual((code, lines), (1, ["keep l1 (worktree-l1): the agent is running (onsa-impl l1)"]))
        self.record(work.new("l2", self.main), session="s2")
        bad = Path(self.tmp.name) / "records" / "s2" / "subagents" / "agent-x.meta.json"
        bad.write_text("{")
        code, lines = self.clean("done", "l2")
        self.assertEqual(code, 1)
        self.assertRegex(lines[0], r"^keep l2 \(worktree-l2\): the record .*agent-x\.meta\.json cannot be read")
        bad.unlink()
        code, lines = self.clean("done", "l1", "--session", "s2")  # another session's record: finished
        self.assertEqual((code, lines[0]), (0, f"remove l1 (worktree-l1): no change (no commit after dev, the tree is "
                                               "its HEAD's)"))  # fmt: skip
        self.assertIn("  reports: not checked (no --scratchpad)", lines)
        self.assertTrue(self.gone(wt))

    def test_done_clean_locked_and_reports(self):
        wt = work.new("c1", self.main)
        (wt / "target" / "fuzz" / "new").mkdir(parents=True)  # ignored under target/: the tree is clean
        (wt / "target" / "fuzz" / "new" / "f1.onsa").write_text("x\n")
        git_in(self.main, "worktree", "lock", "--reason", "kept by hand", str(wt))
        self.record(wt, finished=True)
        scratch = Path(self.tmp.name) / "scratch"
        code, lines = self.clean("done", wt, "--session", "s1", "--scratchpad", scratch)  # by path
        self.assertEqual(code, 0, lines)
        self.assertIn(f"  reports: none saved for onsa-impl c1 in {scratch}/handback/", lines)
        self.assertRegex(lines[-1], r"^  removed the branch worktree-c1 \(in dev; its tip was [0-9a-f]{40}\)$")
        self.assertTrue(self.gone(wt))
        self.assertTrue((self.main / "target" / "fuzz" / "new" / "f1.onsa").is_file())
        wt = work.new("c2", self.main)
        self.record(wt, finished=True)
        (scratch / "handback").mkdir(parents=True)
        (scratch / "handback" / "onsa-impl-c2-001.md").write_text("report\n")
        code, lines = self.clean("done", "c2", "--scratchpad", scratch)
        self.assertEqual(code, 0, lines)
        self.assertFalse([x for x in lines if "reports:" in x])
        # X-13 T8: a saved report with no body (the hook's, `handback.saved`) is not counted as saved
        wt = work.new("c3", self.main)
        self.record(wt, finished=True)
        empty = scratch / "handback" / "onsa-impl-c3-002.md"
        empty.write_text(handback.saved("usage: x", f"{handback.NO_BODY}… ）\n取り出し直す: …"))
        (scratch / "handback" / "onsa-impl-c3-001.md").write_text(handback.saved("usage: x", "報告"))
        (scratch / "handback" / "onsa-impl-c3-003.md").write_text(f"報告 3\n\n引いた: {handback.NO_BODY}\n")  # save's
        code, lines = self.clean("done", "c3", "--scratchpad", scratch)
        self.assertEqual(code, 0, lines)
        self.assertEqual([x for x in lines if "reports:" in x],
                         [f"  reports: no body in {empty} for onsa-impl c3: take it out with the command in it"])

    def test_done_live_by_the_lock_and_records_of_a_wrong_form(self):
        wt = work.new("k1", self.main)
        self.record(wt, finished=True)
        git_in(self.main, "worktree", "lock", "--reason", "claude agent agent-k1 (pid 1)", str(wt))  # Claude Code's
        self.assertEqual(self.clean("done", "k1", "--session", "s1"),
                         (1, ["keep k1 (worktree-k1): the agent is running (locked: claude agent agent-k1 (pid 1))"]))
        git_in(self.main, "worktree", "unlock", str(wt))
        subagents = Path(self.tmp.name) / "records" / "s1" / "subagents"
        for session, meta, says in (
                ("nosuch", None, "no record of the session nosuch in "),
                ("s1", {"agentType": "onsa-impl", "spawnedWithWorktree": True}, "names no worktree, though spawned"),
                ("s1", {"spawnedWithWorktree": True, "inheritedWorktreePath": "", "finished": True},
                 "names no worktree, though spawned"),
                ("s1", {"inheritedWorktreePath": 5, "finished": True}, "is not of the form known"),
                ("s1", {"agentType": "onsa-impl", "worktreePath": 5}, "is not of the form known"),
                ("s1", {"worktreeBranch": ["x"], "finished": True}, "is not of the form known"),
                ("s1", {"worktreePath": str(wt), "finished": "yes"}, "is not of the form known")):  # fmt: skip
            with self.subTest(meta=meta, session=session):
                if meta is not None:
                    (subagents / "agent-x.meta.json").write_text(json.dumps(meta))
                code, lines = self.clean("done", "k1", "--session", session)
                self.assertEqual(code, 1, lines)
                self.assertIn(says, lines[0])
                self.assertTrue(wt.is_dir())
        (subagents / "agent-x.meta.json").unlink()
        self.assertEqual(self.clean("done", "k1", "--session", "s1")[0], 0)

    def inherited(self, wt, agent, finished):
        """The record of an agent an agent spawned in its worktree `wt` (seen 2026-10-25: no `worktreePath` nor
        `worktreeBranch`)."""
        meta = {"agentType": "general-purpose", "inheritedWorktreePath": str(wt), "spawnedWithWorktree": True,
                "parentAgentId": wt.name, "spawnDepth": 2, **({"finished": True} if finished else {})}  # fmt: skip
        (Path(self.tmp.name) / "records" / "s1" / "subagents" / f"agent-{agent}.meta.json").write_text(json.dumps(meta))

    def test_done_an_agents_agent_in_the_worktree(self):
        wt, other, live = work.new("a1", self.main), work.new("a2", self.main), work.new("a3", self.main)
        for x in (wt, other, live):
            self.record(x, finished=True)
        self.inherited(wt, "a1x", finished=True)
        self.inherited(live, "a3x", finished=False)
        code, lines = self.clean("done", "a2", "--session", "s1")  # the records of the agents' agents: read
        self.assertEqual((code, lines[0]), (0, "remove a2 (worktree-a2): no change (no commit after dev, the tree is "
                                               "its HEAD's)"))  # fmt: skip
        scratch = Path(self.tmp.name) / "scratch"
        code, lines = self.clean("done", wt, "--session", "s1", "--scratchpad", scratch)
        self.assertEqual(code, 0, lines)
        self.assertEqual([x for x in lines if "reports:" in x],
                         [f"  reports: none saved for {k} in {scratch}/handback/" for k in ("onsa-impl a1",
                                                                                           "general-purpose a1x")])
        self.assertTrue(self.gone(wt) and self.gone(other))
        for argv in (["--session", "s1"], [], ["--session", "s1", "--discard"]):  # an agent's agent running in it
            with self.subTest(argv=argv):
                self.assertEqual(self.clean("done", "a3", *argv),
                                 (1, ["keep a3 (worktree-a3): the agent is running (general-purpose a3x)"]))
        self.assertTrue(live.is_dir())

    def test_done_ignored_files_and_a_change_after_the_verdict(self):
        (self.main / ".gitignore").write_text("*.log\ntarget/\n")
        git_in(self.main, "add", ".gitignore")
        git_in(self.main, "commit", "-qm", "ignore")
        wt = work.new("i1", self.main)
        (wt / "notes.log").write_text("a note\n")
        (wt / "target").mkdir()
        (wt / "target" / "x.log").write_text("build\n")  # under target/: it goes with the worktree
        code, lines = self.clean("done", "i1")
        self.assertEqual((code, lines), (1, ["keep i1 (worktree-i1): no change (no commit after dev, the tree is its "
                                             "HEAD's); but 1 ignored file(s) outside target/ would go with it: "
                                             "notes.log"]))  # fmt: skip
        code, lines = self.clean("done", "i1", "--discard")
        self.assertEqual(code, 0, lines)
        self.assertIn("  the ignored files that go with it: notes.log", lines)
        self.assertTrue(self.gone(wt))
        # changed after the verdict (here while the fuzzing inputs are copied): nothing goes
        wt = work.new("i2", self.main)
        late = lambda wt, main, strict: (Path(wt) / "late.txt").write_text("x\n") and "fuzz inputs: none"  # noqa: E731
        with mock.patch.object(work, "copy_fuzz_inputs", late):
            code, lines = self.clean("done", "i2")
        self.assertEqual((code, lines[-1]), (1, f"{wt} changed after the verdict; nothing removed"))
        self.assertEqual(((wt / "late.txt").is_file(), self.gone(wt)), (True, False))

    def test_done_clean_when_the_main_tree_is_not_on_dev(self):
        (self.main / "a.txt").write_text("dev moved\n")
        git_in(self.main, "commit", "-qam", "dev moved")
        wt = work.new("g1", self.main)
        git_in(self.main, "checkout", "-q", "-b", "old", "HEAD~1")  # `git branch -d` would ask `old`
        code, lines = self.clean("done", "g1")
        self.assertEqual(code, 0, lines)
        self.assertRegex(lines[-1], r"^  removed the branch worktree-g1 \(in dev; its tip was ")
        self.assertTrue(self.gone(wt))

    def test_done_taken_by_the_record(self):
        wt = self.worktree()
        gate_runs.record(wt, "work X-9/U5", [], {"fz": ["PASS", 1.0]}, "PASS", 1.0, repo.tree_hash(wt),
                         code_tree=repo.tree_hash(wt, narrowing.SWEPT))  # fmt: skip
        tip = self.head(wt)
        (self.main / work.TAKEN).parent.mkdir(parents=True)
        with (self.main / work.TAKEN).open("a") as f:  # rows of a wrong form are passed over
            f.write('{"kind": "patch", "patch": [1]}\n{"kind": "apply", "patch": "p", "to": 5}\n[1]\n')
        self.assertEqual(self.take("w1")[0], 0)
        patch = json.loads((self.main / work.TAKEN).read_text().splitlines()[-1])["patch"]
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "taken")
        (self.main / "a.txt").write_text(self.LINES.replace("2\n", "TWO\n"))  # dev changes the same line after it
        git_in(self.main, "commit", "-qam", "dev moved")
        code, lines = self.clean("done", "w1")
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"remove w1 (worktree-w1): taken (the patch {patch} of this tree and its apply to "
                                   "the main tree are in target/work/taken.jsonl)")  # fmt: skip
        self.assertEqual(lines[-1], f"  removed the branch worktree-w1 (-D; its tip was {tip})")
        self.assertTrue(self.gone(wt))

    def test_done_taken_in_reverse_and_an_apply_elsewhere(self):
        wt = work.new("r1", self.main)
        (wt / "a.txt").write_text(self.LINES.replace("3\n", "three\n"))
        (self.main / "a.txt").write_text(self.LINES.replace("3\n", "three\n"))
        git_in(self.main, "commit", "-qam", "the same change")
        code, lines = self.clean("done", "r1")
        self.assertEqual((code, lines[0]), (0, "remove r1 (worktree-r1): taken (its patch from the base applies in "
                                               "reverse in the main tree)"))  # fmt: skip
        self.assertTrue(self.gone(wt))
        # applied to another worktree only: not taken
        wt, other, out = work.new("r2", self.main), work.new("r3", self.main), Path(self.tmp.name) / "r2.patch"
        (wt / "a.txt").write_text(self.LINES.replace("4\n", "four\n"))
        self.assertEqual(quiet_out(work.main, ["patch", str(wt), self.head(self.main), str(out), "--main",
                                               str(self.main)])[0], 0)  # fmt: skip
        self.assertEqual(quiet_out(work.main, ["apply", str(out), "--to", str(other)])[0], 0)
        self.assertEqual([json.loads(x)["kind"] for x in (self.main / work.TAKEN).read_text().splitlines()],
                         ["patch", "apply"])  # fmt: skip
        code, lines = self.clean("done", "r2")
        self.assertEqual((code, lines), (1, ["keep r2 (worktree-r2): not taken: 1 file(s) changed from the base, "
                                             "0 commit(s) after dev"]))  # fmt: skip

    def test_done_changed_and_discard(self):
        wt = work.new("u1", self.main)
        (wt / "new.txt").write_text("untracked\n")  # an untracked file alone
        code, lines = self.clean("done", "u1")
        self.assertEqual((code, lines), (1, ["keep u1 (worktree-u1): not taken: 1 file(s) changed from the base, "
                                             "0 commit(s) after dev"]))  # fmt: skip
        self.assertTrue(wt.is_dir())
        code, lines = self.clean("done", "u1", "--discard")
        self.assertEqual(code, 0, lines)
        saved = list((self.main / work.DISCARDED).glob("u1-*.patch"))
        self.assertEqual(len(saved), 1, lines)
        self.assertIn("+untracked", saved[0].read_text())
        self.assertRegex(lines[-1], r"^  removed the branch worktree-u1 \(-D; its tip was ")
        self.assertTrue(self.gone(wt))

    def test_close_dry_run_prune_and_what_never_goes(self):
        git_in(self.main, "branch", "main")
        git_in(self.main, "branch", "other-x")
        clean, kept, gone = work.new("k1", self.main), work.new("k2", self.main), work.new("k3", self.main)
        (kept / "a.txt").write_text("changed\n")
        git_in(kept, "commit", "-qam", "WIP")
        shutil.rmtree(gone)  # the directory alone gone: its registration is pruned, its branch judged alone
        feature = self.main / ".claude" / "worktrees" / "f1"
        git_in(self.main, "worktree", "add", "-q", "-b", "feature", str(feature), "dev")
        branches = lambda: sorted(git_in(self.main, "branch", "--format=%(refname:short)").split())  # noqa: E731
        before = branches()
        code, lines = self.clean("close", "--dry-run")
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"the main tree {self.main}: 0 uncommitted change(s)")
        self.assertEqual(sorted(lines[1:-1]), sorted([
            "keep k2 (worktree-k2): not taken: 1 file(s) changed from the base, 1 commit(s) after dev",
            "would remove f1 (feature): no change (no commit after dev, the tree is its HEAD's)",
            "would remove k1 (worktree-k1): no change (no commit after dev, the tree is its HEAD's)",
            "would remove worktree-k3: no change (no commit after dev, the tree is its HEAD's)",
            *["  reports: not checked (no --scratchpad)"] * 3]))  # fmt: skip
        self.assertEqual(lines[-1], "close: 3 to remove, 1 kept, 0 failed")
        self.assertEqual((branches(), clean.is_dir(), feature.is_dir()), (before, True, True))
        # by the names of the trees: the temporary directory's own name may hold "k3"
        trees = lambda: [Path(line.split()[0]).name for line in git_in(self.main, "worktree", "list").splitlines()]  # noqa: E731
        self.assertIn("k3", trees())
        code, lines = self.clean("close")
        self.assertEqual((code, lines[-1]), (0, "close: 3 removed, 1 kept, 0 failed"))
        self.assertIn("  kept the branch feature (only worktree-… go)", lines)
        self.assertEqual(branches(), ["dev", "feature", "main", "other-x", "worktree-k2"])
        self.assertEqual((clean.exists(), kept.is_dir(), feature.exists()), (False, True, False))
        self.assertNotIn("k3", trees())
        self.assertEqual(self.clean("done", self.main)[0], 1)  # the main tree is never one
        self.assertTrue(self.main.is_dir())

    def test_the_hook_worktree_remove(self):
        def hook(path, session="s1"):
            out, err = io.StringIO(), io.StringIO()
            event = {"session_id": session, "hook_event_name": "WorktreeRemove", "cwd": str(self.main),
                     "worktree_path": str(path) if isinstance(path, Path) else path}  # fmt: skip
            env = {work.RECORDS_ENV: str(Path(self.tmp.name) / "records")}
            with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", err), \
                    mock.patch.dict(os.environ, env):  # fmt: skip
                code = claude_hook.main(["WorktreeRemove"], io.StringIO(json.dumps(event)))
            self.assertEqual(out.getvalue(), "")  # stdout is the hook's JSON or nothing
            return code, err.getvalue().splitlines()

        wt = work.new("h1", self.main)
        self.record(Path("/elsewhere"), agent="other", finished=True)  # the session has a record
        code, err = hook(wt)
        self.assertEqual((code, err[0]), (0, "remove h1 (worktree-h1): no change (no commit after dev, the tree is "
                                             "its HEAD's)"))  # fmt: skip
        self.assertTrue(self.gone(wt))
        self.assertEqual(hook(wt), (0, [f"nothing to remove: no worktree {wt} nor its branch worktree-h1"]))
        wt = work.new("h2", self.main)
        (wt / "a.txt").write_text("changed\n")
        self.assertEqual(hook(wt), (1, ["keep h2 (worktree-h2): not taken: 1 file(s) changed from the base, "
                                        "0 commit(s) after dev"]))  # fmt: skip
        self.assertTrue(wt.is_dir())
        code, err = hook(wt, session="a b")  # argparse refuses it: one line, exit 1
        self.assertEqual((code, len(err)), (1, 1))
        self.assertRegex(err[0], r"^WorktreeRemove: .*not the ID of a session: a b")
        code, err = hook(Path(self.tmp.name) / "elsewhere")
        self.assertNotEqual(code, 0)
        self.assertRegex(err[-1], "is not a worktree under .claude/worktrees/")
        for path in (None, ".claude/worktrees/h2", ""):  # not an absolute path: kept, one line
            with self.subTest(path=path):
                self.assertEqual(hook(path), (1, [f"WorktreeRemove: ValueError: worktree_path is not an absolute "
                                                  f"path: {path!r}"]))  # fmt: skip
        self.assertTrue(wt.is_dir())

    def test_lines(self):
        # X9-20 (U16): from take's base, the WIP commit, the uncommitted change and the untracked files counted; the
        # tests, the data and the test module inside the Rust file left out; the same lines as take's
        wt = work.new("w1", self.main)
        (wt / "m.rs").write_text(Take.RUST)
        git_in(wt, "add", "m.rs")
        git_in(wt, "commit", "-qm", "WIP")
        (wt / "m.rs").write_text(Take.RUST.replace("fn a() {}", "fn a() { b() }\nfn b() {}")
                                 .replace("s.len(), 8);", "s.len(), 9);\n        let e = 1;"))  # fmt: skip
        (wt / "c.py").write_text("x = 1\n" * 30)
        (wt / "tests" / "x.rs").write_text("a\nb\n")
        (wt / "a.txt").write_text("data\n")
        code, lines = quiet_out(work.main, ["lines", "--estimate", "10", "--tree", str(wt)])
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"lines: {wt} from {self.dev[:9]} (git merge-base dev HEAD), uncommitted changes "
                                   "and untracked files too")  # fmt: skip
        # m.rs: 15 lines, 12 of them its test module (from the attribute to the brace); c.py 30
        self.assertIn("  4 file(s), +48 -9; without the tests and the data: +33 -0 (the test modules inside 1 file(s), "
                      "+12 -0, left out)", lines)  # fmt: skip
        self.assertIn("      30      0  c.py  (new)", lines)
        self.assertEqual(lines[-1], "estimate: +33 of the code (without the tests and the data) against 10: 3.30 times; "
                                    "within the size to refactor (rules/budgets.md: over 3 times and 100 lines more)")
        self.assertEqual(git_in(wt, "diff", "--cached", "--name-only"), "")  # the index as before (nothing staged)
        self.assertIn("?? c.py", git_in(wt, "status", "--porcelain"))
        code, taken = self.take("w1", "--estimate", 10)
        self.assertEqual(code, 1, taken)  # no work check: not applied
        self.assertEqual([x for x in taken if x.startswith(("  ", "estimate: "))], lines[1:])
        # --base: from the WIP commit (of the unit before, rules/common.md 2.4), its m.rs (15 lines, new) not counted;
        # m.rs: +2 -1 of code (fn a, fn b) and +2 -1 in its test module
        code, lines = quiet_out(work.main, ["lines", "--base", "HEAD", "--tree", str(wt)])
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"lines: {wt} from HEAD, uncommitted changes and untracked files too")
        self.assertIn("  4 file(s), +37 -11; without the tests and the data: +32 -1 (the test modules inside 1 file(s), "
                      "+2 -1, left out)", lines)  # fmt: skip
        self.assertIn("       4      2  m.rs", lines)
        other = git_in(wt, "commit-tree", "-m", "x", git_in(wt, "write-tree").strip()).strip()
        self.assertEqual(quiet_out(work.main, ["lines", "--base", other, "--tree", str(wt)]),
                         (1, [f"{other} is not an ancestor of the HEAD of {wt}"]))
        plain = Path(self.tmp.name) / "plain"
        plain.mkdir()
        git_in(wt, "add", "-A")
        git_in(wt, "commit", "-qm", "WIP 2")
        (self.main / "a.txt").write_text("dev\n")
        git_in(self.main, "commit", "-qam", "dev")
        merge = subprocess.run(["git", "-C", str(wt), "-c", "user.name=t", "-c", "user.email=t@t", "merge", "-q", "dev"],
                               capture_output=True)  # fmt: skip
        self.assertEqual(merge.returncode, 1)  # stopped on the conflict in a.txt: `add -A` and `reset` would end it
        for tree, says in ((plain, "not the top of a git tree"), (wt, "in a merge (MERGE_HEAD): finish or abort it")):
            with self.subTest(tree=tree):
                self.assertEqual(quiet_out(work.main, ["lines", "--tree", str(tree)]),
                                 (1, [f"lines: {tree}: {says}; nothing done"]))
        # patch and take stop alike in the merge (their `add -A` and `reset` would end it), and write no patch
        out = Path(self.tmp.name) / "m.patch"
        stop = [f"patch: {wt}: in a merge (MERGE_HEAD): finish or abort it; nothing done"]
        self.assertEqual(quiet_out(work.main, ["patch", str(wt), self.dev, str(out), "--main", str(self.main)]),
                         (1, stop))
        self.assertEqual(self.take("w1", "--out", out), (1, stop))
        self.assertFalse(out.exists())
        self.assertEqual(git_in(wt, "diff", "--name-only", "--diff-filter=U"), "a.txt\n")
        self.assertTrue(git_in(wt, "rev-parse", "-q", "--verify", "MERGE_HEAD").strip())

    def test_lines_in_the_main_tree(self):
        # X-17: in the main tree, from HEAD (an agent there commits nothing), the uncommitted change and the untracked
        # file counted, the data left out, the index as before; --base as in a worktree
        (self.main / "d.py").write_text("y = 2\n")
        git_in(self.main, "add", "d.py")
        git_in(self.main, "commit", "-qm", "d")
        head = self.head(self.main)
        (self.main / "d.py").write_text("y = 3\nz = 4\n")
        (self.main / "c.py").write_text("x = 1\n" * 3)
        (self.main / "a.txt").write_text("data\n")
        code, lines = quiet_out(work.main, ["lines", "--tree", str(self.main)])
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"lines: {self.main} from {head[:9]} (HEAD of the main tree), uncommitted changes "
                                   "and untracked files too")  # fmt: skip
        self.assertIn("  3 file(s), +6 -10; without the tests and the data: +5 -1", lines)
        self.assertIn("       3      0  c.py  (new)", lines)
        self.assertEqual(git_in(self.main, "diff", "--cached", "--name-only"), "")
        self.assertIn("?? c.py", git_in(self.main, "status", "--porcelain"))
        code, lines = quiet_out(work.main, ["lines", "--base", self.dev, "--tree", str(self.main)])
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], f"lines: {self.main} from {self.dev}, uncommitted changes and untracked files too")
        self.assertIn("  3 file(s), +6 -9; without the tests and the data: +5 -0", lines)

    def test_lines_and_patch_keep_the_index(self):
        # W4-18 U10e: what is staged, a `git mv` too, stays staged after `lines` (both trees) and `patch`
        wt, out = work.new("w1", self.main), Path(self.tmp.name) / "w1.patch"
        for tree in (self.main, wt):
            git_in(tree, "mv", "a.txt", "moved.txt")
            (tree / "n.py").write_text("x = 1\n")
            git_in(tree, "add", "n.py")
            staged = git_in(tree, "diff", "--cached", "--name-status", "-M")
            self.assertEqual(staged, "R100\ta.txt\tmoved.txt\nA\tn.py\n")
            runs = [["lines", "--tree", str(tree)]]
            runs += [["patch", str(wt), self.dev, str(out), "--main", str(self.main)]] if tree == wt else []
            for argv in runs:
                with self.subTest(tree=tree, cmd=argv[0]):
                    code, lines = quiet_out(work.main, argv)
                    self.assertEqual(code, 0, lines)
                    self.assertIn("       1      0  n.py  (new)", lines)
                    self.assertEqual(git_in(tree, "diff", "--cached", "--name-status", "-M"), staged)

    def test_help(self):
        for name, c in work.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^work\.py {name}( |$)")
                code, lines = quiet_out(work.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        self.assertIn("work check: no need to run it again", "\n".join(quiet_out(work.main, ["help", "patch"])[1]))
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(work.main, ["help", "--role", role])
                want = [n for n, c in work.COMMANDS.items() if role in c.roles]
                got = [x.split()[0] for x in lines if not x.startswith(" ")]
                self.assertEqual((code, got), (0, want or ["（役割"]))
        names = list(work.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(work.main, ["help"])[1][: len(names)]], names)
        # in the order of the work (X-9 U8): an agent's first command first
        self.assertEqual(names, ["sync", "lines", "new", "take", "patch", "check", "apply", "commit", "done", "close",
                                 "remove"])  # fmt: skip
        self.assertEqual(quiet_out(work.main, ["help", "--role", "i"])[1][0].split()[0], "sync")


class WorkSync(unittest.TestCase):
    """tools/work.py (X-9 U6): an agent's `sync` in its worktree and the parent's `commit` in the main tree."""

    LINES = "".join(f"{i}\n" for i in range(1, 10))

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.main = Path(self.tmp.name).resolve() / "main"
        git_in(self.tmp.name, "init", "-q", "-b", "dev", str(self.main))
        for key, value in (("user.name", "t"), ("user.email", "t@t"), ("commit.gpgsign", "false")):
            git_in(self.main, "config", key, value)  # the tool's own commits, in the worktrees too
        (self.main / ".git" / "info" / "exclude").write_text("target/\n.claude/\n")
        for name in ("a.txt", "b.txt", "c.txt"):
            (self.main / name).write_text(self.LINES)
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "base")
        self.base = self.head(self.main)

    def head(self, tree, rev="HEAD"):
        return git_in(tree, "rev-parse", rev).strip()

    def on_dev(self, name, text):
        (self.main / name).write_text(text)
        git_in(self.main, "commit", "-qam", f"dev {name}")

    def sync(self, tree, *argv):
        return quiet_out(work.main, ["sync", *map(str, argv), "--tree", str(tree)])

    def subjects(self, tree, n):
        return git_in(tree, "log", f"-{n}", "--format=%s").split("\n")[:n]

    def test_sync_stops_without_a_worktree_or_in_a_merge(self):
        wt = work.new("w1", self.main)
        self.on_dev("a.txt", "dev\n")
        plain = Path(self.tmp.name) / "plain"
        plain.mkdir()
        git_in(wt, "checkout", "-q", "--detach")
        for tree, says in ((self.main, "the main tree; sync is for a worktree"), (plain, "not the top of a git tree"),
                           (wt, "HEAD is on no branch")):  # fmt: skip
            with self.subTest(tree=tree):
                self.assertEqual(self.sync(tree), (1, [f"sync: {tree}: {says}; nothing done"]))
        self.assertEqual(self.head(wt), self.base)
        git_in(wt, "checkout", "-q", "worktree-w1")
        (wt / "a.txt").write_text("mine\n")  # a conflict: the merge stops in the middle
        code, lines = self.sync(wt)
        self.assertEqual(code, 1, lines)
        wip = git_in(wt, "rev-parse", "--short", "HEAD").strip()
        self.assertEqual(lines[:3], [f"sync: committed 'WIP: before sync with dev' ({wip})",
                                     "sync: the merge of dev stopped with conflicts; resolve them and commit "
                                     "(rules/common.md 2.2):", "  a.txt"])  # fmt: skip
        self.assertRegex(lines[-1], r"^sync: worktree-w1, HEAD \w+, dev \w+; 1 commit\(s\) after dev, 0 commit\(s\) of "
                                    r"dev taken in, \d+ uncommitted change\(s\)$")  # fmt: skip
        self.assertEqual(git_in(wt, "rev-parse", "-q", "--verify", "MERGE_HEAD").strip(), self.head(self.main))
        self.assertEqual(self.sync(wt), (1, [f"sync: {wt}: in a merge (MERGE_HEAD): finish or abort it; nothing done"]))

    def test_sync_forwards_or_merges(self):
        wt = work.new("w1", self.main)
        code, lines = self.sync(wt)  # dev has not moved
        self.assertEqual((code, lines[0]), (0, "sync: dev is in HEAD already; nothing to take in"))
        self.assertEqual(self.head(wt), self.base)
        self.on_dev("a.txt", "dev 1\n")
        code, lines = self.sync(wt)  # no commit, no change: fast-forward
        self.assertEqual((code, lines[0], self.head(wt)), (0, "sync: fast-forwarded to dev", self.head(self.main)))
        self.assertRegex(lines[-1], r"; 0 commit\(s\) after dev, 1 commit\(s\) of dev taken in, 0 uncommitted change")
        self.on_dev("a.txt", "dev 2\n")
        (wt / "n.txt").write_text("new\n")  # an untracked file alone: a WIP commit, then the merge
        code, lines = self.sync(wt, "-m", "WIP: X-9 U6")
        self.assertEqual((code, lines[1]), (0, "sync: merged dev"), lines)
        self.assertEqual(self.subjects(wt, 2)[1], "WIP: X-9 U6")
        self.assertEqual(len(git_in(wt, "log", "-1", "--format=%P").split()), 2)
        self.assertRegex(lines[-1], r"; 2 commit\(s\) after dev, 1 commit\(s\) of dev taken in, 0 uncommitted change")
        self.on_dev("b.txt", "dev 3\n")
        code, lines = self.sync(wt)  # the commits of the branch alone: the merge, no WIP
        self.assertEqual((code, lines[0]), (0, "sync: merged dev"))
        self.assertEqual(self.head(wt, "HEAD^2"), self.head(self.main))
        self.assertEqual((wt / "b.txt").read_text(), "dev 3\n")

    def patch_of(self, name, new):
        """A patch of `name` from the base to `new`, made in the main tree (put back after)."""
        (self.main / name).write_text(new)
        out = Path(self.tmp.name) / f"{name}.patch"
        out.write_text(git_in(self.main, "diff", "--binary", "--", name))
        git_in(self.main, "checkout", "-q", "--", name)
        return out

    def test_sync_apply(self):
        wt = work.new("w1", self.main)
        p = self.patch_of("a.txt", self.LINES.replace("2\n", "two\n"))
        code, lines = self.sync(wt, "--apply", p)
        self.assertEqual(code, 0, lines)
        self.assertEqual((self.subjects(wt, 1), git_in(wt, "status", "--porcelain")), (["WIP: apply a.txt.patch"], ""))
        self.assertIn("two\n", (wt / "a.txt").read_text())
        rows = [json.loads(x) for x in (self.main / work.TAKEN).read_text().splitlines()]
        self.assertEqual((rows[-1]["kind"], rows[-1]["to"]), ("apply", str(wt)))  # recorded as `apply` does
        head = self.head(wt)
        code, lines = self.sync(wt, "--apply", p)  # there already: nothing
        self.assertEqual((code, self.head(wt)), (0, head))
        self.assertIn(f"applies: {work.ALREADY}", lines)
        # uncommitted changes in its files: not applied
        q = self.patch_of("b.txt", self.LINES.replace("5\n", "five\n"))
        (wt / "b.txt").write_text(self.LINES + "mine\n")
        code, lines = self.sync(wt, "--apply", q)
        self.assertEqual((code, self.head(wt)), (1, head))
        self.assertIn("sync: not applied: the tree has uncommitted changes in the files of the patch", lines)
        git_in(wt, "checkout", "--", "b.txt")
        # 3-way with conflicts: not committed, the conflicts listed
        (wt / "b.txt").write_text(self.LINES.replace("5\n", "FIVE\n"))
        git_in(wt, "commit", "-qam", "WIP mine")
        head = self.head(wt)
        code, lines = self.sync(wt, "--apply", q)
        self.assertEqual((code, self.head(wt)), (1, head), lines)
        self.assertIn("sync: the patch did not apply cleanly; nothing committed; conflicts: b.txt", lines)
        git_in(wt, "checkout", "--", "b.txt")
        # one that applies neither way: the reason, nothing committed
        r = Path(self.tmp.name) / "r.patch"  # a blob not in the repository: no 3-way either
        r.write_text("diff --git a/c.txt b/c.txt\nindex 1234567..89abcde 100644\n--- a/c.txt\n+++ b/c.txt\n"
                     "@@ -1,2 +1,2 @@\n x\n-y\n+z\n")  # fmt: skip
        code, lines = self.sync(wt, "--apply", r)
        self.assertEqual((code, self.head(wt)), (1, head))
        self.assertIn("the patch does not apply, plain nor with -3:", "\n".join(lines))
        self.assertRegex(lines[-1], r"^sync: worktree-w1, HEAD ")

    # ------------------------------------------------ commit

    def commit(self, *argv):
        return quiet_out(work.main, ["commit", *map(str, argv), "--tree", str(self.main)])

    def files_of(self, rev="HEAD"):
        return sorted(git_in(self.main, "diff-tree", "--root", "--no-commit-id", "--name-only", "-r", rev).split())

    def test_commit_the_paths_named_alone(self):
        (self.main / "a.txt").write_text("changed\n")
        (self.main / "c.txt").unlink()
        (self.main / "d").mkdir()
        (self.main / "d" / "n.txt").write_text("new\n")  # untracked, under a directory named
        (self.main / "b.txt").write_text("staged\n")
        git_in(self.main, "add", "b.txt")
        (self.main / "e.txt").write_text("other\n")  # untracked, not named
        code, lines = self.commit("-m", "subject", "-m", "a paragraph", "a.txt", "c.txt", "d", "nosuch.txt")
        self.assertEqual(code, 0, lines)
        self.assertEqual(lines[0], "commit: no change in nosuch.txt")
        self.assertRegex(lines[-2], r"^commit \w+ on dev: 3 file\(s\); 2 uncommitted change\(s\) not in it$")
        self.assertEqual(lines[-1], NOTHING)  # X-1 U13
        self.assertEqual(self.files_of(), ["a.txt", "c.txt", "d/n.txt"])
        self.assertEqual(git_in(self.main, "log", "-1", "--format=%B"), "subject\n\na paragraph\n\n")
        self.assertEqual(sorted(git_in(self.main, "status", "--porcelain").splitlines()), ["?? e.txt", "M  b.txt"])
        head = self.head(self.main)
        code, lines = self.commit("-m", "x", "a.txt", "nosuch.txt")  # no change at all
        self.assertEqual((code, self.head(self.main)), (1, head))
        self.assertEqual(lines, ["commit: no change in a.txt, nosuch.txt",
                                 "commit: none of the paths named has a change; nothing committed",
                                 "commit: the index is as before"])  # fmt: skip

    def test_commit_trailers(self):
        (self.main / "a.txt").write_text("changed\n")
        body = Path(self.tmp.name) / "body.txt"
        body.write_text("from a file\n")
        short = lambda rev: git_in(self.main, "rev-parse", "--short", rev).strip()  # noqa: E731
        # a long hash and a name (HEAD, a branch) are written as short hashes: HEAD would read as another commit later
        rng, written = f"{self.base}..HEAD", f"{short(self.base)}..{short('HEAD')}"
        self.assertNotEqual(rng, written)
        code, lines = self.commit("-m", "take in the check", "-F", body, "a.txt", "--docs-checked", rng, "X-9",
                                  "--co-author", "A B <a@b.c>")  # fmt: skip
        self.assertEqual(code, 0, lines)
        self.assertEqual(len(lines), 2, lines)  # docs.last_docs_check reads it: no line
        value = f"{written} (X-9, onsa-docs)"
        self.assertEqual(git_in(self.main, "log", "-1", "--format=%B"),
                         f"take in the check\n\nfrom a file\n\nDocs-Checked: {value}\nCo-Authored-By: A B <a@b.c>\n\n")
        self.assertEqual(docs_tool.last_docs_check(self.main), (self.head(self.main), value))
        # the ends of the range are commits, else nothing is done
        (self.main / "b.txt").write_text("changed\n")
        head = self.head(self.main)
        for bad in ("nosuch..HEAD", "HEAD", f"{self.base}...HEAD", "..HEAD", f"HEAD:a.txt..HEAD"):
            with self.subTest(bad=bad):
                code, lines = self.commit("-m", "x", "b.txt", "--docs-checked", bad, "X-9")
                self.assertEqual((code, lines), (1, [f"commit: {bad} is not <A>..<B> of two commits of {self.main}; "
                                                     "nothing done"]))  # fmt: skip
        self.assertEqual(self.head(self.main), head)
        branch = git_in(self.main, "branch", "--show-current").strip()
        code, lines = self.commit("-m", "x", "b.txt", "--docs-checked", f"HEAD~1..{branch}", "X-9")
        self.assertEqual(code, 0, lines)
        self.assertEqual(docs_tool.last_docs_check(self.main)[1], f"{short('HEAD~2')}..{short('HEAD~1')} (X-9, onsa-docs)")
        with self.assertRaises(SystemExit) as e:
            quiet_out(work.main, ["commit", "-m", "x", "b.txt", "--co-author", "no mail", "--tree", str(self.main)])
        self.assertEqual(e.exception.code, 2)

    def documents(self):
        for rel, text in NEW_LAYOUT.items():
            (self.main / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.main / rel).write_text(text, encoding="utf-8")
        self.assertEqual(quiet(docs_tool.main, ["set", "W1-01", "status=DOING", "--root", str(self.main)]), 0)
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "documents")
        return self.main / "tasks" / "W" / "W1-01.md"

    def test_commit_done(self):
        w1 = self.documents()
        (self.main / "a.txt").write_text("changed\n")
        code, lines = self.commit("-m", "the work", "a.txt", "--done", "W1-01")
        self.assertEqual(code, 0, lines)
        self.assertEqual(self.files_of(), ["a.txt", "tasks/W/W1-01.md"])
        self.assertIn('status = "DONE"', git_in(self.main, "show", "HEAD:tasks/W/W1-01.md"))
        self.assertEqual(git_in(self.main, "status", "--porcelain"), "")
        self.assertIn('status = "DONE"', w1.read_text())
        code, lines = self.commit("-m", "again", "--done", "W1-01")  # DONE already: no change
        self.assertEqual(code, 1, lines)
        self.assertIn("commit: no change in tasks/W/W1-01.md", lines)
        code, lines = self.commit("-m", "x", "--done", "W9-99")
        self.assertEqual(code, 1)
        self.assertIn("commit: --done W9-99: no file of it; nothing done", lines)
        self.assertEqual(self.commit("-m", "x"), (1, ["commit: name the paths to commit (or --done)"]))

    def test_a_failed_commit_puts_the_tree_back(self):
        w1 = self.documents()
        held = w1.read_bytes()
        hooks = Path(self.tmp.name) / "hooks"
        hooks.mkdir()
        (hooks / "pre-commit").write_text("#!/bin/sh\nexit 1\n")
        (hooks / "pre-commit").chmod(0o755)
        git_in(self.main, "config", "core.hooksPath", str(hooks))
        (self.main / "n.txt").write_text("new\n")
        (self.main / "b.txt").write_text("staged\n")
        git_in(self.main, "add", "b.txt")
        head, status = self.head(self.main), git_in(self.main, "status", "--porcelain")
        code, lines = self.commit("-m", "x", "n.txt", "--done", "W1-01")
        self.assertEqual(code, 1, lines)
        self.assertEqual(lines[-1], "commit: the index and the file of --done are as before")
        self.assertEqual((self.head(self.main), git_in(self.main, "status", "--porcelain"), w1.read_bytes()),
                         (head, status, held))  # fmt: skip


if __name__ == "__main__":
    unittest.main(verbosity=1)
