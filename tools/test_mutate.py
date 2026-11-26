#!/usr/bin/env python3
"""Self-tests of tools/mutate.py (tools/selftest.py runs every self-test): a made-up tree and `sh` commands, no cargo.

Alone: python3 -B tools/test_mutate.py
"""
import io
import json
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import mutate  # noqa: E402
import repo  # noqa: E402
from selftest_support import quiet_out  # noqa: E402

A = "fn a() {\n    x < y\n}\n"
B = "let b = 1;\nlet c = 2;\n"


def toml_str(s):
    return "'''\n" + s + "'''" if "\n" in s else json.dumps(s)


def command(label, script, env=None):
    e = "" if env is None else "env = { " + ", ".join(f'{k} = "{v}"' for k, v in env.items()) + " }\n"
    return f'[[command]]\nlabel = "{label}"\nrun = ["sh", "-c", {toml_str(script)}]\n{e}\n'


def mutant(name, path, before, after, *more):
    text = f'[[mutant]]\nname = "{name}"\npath = "{path}"\nbefore = {toml_str(before)}\nafter = {toml_str(after)}\n'
    for p, b, a in more:
        text += f'[[mutant.more]]\npath = "{p}"\nbefore = {toml_str(b)}\nafter = {toml_str(a)}\n'
    return text + "\n"


# A command that fails when the mutant `<` -> `<=` is in, as a test would.
CHECK_A = "grep -q '<=' a.rs && { echo 'test m::a_le ... FAILED'; echo 'test m::b ... FAILED'; exit 101; }; exit 0"


class Mutate(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.tree = self.root / "tree"
        (self.tree / "sub").mkdir(parents=True)
        (self.tree / "a.rs").write_text(A)
        (self.tree / "sub" / "b.rs").write_text(B)
        self.list = self.root / "m.toml"

    def tearDown(self):
        self.tmp.cleanup()

    def run_tool(self, text, *args, cmd="run"):
        self.list.write_text(text)
        return quiet_out(mutate.main, [cmd, str(self.tree), str(self.list), *args])

    def assertBack(self):
        self.assertEqual(((self.tree / "a.rs").read_text(), (self.tree / "sub" / "b.rs").read_text()), (A, B))
        self.assertFalse((self.tree / mutate.BACKUP).exists())

    def lines(self, out):
        """{name: the result} of the lines of `run` (the seconds cut)."""
        return {x.split("  ")[0]: x.split("  ")[1] for x in out if not x.startswith("mutate")}

    def test_results_and_order(self):
        # (a): LIVED, killed by the first failing command (its tests), the third command not run
        mark = self.root / "third_ran"
        text = (command("one", "exit 0") + command("two", CHECK_A) + command("three", f"touch {mark}; exit 1")
                + mutant("le", "a.rs", "x < y", "x <= y") + mutant("same", "sub/b.rs", "let c", "let  c"))  # fmt: skip
        code, out = self.run_tool(text, "le")
        self.assertEqual((code, self.lines(out)), (0, {"le": "killed by two [m::a_le, m::b]"}))
        self.assertFalse(mark.exists())
        self.assertIn("mutate: 1 mutant(s): killed 1", out)
        self.assertBack()
        code, out = self.run_tool(text.replace(f"touch {mark}; exit 1", "exit 0"))
        self.assertEqual((code, self.lines(out)), (0, {"le": "killed by two [m::a_le, m::b]", "same": "LIVED"}))
        self.assertBack()

    def test_compile_error_and_shown_names(self):
        names = "".join(f"echo 'test t{i} ... FAILED'; " for i in range(5))
        text = (command("c", "grep -q '<=' a.rs && { echo 'error: could not compile `x`'; exit 101; }; exit 0")
                + command("t", names + "exit 101") + mutant("le", "a.rs", "x < y", "x <= y")
                + mutant("b", "sub/b.rs", "1", "3"))  # fmt: skip
        code, out = self.run_tool(text)
        self.assertEqual((code, self.lines(out)), (0, {"le": "COMPILE-ERROR c", "b": "killed by t [t0, t1, t2 +2]"}))
        self.assertBack()

    def test_bad_match(self):
        # (b): found 0 and 2 times, a file that is not there; nothing run, the tree as it was
        mark = self.root / "ran"
        text = (command("one", f"touch {mark}") + mutant("none", "a.rs", "z", "w")
                + mutant("two", "sub/b.rs", "let", "var") + mutant("gone", "c.rs", "a", "b")
                + mutant("second", "a.rs", "x", "z", ("a.rs", "x", "w")))  # fmt: skip
        code, out = self.run_tool(text)
        want = {"none": "BAD-MATCH 0", "two": "BAD-MATCH 2", "gone": "BAD-MATCH no file c.rs",
                "second": "BAD-MATCH 1,0"}  # fmt: skip
        self.assertEqual((code, self.lines(out)), (1, want))
        self.assertFalse(mark.exists())
        self.assertBack()

    def test_back_after_a_timeout_and_the_env(self):
        # (c): put back after a failure (above) and a timeout; the command sees the mutant and its env; the child
        # of the command that timed out is killed too (its output away from the pipe: not waited for by `communicate`)
        pid = self.root / "pid"
        text = (command("env", 'test "$K" = v && grep -q "x <= y" a.rs', {"K": "v"})
                + command("slow", f"sleep 30 > /dev/null 2>&1 & echo $! > {pid}; wait")
                + mutant("le", "a.rs", "x < y", "x <= y"))  # fmt: skip
        code, out = self.run_tool(text, "--timeout", "0.3")
        self.assertEqual((code, self.lines(out)), (0, {"le": "TIMEOUT slow"}))
        self.assertBack()
        for _ in range(50):  # the killed child is reaped by init: up to a second
            try:
                os.kill(int(pid.read_text()), 0)
            except ProcessLookupError:
                break
            time.sleep(0.02)
        else:
            self.fail("the child of the command is left")

    def test_multi_line_and_more_places(self):
        # (f): a `before` and an `after` of several lines, and two files of one mutant
        before, after = "fn a() {\n    x < y\n", "fn a() {\n    y > x\n    // two lines\n"
        check = "grep -q 'y > x' a.rs && grep -q 'two lines' a.rs && grep -q 'c = 9' sub/b.rs && exit 1; exit 0"
        text = command("t", check) + mutant("ml", "a.rs", before, after, ("sub/b.rs", "c = 2", "c = 9"))
        self.assertEqual(self.run_tool(text, cmd="match")[0], 0)
        code, out = self.run_tool(text)
        self.assertEqual((code, self.lines(out)), (0, {"ml": "killed by t"}))
        self.assertBack()

    def test_a_backup_left(self):
        # (d): a backup left stops run and match; restore puts the tree back; a file changed by hand stops it
        text = command("t", "exit 1") + mutant("le", "a.rs", "x < y", "x <= y")
        (self.tree / "target").mkdir()
        saved = {"name": "le", "files": {"a.rs": {"text": A, "mutated": A.replace("<", "<=")}}}
        (self.tree / mutate.BACKUP).write_text(json.dumps(saved))
        (self.tree / "a.rs").write_text(A.replace("<", "<="))
        for cmd in ("run", "match"):
            code, out = self.run_tool(text, cmd=cmd)
            self.assertEqual(code, 1)
            self.assertIn(f"`mutate.py restore {self.tree.resolve()}`", out[0])
        self.assertEqual((self.tree / "a.rs").read_text(), A.replace("<", "<="))
        (self.tree / "a.rs").write_text("edited")
        code, out = quiet_out(mutate.main, ["restore", str(self.tree)])
        self.assertEqual((code, (self.tree / "a.rs").read_text()), (1, "edited"))
        self.assertIn("not put back: a.rs", out[0])
        self.assertTrue((self.tree / mutate.BACKUP).exists())
        (self.tree / "a.rs").write_text(A.replace("<", "<="))
        self.assertEqual(quiet_out(mutate.main, ["restore", str(self.tree)])[0], 0)
        self.assertBack()
        self.assertEqual(quiet_out(mutate.main, ["restore", str(self.tree)])[0], 1)  # no backup

    def test_changed_while_running(self):
        # the command edits the file: not put back, the backup kept, the run stopped (exit 1)
        text = command("t", "echo edited > a.rs") + mutant("le", "a.rs", "x < y", "x <= y") + mutant("b", "sub/b.rs", "1", "3")
        code, out = self.run_tool(text)
        self.assertEqual(code, 1)
        self.assertIn("not put back: a.rs", out[-1])
        self.assertEqual(((self.tree / "a.rs").read_text(), (self.tree / "sub/b.rs").read_text()), ("edited\n", B))
        self.assertTrue((self.tree / mutate.BACKUP).exists())

    def test_not_utf8(self):
        # a file that is not UTF-8 is an error of the run (exit 1), in `put_in` and in `restore`
        (self.tree / "c.bin").write_bytes(b"\xff\xfe x")
        code, out = self.run_tool(command("t", "exit 0") + mutant("c", "c.bin", "x", "y"))
        self.assertEqual(code, 1)
        self.assertIn("c.bin is not UTF-8", "\n".join(out))
        (self.tree / "target").mkdir(exist_ok=True)  # made by `run`
        (self.tree / mutate.BACKUP).write_text(json.dumps({"name": "c", "files": {"c.bin": {"text": "x", "mutated": "y"}}}))
        code, out = quiet_out(mutate.main, ["restore", str(self.tree)])
        self.assertEqual((code, (self.tree / "c.bin").read_bytes()), (1, b"\xff\xfe x"))
        self.assertIn("c.bin is not UTF-8", out[0])
        self.assertTrue((self.tree / mutate.BACKUP).exists())

    def test_match(self):
        # (e): the counts of each mutant, no command run
        mark = self.root / "ran"
        text = command("one", f"touch {mark}") + mutant("le", "a.rs", "x < y", "x <= y") + mutant("two", "sub/b.rs", "let", "v")
        code, out = self.run_tool(text, cmd="match")
        self.assertEqual((code, out[:2]), (1, ["le  ok  (1 place(s))", "two  BAD-MATCH 2  (1 place(s))"]))
        self.assertIn("BAD-MATCH 1", out[2])
        self.assertEqual(self.run_tool(text, "le", cmd="match")[0], 0)
        self.assertFalse(mark.exists())
        self.assertBack()

    def test_errors_of_the_list(self):
        ok = command("t", "exit 0") + mutant("le", "a.rs", "x < y", "x <= y")
        for text, needle in (
            (command("t", "exit 0"), "the keys are"),  # no mutant table
            (ok.replace("label", "lable"), "the keys are"),
            (ok + mutant("le", "a.rs", "x", "z"), "taken"),
            (command("t", "exit 0") + mutant("s", "a.rs", "x", "x"), "not the same as after"),
            (command("t", "exit 0") + mutant("s", "../a.rs", "x", "y"), "not inside the tree"),
            (ok.replace('run = ["sh", "-c", "exit 0"]', "run = []"), "run words"),
            (ok.replace('run = ["sh", "-c", "exit 0"]', 'run = "no-such-command-of-mutate"'), "cannot run"),
            (ok + "[[mutant]]\nname = 'x'\nbefore = 'a'\nafter = 'b'\n", "the keys are"),
            ("[[mutant", "m.toml"),
        ):
            with self.subTest(needle=needle):
                code, out = self.run_tool(text)
                self.assertEqual(code, 1)
                self.assertIn(needle, "\n".join(out))
                self.assertBack()
        self.assertEqual(self.run_tool(ok, "nope")[0], 1)

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in mutate.COMMANDS.items():
            with self.subTest(name=name):
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^mutate\.py {name}( |$)")
                code, lines = quiet_out(mutate.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            code, lines = quiet_out(mutate.main, ["help", "--role", role])
            want = [n for n, c in mutate.COMMANDS.items() if role in c.roles]
            self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        code, lines = quiet_out(mutate.main, ["help"])
        self.assertEqual([x.split()[0] for x in lines[:3]], ["run", "match", "restore"])
        self.assertIn("waiting-clean", "\n".join(lines))
        with mock.patch.object(sys, "stderr", io.StringIO()), self.assertRaises(SystemExit) as e:
            mutate.main([])
        self.assertEqual(e.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
