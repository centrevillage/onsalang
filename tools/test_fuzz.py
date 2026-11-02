#!/usr/bin/env python3
"""Self-tests of tools/fuzz.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_fuzz.py
"""
import dataclasses
import io
import os
import re
import shutil
import sys
import tomllib
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz  # noqa: E402
import narrowing  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402
from selftest_support import entry, FAKE_SERVE, quiet, quiet_out, TempRepo  # noqa: E402


def allowed(cls, inp, reasons=("S-45",), note="n", left="m"):
    """An entry of `tests/fuzz/allowed.toml` (R-207)."""
    rs = ", ".join(f'"{r}"' for r in reasons)
    return (f"[[allowed]]\nclass = {spec_blocks.toml_string(cls)}\nleft = {spec_blocks.toml_string(left)}\n"
            f"input = {spec_blocks.toml_string(inp)}\nreasons = [{rs}]\nnote = \"{note}\"\n\n")


# A stand-in for the compiler: an input with `X` is an internal error, one with
# `Y` a raw panic in the `check` command only, one with `Z` a signal, one that
# ends with `@` (no newline after it) another internal error. The signal is
# SIGKILL: an abort would make the system write a crash report.
FAKE_ONSA = r"""
import os, sys
text = open(sys.argv[-1], encoding="utf-8").read()
check = sys.argv[1] == "check"
if "X" in text:
    sys.stderr.write("onsa: internal error: index out of bounds: the len is 3 but the index is 7\n"
                     "  = at crates/onsa_sema/src/body.rs:12:5\n")
    sys.exit(101)
if text.endswith("@"):
    sys.stderr.write("onsa: internal error: range end index 4 out of range for slice of length 3\n"
                     "  = at crates/onsa_sema/src/layout.rs:7:9\n")
    sys.exit(101)
if "Y" in text and check:
    sys.stderr.write("thread 'main' panicked at crates/a.rs:1:1:\nboom\n")
    sys.exit(0)
if "Z" in text:
    os.kill(os.getpid(), 9)
sys.exit(1 if "e" in text else 0)
"""


# A stand-in for `onsa_cases --fix-same-place` (W3-17): an input with `BADCANDIDATE` breaks the
# contract of a fix candidate; with `CRASH_FIX` in a path list's first input, the tool fails.
FAKE_CASES = FAKE_SERVE + r"""
import json, sys
assert sys.argv[1] == "--fix-same-place"
out = []
for path in sys.argv[2:]:
    text = open(path, encoding="utf-8", errors="surrogateescape").read()
    if "CRASH_FIX" in text:
        sys.stderr.write("boom\n")
        sys.exit(3)
    v = []
    if "BADCANDIDATE" in text:
        v.append({"code": "E0010", "line": 1, "col": 1, "title": "parenthesize the `&&` of 12", "left": "E0010",
                  "left_line": 1, "left_col": 1, "message": "m"})
    out.append({"file": path, "candidates": len(v), "violations": v, "internal": None})
print(json.dumps(out))
"""


class Fuzz(TempRepo):
    def setUp(self):
        super().setUp()
        self.fake = self.repo.write("fake_onsa.py", FAKE_ONSA)
        self.argv = [sys.executable, "-B", str(self.fake)]
        self.fix_argv = [sys.executable, "-B", str(self.repo.write("fake_cases.py", FAKE_CASES))]

    def go(self, per_seed=0, save=False, truncated=fuzz.TRUNCATIONS, swept=False):
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, per_seed, "t", 2, save, out=lines.append,
                        truncated=truncated, swept=swept)
        return code, "\n".join(lines)

    def test_classify(self):
        self.assertIsNone(fuzz.classify(("check",), 1, "x.onsa:1:1: error[E0002]: ..."))
        c = fuzz.classify(
            ("check",), 101,
            "onsa: internal error: byte index 29 is not a char boundary; it is inside '辞' (bytes 28..31) of `\"{辞\n"
            "fn f() {`\n  --> m.onsa:1:1\n  = at crates/onsa_syntax/src/lexer.rs:283:34\n",
        )
        self.assertEqual(
            c.signature,
            "internal|crates/onsa_syntax/src/lexer.rs|byte index # is not a char boundary; it is inside '?' (bytes #..#) of `…`",
        )
        # a quoted name stays: two different panics are two classes
        a = fuzz.classify(("check",), 101, "onsa: internal error: called `Option::unwrap()` on a `None` value\n"
                          "  = at crates/a.rs:1:1\n")
        b = fuzz.classify(("check",), 101, "onsa: internal error: called `Result::unwrap()` on an `Err` value\n"
                          "  = at crates/a.rs:1:1\n")
        self.assertIn("`Option::unwrap()`", a.signature)
        self.assertNotEqual(a.signature, b.signature)
        lowering = fuzz.classify(("check",), 101, "onsa: internal error: internal lowering error: no field\n  --> m.onsa:1:1\n")
        self.assertEqual(lowering.signature, "internal|-|internal lowering error: no field")
        raw = fuzz.classify(("fmt", "--check"), 0, "thread 'main' panicked at a.rs:1:1:\n")
        self.assertEqual(raw.command, "fmt --check")
        overflow = fuzz.classify(("check",), -6, "thread 'main' has overflowed its stack\nfatal runtime error: stack overflow\n")
        self.assertTrue(overflow.signature.startswith("signal 6|check|"), overflow)
        self.assertEqual(fuzz.classify(("check",), None, "", timed_out=True).signature, "timeout")

    def test_mutants_are_the_same_for_the_same_seeds(self):
        files = [("tests/a.onsa", "pub fn f() -> I32 {\n  1\n}\n"), ("tests/b.onsa", "let x = 2\n")]
        a = fuzz.mutants(files, 5, "1")
        self.assertEqual(a, fuzz.mutants(files, 5, "1"))
        self.assertEqual(len(a), 10)
        self.assertNotEqual(a, fuzz.mutants(files, 5, "2"))
        # a new seed file does not change the mutants of the others
        more = fuzz.mutants(files + [("tests/c.onsa", "x\n")], 5, "1")
        self.assertEqual([m for m in more if m[0] != "tests/c.onsa"], a)

    def test_truncations_are_the_same_for_the_same_seeds(self):
        # FZ-1: each seed cut at the end of a token, with no blank or newline at the end of the file
        text = "// a comment: (x, y)\npub fn f(x: I32) -> I32 {\n  let y = x@3 ~ _\n  y\n}\n"
        files = [("tests/a.onsa", text), ("tests/b.onsa", "let x = 2\n")]
        a = fuzz.truncations(files, 50, "1")
        self.assertEqual(a, fuzz.truncations(files, 50, "1"))
        self.assertEqual(len(a), 100)
        self.assertNotEqual(a, fuzz.truncations(files, 50, "2"))
        self.assertEqual(len(fuzz.truncations(files, 0, "1")), 0)
        for path, k, t in a:
            seed = dict(files)[path]
            with self.subTest(path=path, k=k, t=t):
                self.assertTrue(t and seed.startswith(t), t)
                self.assertNotIn(t[-1], " \t\r\n")
                self.assertNotIn("//", t.rsplit("\n", 1)[-1])  # never inside the comment
                # at the end of a token: the next character of the seed does not continue a name or a number
                self.assertFalse(re.fullmatch(r"\w\w", seed[len(t) - 1:len(t) + 1]), seed[len(t):])
        # most of the cuts come right after a symbol, some after a name or a number
        after = [t for p, _, t in a if p == "tests/a.onsa" and fuzz.CUT_AFTER.search(t[-1])]
        self.assertGreater(len(after), 25)
        self.assertLess(len(after), 50)
        self.assertTrue(any(t.endswith("@") for _, _, t in a), a)
        # a symbol rare in the corpus is cut after as often as a common one: the one `@` among 30 `(`
        rare = fuzz.truncations([("tests/a.onsa", "f(" * 30 + "x@1\n"), ("tests/b.onsa", "g(" * 200 + "\n")], 40, "1")
        self.assertGreater(sum(1 for p, _, t in rare if p == "tests/a.onsa" and t.endswith("x@")), 20, rare)
        # a seed with no token (only a comment, or empty) gives itself without the blanks at its end
        self.assertEqual(fuzz.truncations([("tests/c.onsa", "// c\n\n")], 2, "1"),
                         [("tests/c.onsa", 0, "// c"), ("tests/c.onsa", 1, "// c")])
        self.assertEqual(fuzz.truncations([("tests/e.onsa", "")], 1, "1"), [("tests/e.onsa", 0, "")])

    # FZ-1: `_` inside a name, a line comment (its words and its end: the `?` and the `!` of the comments
    # end them), a string (its `@` and `//` are code), the operators `* / %` and the backslash.
    CUT_TEXT = 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//t"~\n// end!\n'

    def test_cut_sites_are_exact(self):
        after, ends = fuzz.cut_sites(self.CUT_TEXT)
        self.assertEqual(after, {"(": [4], "_": [5], "*": [8], "/": [11, 34, 35], "%": [14], "\\": [17],
                                 "@": [30, 33], '"': [31, 37], "~": [38]})
        self.assertEqual(ends, [3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 29, 31, 32, 34, 35, 36, 38])
        # the rare symbols of the sweep are symbols of CUT_AFTER (else `cut_sites` never gives them)
        self.assertTrue(all(fuzz.CUT_AFTER.fullmatch(c) for c in fuzz.RARE), fuzz.RARE)
        self.assertEqual(sorted(fuzz.RARE), sorted("~!?'^@#/\\%"))
        self.assertEqual(sorted(fuzz.RARE), sorted(set(fuzz.RARE)))

    def test_sweep_cuts_after_every_rare_symbol(self):
        # FZ-1: every place right after a rare symbol, outside a line comment and not at its end (the
        # first `/` of a comment is in it), in the order of the seeds and the places; the same text
        # once; no generator (no version). `*` is not rare: no cut after it.
        files = [("tests/a.onsa", self.CUT_TEXT), ("tests/b.onsa", "x@\n// ^\n"), ("tests/c.onsa", "y ~ z\n"),
                 ("tests/d.onsa", "a'b' #[c] !d ?e ^f\n")]
        self.assertEqual(fuzz.sweep(files), [
            ("tests/a.onsa", "sweep `/` at 1:11", "a_b(_) * c/"),
            ("tests/a.onsa", "sweep `%` at 1:14", "a_b(_) * c/d %"),
            ("tests/a.onsa", "sweep `\\` at 1:17", "a_b(_) * c/d % e\\"),
            ("tests/a.onsa", "sweep `@` at 2:2", 'a_b(_) * c/d % e\\f // g@ h?\nx@'),
            ("tests/a.onsa", "sweep `@` at 2:5", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@'),
            ("tests/a.onsa", "sweep `/` at 2:6", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@/'),
            ("tests/a.onsa", "sweep `/` at 2:7", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//'),
            ("tests/a.onsa", "sweep `~` at 2:10", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//t"~'),
            ("tests/b.onsa", "sweep `@` at 1:2", "x@"),
            ("tests/c.onsa", "sweep `~` at 1:3", "y ~"),
            ("tests/d.onsa", "sweep `'` at 1:2", "a'"),
            ("tests/d.onsa", "sweep `'` at 1:4", "a'b'"),
            ("tests/d.onsa", "sweep `#` at 1:6", "a'b' #"),
            ("tests/d.onsa", "sweep `!` at 1:11", "a'b' #[c] !"),
            ("tests/d.onsa", "sweep `?` at 1:14", "a'b' #[c] !d ?"),
            ("tests/d.onsa", "sweep `^` at 1:17", "a'b' #[c] !d ?e ^"),
        ])
        # the same cut from another seed is not run twice
        self.assertEqual(fuzz.sweep([("tests/b.onsa", "x@\n"), ("tests/e.onsa", "x@\n\n// y\n")]),
                         [("tests/b.onsa", "sweep `@` at 1:2", "x@")])
        self.assertEqual(fuzz.sweep([("tests/c.onsa", "// only ~ a comment\n"), ("tests/e.onsa", "")]), [])

    def test_sweep_finds_crashes_but_skips_the_fix_stage(self):
        # FZ-1: every cut after a `@` crashes the fake compiler; the seed itself (with its newline) does
        # not, and the fix stage, which the seed would break, does not see the cuts
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE x@ y@\n")
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/layout.rs|range end index # out of range "
                      "for slice of length # (seed tests/spec/x.onsa, sweep `@` at 1:15)", text)
        self.assertIn("0 truncations (0 each, 0 crashing), 2 cuts swept after `~!?'^@#/\\%` (2 crashing), 2 crashing in all",
                      text)
        self.assertIn("0 mutants through the fix stage", text)
        self.assertNotIn("fix-same-place", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "@", new)
        # listed: known
        self.repo.write("tests/fuzz/at.onsa", "@")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/at.onsa"))
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 0, text)
        # without the sweep the cuts do not run, and the line does not name them
        code, text = self.go(truncated=0)
        self.assertEqual(code, 0, text)
        self.assertNotIn("swept", text)
        # a sweep with no place to cut is no pass
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE // x@\n")
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL the sweep found no place after a rare symbol (~!?'^@#/\\%) in 2 seeds", text)

    def test_main_passes_the_options_to_run(self):
        # FZ-1: --truncations reaches the run; --deep sweeps and has no weighted truncation unless asked
        calls = []

        def run(*args, **kw):
            calls.append((args, kw))
            return 0

        base = ["--root", str(self.repo.root), "--binary", "onsa", "--cases-binary", "onsa_cases"]
        with mock.patch.object(fuzz, "run", run), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"):
            for extra, want in (([], (fuzz.PER_SEED, fuzz.TRUNCATIONS, False, False)),
                                (["--truncations", "5"], (fuzz.PER_SEED, 5, False, False)),
                                (["--deep"], (fuzz.PER_SEED, 0, True, True)),
                                (["--deep", "--per-seed", "0", "--truncations", "3"], (0, 3, True, True))):
                with self.subTest(extra=extra):
                    calls.clear()
                    self.assertEqual(fuzz.main(base + extra), 0)
                    (args, kw), = calls
                    self.assertEqual((args[3], kw["truncated"], kw["deep"], kw["swept"]), want)
                    self.assertEqual(args[1:3], (["onsa"], ["onsa_cases"]))

    def test_truncations_find_crashes_but_skip_the_fix_stage(self):
        # FZ-1: a file that ends right after `@` crashes the fake compiler; the seed itself (with its
        # newline) and the fix stage do not see it. No mutant here: the truncations alone find it.
        # (the comment holds no cut: every cut ends with `@`)
        self.repo.write("tests/spec/x.onsa", "// BADCANDIDATE\n@@@@@@@@@@\n")
        code, text = self.go(per_seed=0, truncated=3)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/layout.rs|range end index # out of range "
                      "for slice of length # (seed tests/spec/x.onsa, truncation 0)", text)
        self.assertIn("6 truncations (3 each, 3 crashing)", text)
        # the truncations do not go through the fix stage: no broken candidate is seen
        self.assertIn("0 mutants through the fix stage", text)
        self.assertNotIn("fix-same-place", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "@", new)
        # listed: known, as the crash classes of the mutants
        self.repo.write("tests/fuzz/at.onsa", "@")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/at.onsa"))
        code, text = self.go(per_seed=0, truncated=3)
        self.assertEqual(code, 0, text)
        # without truncations nothing crashes
        self.repo.write("tests/pending.toml", "")
        self.repo.write("tests/fuzz/at.onsa", "ok")
        code, text = self.go(per_seed=0, truncated=0)
        self.assertEqual(code, 0, text)

    def test_minimize_keeps_the_class(self):
        runner = fuzz.Runner(fuzz.pool(self.argv, self.fix_argv, self.repo.root / "work"))
        self.addCleanup(runner.pool.close)
        text = "fn a() {}\nfn b() { X }\nfn c() {}\n"
        sig = runner.crashes(text)[0].signature
        small = fuzz.minimize(runner, text, sig)
        self.assertEqual(small, "X")

    def test_replay_follows_the_list(self):
        self.repo.write("tests/fuzz/listed.onsa", "X")
        self.repo.write("tests/fuzz/fixed.onsa", "ok")
        self.repo.write("tests/fuzz/regression.onsa", "ok")
        self.repo.write("tests/fuzz/unlisted.onsa", "a Z")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/listed.onsa")
                        + entry("fuzz-input", "tests/fuzz/fixed.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        fails = [l for l in text.split("\n") if l.startswith("FAIL")]
        self.assertEqual(len(fails), 2, text)
        self.assertIn("tests/fuzz/fixed.onsa: no longer crashes", fails[0])
        self.assertIn("tests/fuzz/unlisted.onsa: crashes but is not listed", fails[1])

    def test_new_and_known_classes(self):
        # the seed's mutants crash (it holds an X); the class is new until a listed input shows it
        self.repo.write("tests/spec/x.onsa", "XXXXXXXXXXXXXXXXXXXX\n")
        code, text = self.go(per_seed=3)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/body.rs|index out of bounds", text)
        self.assertIn('kind = "fuzz-input"', text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "X", new)
        self.assertFalse((self.repo.root / "tests" / "fuzz").exists())  # the gate writes nothing under tests/
        # listed: known
        self.repo.write("tests/fuzz/x.onsa", "X")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/x.onsa"))
        code, text = self.go(per_seed=3)
        self.assertEqual(code, 0, text)
        # --save writes the input under tests/fuzz
        self.repo.write("tests/spec/y.onsa", "YYYYYYYYYYYYYYYYYYYY\n")
        code, text = self.go(per_seed=3, save=True)
        self.assertEqual(code, 0, text)
        self.assertTrue((self.repo.root / "tests" / "fuzz" / f"{fuzz.short_name('Y')}.onsa").exists(), text)

    def test_replay_of_the_fix_stage(self):
        # W3-17: a listed input that still breaks a candidate's contract is still failing; one not
        # listed fails; a listed input that does neither asks for its entry to go
        self.repo.write("tests/fuzz/listed.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/fixed.onsa", "ok")
        self.repo.write("tests/fuzz/unlisted.onsa", "BADCANDIDATE")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/listed.onsa")
                        + entry("fuzz-input", "tests/fuzz/fixed.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        fails = [l for l in text.split("\n") if l.startswith("FAIL")]
        self.assertEqual(len(fails), 2, text)
        self.assertIn("tests/fuzz/fixed.onsa: no longer crashes nor breaks the contract", fails[0])
        self.assertIn("tests/fuzz/unlisted.onsa: breaks the contract of a fix candidate but is not listed", fails[1])
        self.assertIn("fix|E0010|parenthesize the `…` of #|E0010", fails[1])

    def test_fix_stage_classes(self):
        # one mutant in FIX_EVERY goes through the fix stage; a new class is minimized and written
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 1, text)
        self.assertIn("a new class of a broken fix candidate: fix-same-place: fix|E0010|parenthesize the `…` of #|E0010",
                      text)
        # 2 seeds of FIX_EVERY mutants: the first of each FIX_EVERY
        self.assertIn("2 mutants through the fix stage (0 not UTF-8)", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "BADCANDIDATE", new)
        # a listed input shows the class: known
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/f.onsa"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 0, text)

    BAD = "fix|E0010|parenthesize the `…` of #|E0010"

    def test_allowed_classes(self):
        # R-207: a class of the fix stage that the spec puts outside the contract is known through
        # tests/fuzz/allowed.toml, as long as its input shows it
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 0, text)
        self.assertIn("(0 listed, 1 allowed)", text)
        # the input no longer shows the class: the entry goes
        self.repo.write("tests/fuzz/f.onsa", "ok")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn(f"tests/fuzz/f.onsa: the class `{self.BAD}` with `m` no longer shows; remove its entry", text)
        # the class with another message left is not the entry's: a new class, and the input
        # does not show the entry's
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa", left="another"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 1, text)
        self.assertIn(f"a new class of a broken fix candidate: fix-same-place: {self.BAD}", text)
        self.assertIn(f"tests/fuzz/f.onsa: shows `{self.BAD}` with `m`, which is not the entry's", text)
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa"))
        # the input shows another class too
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE X")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("tests/fuzz/f.onsa: shows `internal|", text)

    def test_allowed_entries_are_checked(self):
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        good = allowed(self.BAD, "tests/fuzz/f.onsa")
        for toml, want in (
            (good.replace('note = "n"', 'note = "n"\nuntil = "W3-06"'), "unknown field `until`"),
            (good.replace('note = "n"\n', ""), "missing field `note`"),
            (allowed("internal|crates/a.rs|boom", "tests/fuzz/f.onsa"), "a crash is never allowed"),
            (allowed(self.BAD, "tests/fuzz/none.onsa"), "the input `tests/fuzz/none.onsa` does not exist"),
            (allowed(self.BAD, "tests/spec/ops/groups.onsa"), "must be a saved input"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("W3-07",)), "one or more S / R numbers"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-45", "s-45")), "one or more S / R numbers"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-99999",)),
             "the reason `S-99999` is not in decisions/S/, issues/R/"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-45", "R-1")),
             "the reason `R-1` is not in decisions/S/, issues/R/"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("R-23", "R-23")), "a reason is listed twice"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", note=""), "`note` must be a non-empty string"),
            (good + good, f"the class `{self.BAD}` with `m` is listed twice"),
            (good + allowed(self.BAD, "tests/fuzz/f.onsa", left="other"), "is the input of another entry"),
            (good.replace('left = "m"\n', ""), "missing field `left`"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", left="line 3"), "`left` must be the message"),
            ("[x]\n" + good, "unknown top-level key `x`"),
        ):
            with self.subTest(want=want):
                self.repo.write("tests/fuzz/allowed.toml", toml)
                code, text = self.go()
                self.assertEqual(code, 1, text)
                self.assertIn(want, text)
        # an R number of the review is a reason too (a low harm recorded there)
        for reasons in (("R-23",), ("S-45", "R-113")):
            with self.subTest(reasons=reasons):
                self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa", reasons=reasons))
                code, text = self.go()
                self.assertEqual(code, 0, text)
                self.assertIn("(0 listed, 1 allowed)", text)
        # an input listed in tests/pending.toml too
        self.repo.write("tests/fuzz/allowed.toml", good)
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/f.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("is listed in tests/pending.toml too", text)

    def test_fix_stage_failure_fails(self):
        # the tool failing is never a pass
        self.repo.write("tests/fuzz/a.onsa", "CRASH_FIX")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("the fix stage cannot run on the saved inputs: exit 3: boom", text)

    def test_fix_signature(self):
        v = {"code": "E0320", "title": "rename `Foo1` to `foo1`", "left": "E0002"}
        self.assertEqual(fuzz.fix_signature(v), "fix|E0320|rename `…` to `…`|E0002")
        self.assertEqual(fuzz.fix_signature({**v, "title": "use 3 args"}), "fix|E0320|use # args|E0002")

    def test_inputs_are_bytes(self):
        # a `\r` and invalid UTF-8 reach the compiler as they are
        raw = b"fn f() {\r\n  1\xff\r\n}\r\n"
        self.repo.write("tests/spec/ops/groups.onsa", "")
        (self.repo.root / "tests/spec/ops/groups.onsa").write_bytes(raw)
        files = fuzz.seeds(self.repo.root)
        self.assertEqual(fuzz.encode(files[0][1]), raw)
        echo = self.repo.write("echo.py", "import sys\nsys.stdout.buffer.write(open(sys.argv[-1], 'rb').read())\n")
        runner = fuzz.Runner(fuzz.pool([sys.executable, "-B", str(echo)], self.fix_argv, self.repo.root / "work"))
        self.addCleanup(runner.pool.close)
        with mock.patch.dict("os.environ", {"FAKE_SERVE_ONSA": str(echo)}):
            self.assertEqual(runner.crashes(files[0][1]), [])

    def test_deep_mutants_only_on_request(self):
        # only the mutants are made here; none of them runs (an overflow aborts)
        files = [("tests/a.onsa", "pub fn f() -> I32 {\n  1\n}\n")]
        depth = lambda m: max(m[2].count("("), m[2].count("{"), m[2].count("["))  # noqa: E731
        self.assertTrue([m for m in fuzz.mutants(files, 200, "1", deep=True) if depth(m) >= 2000])
        self.assertFalse([m for m in fuzz.mutants(files, 200, "1") if depth(m) >= 2000])

    def test_time_budget(self):
        self.repo.write("tests/spec/x.onsa", "a\n")
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 50, "t", 1, False, out=lines.append,
                        time_budget=0.001)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("time budget" in l for l in lines), lines)
        # the truncations count against the budget too (FZ-1)
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 0, "t", 1, False, out=lines.append,
                        time_budget=0.001, truncated=50)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("of 100 inputs (0 mutants, 100 truncations, 0 swept) did not run" in l for l in lines),
                        lines)
        # and the sweep (FZ-1)
        self.repo.write("tests/spec/x.onsa", "a@ b@ c@\n")
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 0, "t", 1, False, out=lines.append,
                        time_budget=0.001, truncated=0, swept=True)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("of 3 inputs (0 mutants, 0 truncations, 3 swept) did not run" in l for l in lines), lines)

    def test_seeds_skip_the_saved_inputs(self):
        self.repo.write("tests/fuzz/a.onsa", "X")
        paths = [p for p, _ in fuzz.seeds(self.repo.root)]
        self.assertEqual(paths, ["tests/spec/ops/groups.onsa"])

    # X-1: the narrowed runs and the base binaries.

    def test_a_narrowed_plan_is_a_part_of_the_whole(self):
        # the seeds, the corpus and the weights are the whole run's; the fix stage takes a mutant by its
        # index in the whole run (the subset experiment of the advisor: narrowing the list first breaks it)
        files = [(f"tests/spec/d{i % 4}/s{i}.onsa", f"pub fn f{i}(x: I32) -> I32 {{\n  x@{i} ~ 'a' + {i}\n}}\n")
                 for i in range(24)]
        only = {p for p, _ in files[3::5]}
        whole = fuzz.plan(files, 6, "1", truncated=3, swept=True)
        part = fuzz.plan(files, 6, "1", truncated=3, swept=True, only=only)
        self.assertEqual(whole[3], [i for i in range(len(whole[0])) if i % fuzz.FIX_EVERY == 0])
        mutants, cuts, swept, chosen = part
        self.assertEqual(mutants, [m for m in whole[0] if m[0] in only])
        self.assertEqual(cuts, [c for c in whole[1] if c[0] in only])
        self.assertTrue({c[2] for c in swept} <= {c[2] for c in whole[2]}, swept)
        self.assertEqual({c[0] for c in swept}, only)
        self.assertEqual([mutants[i] for i in chosen], [whole[0][i] for i in whole[3] if whole[0][i][0] in only])
        self.assertTrue(chosen and len(chosen) < len(whole[3]))

    def go_narrowed(self, selection=None, base=None, per_seed=fuzz.FIX_EVERY):
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, per_seed, "t", 2, False, out=lines.append,
                        selection=selection, base=base)
        return code, "\n".join(lines)

    def base_of(self, script=FAKE_CASES):
        return narrowing.Base("abc1234", (), (sys.executable, "-B", str(self.repo.write("base_cases.py", script))))

    SAMPLED = narrowing.Selection(sample=1.0, salt="W9-99")
    SIG = "fix|E0010|parenthesize the `…` of #|E0010"

    def test_a_class_the_base_shows_does_not_fail_a_narrowed_run(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go_narrowed(self.SAMPLED, self.base_of())
        self.assertEqual(code, 0, text)
        self.assertIn(f"\npre-existing (the base abc1234 shows it): fix-same-place: {self.SIG} (seed ", text)
        self.assertIn("from 2 of 2 seeds (sample 2) (4 each)", text)
        self.assertIn("; base abc1234: 1 pre-existing;", text)
        self.assertNotIn("FAIL", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "BADCANDIDATE", new)  # written for the parent to register

    def test_a_class_the_base_does_not_show_fails(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        for name, script in (("no violation", FAKE_CASES.replace('"BADCANDIDATE" in text', "False")),
                             ("another message left", FAKE_CASES.replace('"message": "m"', '"message": "other"')),
                             ("another code left", FAKE_CASES.replace('"left": "E0010"', '"left": "E0011"'))):
            with self.subTest(name):
                code, text = self.go_narrowed(self.SAMPLED, self.base_of(script))
                self.assertEqual(code, 1, text)
                self.assertIn(f"FAIL a new class of a broken fix candidate: fix-same-place: {self.SIG}", text)
                self.assertIn("; base abc1234: 0 pre-existing;", text)
        # the base's tool fails: it cannot tell, and the class fails
        code, text = self.go_narrowed(self.SAMPLED, self.base_of("import sys\nsys.exit(3)\n"))
        self.assertEqual(code, 1, text)
        self.assertIn("(the base cannot tell: exit 3: no list of results)", text)

    def test_a_crash_from_before_fails(self):
        # an internal error fails even when the base would show it: the base does not run it
        self.repo.write("tests/spec/x.onsa", "XXXXXXXXXXXXXXXXXXXX\n")
        code, text = self.go_narrowed(self.SAMPLED, self.base_of(), per_seed=3)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL a new crash class: check: internal|crates/onsa_sema/src/body.rs", text)
        self.assertNotIn("pre-existing", text.replace("0 pre-existing", ""))

    def test_an_unknown_base_and_whole_runs_fail(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go_narrowed(self.SAMPLED, "no target/base/abc1234/COMMIT")
        self.assertEqual(code, 1, text)
        self.assertIn("; base unknown (no target/base/abc1234/COMMIT);", text)
        self.assertIn(f"FAIL a new class of a broken fix candidate: fix-same-place: {self.SIG}", text)
        code, text = self.go_narrowed(self.SAMPLED, None)
        self.assertEqual(code, 1, text)
        self.assertNotIn("; base", text)
        # a whole run and a shard fail on a class from before, and mark it
        for selection in (None, narrowing.Selection(shard=(0, 1))):
            with self.subTest(selection=selection):
                code, text = self.go_narrowed(selection, self.base_of())
                self.assertEqual(code, 1, text)
                self.assertRegex(text, rf"FAIL a new class of a broken fix candidate: fix-same-place: {re.escape(self.SIG)} "
                                       r"\(seed [^)]*\) \(pre-existing: the base abc1234 shows it\)")
        self.assertIn("from 2 of 2 seeds (shard 0/1)", text)
        # the base of the code before HEAD (a run of the main tree, X-1 U6) says so
        code, text = self.go_narrowed(None, dataclasses.replace(self.base_of(), before_head=True))
        self.assertEqual(code, 1, text)
        self.assertIn("(pre-existing: the base abc1234 (the code before HEAD) shows it)", text)
        self.assertIn("; base abc1234 (the code before HEAD): 0 pre-existing;", text)

    def test_a_narrowed_run_mutates_the_picked_seeds_only(self):
        # the seed that is not picked (the sample takes one seed of the group tests/spec/q) gives no mutant;
        # the replay is whole
        for i in range(6):
            self.repo.write(f"tests/spec/q/s{i}.onsa", "XXXXXXXXXXXXXXXXXXXX\n" if i else "ok\n")
        self.repo.write("tests/fuzz/x.onsa", "X")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/x.onsa"))
        selection = narrowing.Selection(sample=1e-9, salt="W9-99")
        seeds = fuzz.seeds(self.repo.root)
        picked = narrowing.pick(seeds, selection, self.repo.root)
        self.assertEqual(len(picked.paths), 2)  # one of each group
        code, text = self.go_narrowed(selection, per_seed=2)
        self.assertEqual(code, 0, text)
        self.assertIn("4 mutants from 2 of 7 seeds (sample 2) (2 each)", text)
        self.assertIn("1 saved inputs replayed (1 listed", text)

    def test_main_passes_the_narrowing(self):
        calls = []

        def run(*args, **kw):
            calls.append(kw)
            return 0

        base = ["--root", str(self.repo.root), "--binary", "onsa", "--cases-binary", "onsa_cases"]
        with mock.patch.object(fuzz, "run", run), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"):
            self.assertEqual(fuzz.main(base + ["--sample", "0.1", "--salt", "W9-99", "--base", "none"]), 0)
            self.assertEqual(calls[-1]["selection"], narrowing.Selection(sample=0.1, salt="W9-99"))
            self.assertIsNone(calls[-1]["base"])
            self.assertEqual(fuzz.main(base + ["--shard", "1/2"]), 0)
            self.assertEqual(calls[-1]["selection"], narrowing.Selection(shard=(1, 2)))
            self.assertIn("merge base", calls[-1]["base"])  # not a git work tree: unknown
            self.assertEqual(fuzz.main(base), 0)
            self.assertIsNone(calls[-1]["selection"])
            for bad in (["--sample", "0.1"], ["--salt", "x"], ["--sample", "0", "--salt", "x"],
                        ["--shard", "2/2"], ["--shard", "0/2", "--sample", "0.1", "--salt", "x"],
                        ["--code-cap", "5"], ["--changed-since", "auto"]):
                with self.subTest(bad=bad), self.assertRaises(SystemExit) as e:
                    quiet(fuzz.main, base + bad)
                self.assertEqual(e.exception.code, 2)
        asked = []  # which runs ask about the work (X-1 U6b): the sample's, not the shard's nor the whole's
        with mock.patch.object(fuzz, "run", run), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"), \
                mock.patch.object(narrowing, "resolve_base", lambda root, spec, narrowed=None: narrowed):
            for extra in (["--sample", "0.1", "--salt", "W9-99"], ["--shard", "1/2"], []):
                self.assertEqual(fuzz.main(base + extra), 0)
                asked.append(calls[-1]["base"])
        self.assertEqual(asked, [True, False, False])

    # X9-23: `fuzz.py sort`, with the fake compiler and fix stage (a signal is a SIGKILL, rules/common.md 3.1).
    def sort(self, go=False):
        lines = []
        served = fuzz.pool(self.argv, self.fix_argv, self.repo.root / "target" / "fuzz" / "work-sort")
        runner, fixer = fuzz.Runner(served), fuzz.FixRunner(served, 2)
        self.addCleanup(served.close)
        code = fuzz.sort_inputs(self.repo.root, runner, fixer, 2, self.new_dir, go, out=lines.append)
        return code, "\n".join(lines)

    @property
    def new_dir(self):
        return self.repo.root / "target" / "fuzz" / "new"

    def test_sort_sorts_the_new_inputs(self):
        self.repo.write("tests/fuzz/x.onsa", "X")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/x.onsa"))
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa"))
        self.repo.write("tests/fuzz/same.onsa", "kept as it is")
        inputs = {"same.onsa": "X", "ok.onsa": "ok", "kx.onsa": "aX", "kf.onsa": "BADCANDIDATE", "z.onsa": "Z",
                  "at.onsa": "@", "mix.onsa": "BADCANDIDATE @"}
        for name, text in inputs.items():
            self.repo.write(f"target/fuzz/new/{name}", text)
        code, text = self.sort()
        self.assertEqual(code, 0, text)
        rows = re.findall(r"^(same name|fixed|known|crash|new) +(\S+)  (?:keep|remove|place)", text, re.M)
        self.assertEqual(rows, [("same name", "same.onsa"), ("fixed", "ok.onsa"), ("known", "kf.onsa"),
                                ("known", "kx.onsa"), ("crash", "at.onsa"), ("crash", "mix.onsa"),
                                ("crash", "z.onsa")], text)
        self.assertIn("sort: 7 inputs in", text)
        self.assertIn(": 1 same name, 1 fixed, 2 known, 3 crash, 0 new; nothing moved (--go places and removes them)",
                      text)
        self.assertIn('target = "tests/fuzz/at.onsa"', text)
        self.assertIn('target = "tests/fuzz/mix.onsa"', text)  # the crash's entry, not the known class's
        self.assertIn("z.onsa  (check)", text)
        self.assertIn("a signal is never saved under tests/", text)
        self.assertNotIn("[[allowed]]", text)  # a crash is never allowed
        self.assertEqual(sorted(p.name for p in self.new_dir.iterdir()), sorted(inputs))  # nothing moved
        self.assertFalse((self.repo.root / "tests/fuzz/ok.onsa").exists())
        code, text = self.sort(go=True)
        self.assertEqual(code, 0, text)
        self.assertIn("; placed and removed", text)
        self.assertEqual(sorted(p.name for p in self.new_dir.iterdir()), ["at.onsa", "mix.onsa", "z.onsa"])
        self.assertEqual((self.repo.root / "tests/fuzz/ok.onsa").read_text(), "ok")
        self.assertEqual((self.repo.root / "tests/fuzz/same.onsa").read_text(), "kept as it is")
        self.assertEqual(self.go()[0], 0)  # the placed input is a regression input the run agrees with
        # nothing to sort: no run of the compiler
        shutil.rmtree(self.new_dir)
        self.assertEqual(self.sort(), (0, f"sort: 0 inputs in {self.new_dir}: 0 same name, 0 fixed, 0 known, 0 crash, "
                                          "0 new; nothing moved (--go places and removes them)"))

    def test_sort_gives_the_allowed_entry_of_a_new_class(self):
        # X9-24: a new class of the fix stage stays with both entries; the allowed one, its reasons written,
        # is what the run reads (`load_allowed`)
        self.repo.write("target/fuzz/new/nf.onsa", "BADCANDIDATE")
        code, text = self.sort(go=True)
        self.assertEqual(code, 0, text)
        self.assertIn(": 0 same name, 0 fixed, 0 known, 0 crash, 1 new; placed and removed", text)
        self.assertIn('kind = "fuzz-input"', text)
        stub = text[text.index("[[allowed]]"):text.index("sort: ")]
        self.assertTrue(self.new_dir.joinpath("nf.onsa").exists())
        self.repo.write("tests/fuzz/nf.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", stub)
        got, errors = fuzz.load_allowed(self.repo.root, set())
        self.assertEqual((got, errors), ({}, ["tests/fuzz/allowed.toml: allowed[0]: `reasons` must be an array of one "
                                              "or more S / R numbers (`S-386`, `R-219`)"]))
        self.repo.write("tests/fuzz/allowed.toml", stub.replace('"S-?"', '"S-45"'))
        self.assertEqual(fuzz.load_allowed(self.repo.root, set()),
                         ({(self.BAD, "m"): "tests/fuzz/nf.onsa"}, []))
        code, text = self.go()
        self.assertEqual(code, 0, text)
        self.assertIn("(0 listed, 1 allowed)", text)
        # the text of a class and a message as they are, quotes and backslashes too
        c = fuzz.Crash('fix|E0001|a "q" \\ `…`|E0002', fuzz.FIX_COMMAND, "", 'left "x" \\ #')
        item = tomllib.loads(fuzz.allowed_stub("tests/fuzz/a.onsa", c))["allowed"][0]
        self.assertEqual((item["class"], item["left"], item["input"]), (c.signature, c.left, "tests/fuzz/a.onsa"))

    def test_sort_moves_nothing_when_it_cannot_tell(self):
        self.repo.write("target/fuzz/new/ok.onsa", "ok")
        self.repo.write("target/fuzz/new/bad.onsa", "CRASH_FIX")
        code, text = self.sort(go=True)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL the fix stage cannot run on the new inputs: exit 3: boom", text)
        self.assertIn("; nothing moved", text)
        self.assertNotIn("--go places", text)
        self.assertEqual(sorted(p.name for p in self.new_dir.iterdir()), ["bad.onsa", "ok.onsa"])
        self.repo.write("target/fuzz/new/bad.onsa", "ok too")
        self.repo.write("tests/fuzz/allowed.toml", "[x]\n")  # the lists cannot be read: the known classes neither
        code, text = self.sort(go=True)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL tests/fuzz/allowed.toml: unknown top-level key `x`", text)
        self.assertEqual(len(list(self.new_dir.iterdir())), 2)

    def test_the_run_gives_the_allowed_entry(self):
        # X9-24: the failure of a new class of the fix stage gives the allowed entry too; a crash's does not
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 1, text)
        self.assertIn(f'[[allowed]]\nclass = "{self.BAD}"\nleft = "m"\ninput = "tests/fuzz/', text)
        self.repo.write("tests/spec/x.onsa", "XXXXXXXXXXXXXXXXXXXX\n")
        code, text = self.go(per_seed=3)
        self.assertEqual(code, 1, text)
        self.assertIn('kind = "fuzz-input"', text)
        self.assertNotIn("[[allowed]]", text)

    def test_commands(self):
        # X9-23, rules/tools.md 9.1: no command is `run` (the gate's call); `sort` finds the new inputs
        calls = []
        base = ["--root", str(self.repo.root), "--binary", "onsa", "--cases-binary", "onsa_cases"]
        with mock.patch.object(fuzz, "run", lambda *a, **kw: calls.append((a, kw)) or 0), \
                mock.patch.object(fuzz, "sort_inputs", lambda *a, **kw: calls.append(a) or 0), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"):
            for extra in ([], ["--deep", "--shard", "0/2", "--base", "none"]):
                with self.subTest(extra=extra):
                    calls.clear()
                    self.assertEqual((fuzz.main(base + extra), fuzz.main(["run", *base, *extra])), (0, 0))
                    self.assertEqual(calls[0], calls[1])
            calls.clear()
            self.assertEqual(fuzz.main(["sort", *base, "--go", "--jobs", "3"]), 0)
            (root, runner, fixer, jobs, new_dir, go), = calls
            # one pool: onsa_cases --serve, and each command the way before (W4-18 U10c)
            served = runner.pool
            self.assertEqual((root, fixer.pool is served, fixer.jobs, jobs, new_dir, go),
                             (self.repo.root, True, 3, 3, self.new_dir, True))
            self.assertEqual((served.serve, served.fallback(("check",)), served.fallback(("--fix-same-place",))),
                             ([os.path.abspath("onsa_cases"), "--serve"], [os.path.abspath("onsa"), "check"],
                              [os.path.abspath("onsa_cases"), "--fix-same-place"]))
            with self.assertRaises(SystemExit) as e:
                quiet(fuzz.main, ["sort", *base, "--per-seed", "1"])
            self.assertEqual(e.exception.code, 2)

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in fuzz.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^fuzz\.py {name}( |$)")
                code, lines = quiet_out(fuzz.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(fuzz.main, ["help", "--role", role])
                want = [n for n, c in fuzz.COMMANDS.items() if role in c.roles]
                self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        names = list(fuzz.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(fuzz.main, ["help"])[1][: len(names)]], names)
        self.assertEqual(names, ["run", "sort"])
        sort_help = "\n".join(quiet_out(fuzz.main, ["help", "sort"])[1])
        for part in ("--save", "work.py patch", "もう一度回すとまた写る"):  # saving by hand (X9-23)
            self.assertIn(part, sort_help.replace("\n", ""))
        for flag in ("-h", "--help"):  # the list of the commands, not `run --help` (rules/common.md 1.14)
            buf = io.StringIO()
            with self.subTest(flag=flag), mock.patch.object(sys, "stdout", buf), self.assertRaises(SystemExit) as e:
                fuzz.main([flag])
            self.assertEqual(e.exception.code, 0)
            self.assertIn("{run,sort,help}", buf.getvalue())
            self.assertNotIn("--per-seed", buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
