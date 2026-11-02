#!/usr/bin/env python3
"""Self-tests of tools/diag_codes.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_diag_codes.py
"""
import io
import re
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import diag_codes  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
from selftest_support import CODES, entry, TempRepo, json_cmd  # noqa: E402


def run(path, mode="check", markers=()):
    """A case of `onsa_cases --run`; markers are (file, line, code, matched, target)."""
    return {
        "path": path,
        "mode": mode,
        "ran": mode != "none",
        "markers": [
            {"code": c, "file": f, "line": ln, "stage": "build" if t else "check", "target": t, "matched": ok}
            for f, ln, c, ok, t in markers
        ],
        "problems": [],
    }


class DiagRegistry(TempRepo):
    def test_spec_codes(self):
        text = "E0001 は（E0002）、コードはE0003。E00xx、E00123、XE0004、`E0005`"
        self.assertEqual(diag_codes.spec_codes(text), {"E0001", "E0002", "E0003", "E0005"})
        for r in (
            "E0410〜E0416", "E0410 ~ E0416", "E0410-E0416", "E0410〜0416", "E0410..E0416", "E0410...E0416",
            "E0410 … E0416", "E0410--E0416", "E0410 to E0416", "E0410 から E0416",
        ):  # fmt: skip
            with self.subTest(r=r):
                with self.assertRaisesRegex(diag_codes.CheckError, "range"):
                    diag_codes.spec_codes(f"型の誤りは {r}。")
        # a list is not a range
        for ok in ("E0410 / E0416", "E0410、E0416", "E0410 total E0416", "E0410, E0416"):
            self.assertEqual(diag_codes.spec_codes(ok), {"E0410", "E0416"}, ok)

    def test_phase2_codes(self):
        # the rows whose last cell is 第 2 期, with the ranges expanded; not the M3 row
        self.assertEqual(repo.phase2_codes(CODES), {"E0612", "E0613", "E0614", "E0620", "E0904", "E0905"})
        with self.assertRaisesRegex(repo.RepoError, "^tasks/diag-codes.md: no row"):
            repo.phase2_codes(CODES.replace("| 第 2 期 |", "| M4 |"))
        with self.assertRaisesRegex(repo.RepoError, "goes down"):
            repo.phase2_codes(CODES.replace("E0612〜E0614", "E0614〜E0612"))

    def test_retired_codes(self):
        # codes in parentheses and after the first sentence are not retired
        self.assertEqual(repo.retired_codes(CODES), {"E0611", "E0814"})
        for bad, needle in (
            (CODES.replace("欠番: ", "欠番は "), "tasks/diag-codes.md: expected one line starting with `欠番:`, found 0"),
            (CODES + "欠番: E0313。\n", "found 2"),
            (CODES.replace("欠番: E0611（S-77 で E0601 にまとめた）、E0814（S-147 で E0815 にまとめた）", "欠番: なし"), "names no code"),
        ):
            with self.subTest(needle=needle):
                with self.assertRaisesRegex(diag_codes.CheckError, re.escape(needle)):
                    repo.retired_codes(bad)

    def test_check_registry(self):
        spec, retired = {"E0001", "E0002", "E0814"}, {"E0814", "E0611"}
        self.assertEqual(diag_codes.check_registry({"E0001", "E0002"}, spec, retired), [])
        problems = diag_codes.check_registry({"E0001", "E0814", "E0999"}, spec, retired)
        self.assertEqual(len(problems), 3, problems)
        self.assertIn("E0002: the spec names it", problems[0])
        self.assertIn("E0814: a retired code", problems[1])
        self.assertIn("E0999: in the registry, but the spec does not name it", problems[2])

    def run_main(self, flag, outputs):
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main([flag], root=self.repo.root, cmd=json_cmd(outputs))
        return code, out.getvalue()

    def test_main(self):
        self.repo.write_spec("E0001 と E0002。E0611 は欠番。")
        codes = [{"code": "E0001"}, {"code": "E0002"}]
        code, out = self.run_main("--registry", {"--codes": codes})
        self.assertEqual(code, 0, out)
        self.assertIn("2 codes in the registry", out)
        code, out = self.run_main("--registry", {"--codes": codes[:1]})
        self.assertEqual(code, 1, out)
        self.assertIn("E0002: the spec names it", out)
        # a failing lister fails the check
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--registry"], root=self.repo.root, cmd=(sys.executable, "-B", "-c", "raise SystemExit(3)"))
        self.assertEqual(code, 1)
        self.assertIn("cannot check", out.getvalue())


class DiagNegatives(TempRepo):
    def test_count(self):
        runs = {
            "cases": [
                # a marker compared once per target counts once; one not matched does not count
                run("tests/a/m.onsa", markers=[("m.onsa", 3, "E0809", True, "a"), ("m.onsa", 3, "E0809", True, "b"),
                                               ("m.onsa", 4, "E0809", False, "a")]),
                # the same file name in another case is another example
                run("tests/b/m.onsa", markers=[("m.onsa", 3, "E0809", True, None)]),
                run("tests/c.onsa", markers=[("tests/c.onsa", 1, "E0302", True, None), ("tests/c.onsa", 2, "E0302", True, None)]),
                # not counted: mode none, a case pending as a whole
                run("tests/none.onsa", mode="none", markers=[("tests/none.onsa", 1, "E0302", True, None)]),
                run("tests/whole.onsa", markers=[("tests/whole.onsa", 1, "E0302", True, None)]),
                # counted: a case with one test pending
                run("tests/one.onsa", mode="test", markers=[("tests/one.onsa", 1, "E0401", True, None)]),
            ],
            "errors": [],
        }
        listed = entry("test-case", "tests/whole.onsa", until="W3-07") + entry("test-case", "tests/one.onsa::t", until="W3-07")
        self.repo.write("tests/whole.onsa", "")
        self.repo.write("tests/one.onsa", "")
        self.repo.write("tests/pending.toml", listed)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        counts = diag_codes.count_negatives(runs, entries)
        self.assertEqual(counts, {"E0809": 2, "E0302": 2, "E0401": 1})

    def test_check(self):
        registry = {"E0001", "E0002", "E0003"}
        counts = {"E0001": 3, "E0002": 2, "E0003": 0}
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002") + entry("diag-code", "E0003"))
        entries, _ = pending.load(self.repo.pending)
        self.assertEqual(diag_codes.check_negatives(counts, registry, entries, set()), [])
        # fewer than 3 and not listed
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, set())
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("E0003: 0 negative example(s), fewer than 3, and not listed", problems[0])
        # listed but reached 3; listed but not a code
        text = entry("diag-code", "E0001") + entry("diag-code", "E0002") + entry("diag-code", "E0003") + entry("diag-code", "E0998")
        self.repo.write("tests/pending.toml", text)
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives({**counts, "E0997": 1}, registry, entries, set())
        self.assertEqual(len(problems), 3, problems)
        self.assertIn("E0001: 3 negative examples, but pending[0]", problems[0])
        self.assertIn("remove the entry", problems[0])
        self.assertIn('"E0998": not a code of the registry', problems[1])
        self.assertIn("E0997: markers name it", problems[2])

    def test_phase2(self):
        # M1: PH2 only for the codes of the second phase (tasks/diag-codes.md), and those listed have PH2
        registry, counts, phase2 = {"E0001", "E0612"}, {}, {"E0612"}
        ok = entry("diag-code", "E0001", until="W3-07") + entry("diag-code", "E0612", until="PH2")
        self.repo.write("tests/pending.toml", ok)
        entries, _ = pending.load(self.repo.pending)
        self.assertEqual(diag_codes.check_negatives(counts, registry, entries, phase2), [])
        # a code of the first phase put off to PH2
        self.repo.write("tests/pending.toml", entry("diag-code", "E0001", until="PH2") + entry("diag-code", "E0612", until="PH2"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, phase2)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"E0001": until "PH2", but tasks/diag-codes.md does not put it in the second phase', problems[0])
        # a code of the second phase given a work of the first
        self.repo.write("tests/pending.toml", entry("diag-code", "E0001", until="W3-07") + entry("diag-code", "E0612", until="W3-07"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, phase2)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"E0612": a code of the second phase (tasks/diag-codes.md), so its until is "PH2", not W3-07', problems[0])

    def test_threshold_is_three(self):
        self.assertEqual(diag_codes.NEGATIVE_MIN, 3)

    def test_main(self):
        runs = {"cases": [run("tests/c.onsa", markers=[("tests/c.onsa", i, "E0001", True, None) for i in (1, 2, 3)])], "errors": []}
        outputs = {"--codes": [{"code": "E0001"}, {"code": "E0002"}], "--run": runs}  # tasks/diag-codes.md: E0612... are PH2
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002"))
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--negatives"], root=self.repo.root, cmd=json_cmd(outputs))
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn("(6 of the second phase)", out.getvalue())
        self.assertIn("1 fewer: E0002 0", out.getvalue())
        # an error of the scan fails
        outputs["--run"] = {**runs, "errors": ["tests/locked: cannot read the directory"]}
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--negatives"], root=self.repo.root, cmd=json_cmd(outputs))
        self.assertEqual(code, 1)
        self.assertIn("cannot scan the cases", out.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
