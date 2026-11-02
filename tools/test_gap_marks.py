#!/usr/bin/env python3
"""Self-tests of tools/gap_marks.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_gap_marks.py
"""
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs as docs_tool  # noqa: E402
import gap_marks  # noqa: E402
import gate_steps  # noqa: E402
import pending  # noqa: E402
from selftest_support import quiet, quiet_out, TempRepo  # noqa: E402


class SpecGap(TempRepo):
    def marks(self, files):
        for rel, text in files.items():
            self.repo.write(rel, text)
        marks = gap_marks.find_marks(self.repo.root)
        known = pending.load_docs(self.repo.root).reasons | gap_marks.api_ids(self.repo.root)
        problems, for_parent = gap_marks.check(marks, known, "decisions/S/, issues/R/, decisions/A/")
        return marks, problems + for_parent

    def test_registered_marks_pass(self):
        marks, problems = self.marks(
            {
                "crates/a/src/lib.rs": "fn f() {} // SPEC-GAP(S-45): the order is not given\n    // SPEC-GAP(R-23): x\n",
                "std/x.onsa": "// SPEC-GAP(A-01): y\n",
                "runtime/c/onsa.h": "/* c */ // SPEC-GAP(S-34): z\n",
                "tools/t.py": "x = 1  # SPEC-GAP(R-23): w\n",
            }
        )
        self.assertEqual(len(marks), 5)
        self.assertEqual(problems, [])

    def test_bad_marks_fail(self):
        cases = {
            "// SPEC-GAP: no id": "malformed",
            "// SPEC-GAP(): empty": "malformed",
            "// SPEC-GAP(S-45) missing colon": "malformed",
            "// spec-gap(S-45): lower case": "malformed",
            "// SPECGAP(S-45): no hyphen": "malformed",
            "// SPEC GAP(S-45): a space": "malformed",
            "// Spec_Gap(S-45): mixed": "malformed",
            "// a spec gap, mentioned in prose": "malformed",
            "// SPEC-GAP(S-45): a note on a specgap": "malformed",
            "// SPEC-GAP(S-45):": "malformed",
            "//SPEC-GAP(S-45): no space": "malformed",
            "/// SPEC-GAP(S-45): a doc comment": "malformed",
            "// SPEC-GAP(S-45): one // SPEC-GAP(R-23): two": "malformed",
            "let s = \"SPEC-GAP\";": "malformed",
            "// SPEC-GAP(NEW): to register": "the parent registers",
            "// SPEC-GAP(Q-10): not S / R / A": "not an S / R / A number",
            "// SPEC-GAP(S-99): no such file": "S-99 is not in decisions/S/, issues/R/, decisions/A/",
            "// SPEC-GAP(A-02): no such file": "A-02 is not in decisions/S/, issues/R/, decisions/A/",
        }
        for line, needle in cases.items():
            with self.subTest(line=line):
                _, problems = self.marks({"crates/a/src/lib.rs": f"fn f() {{}}\n{line}\n"})
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(needle, problems[0])
                self.assertIn("crates/a/src/lib.rs:2", problems[0])

    def test_spelling_hint(self):
        # N3: a line that only mentions a spelling of the token is told how to avoid it
        _, problems = self.marks({"crates/a/src/lib.rs": "// see spec_gap below\n"})
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("if this is not a mark, avoid spellings like `spec_gap`", problems[0])

    def test_comment_leader_follows_the_file(self):
        _, problems = self.marks({"tools/t.py": "# SPEC-GAP(S-45): ok\n// SPEC-GAP(S-45): not a Python comment\n"})
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("tools/t.py:2", problems[0])

    def test_skipped(self):
        marks, _ = self.marks(
            {
                # build outputs: `target/` next to a Cargo.toml or an onsa.toml
                "crates/a/Cargo.toml": "[package]\n",
                "crates/a/target/x.rs": "// SPEC-GAP(NEW): build output\n",
                "std/pkg/onsa.toml": "[package]\n",
                "std/pkg/target/host/x.c": "// SPEC-GAP(NEW): build output\n",
                "docs/x.md": "// SPEC-GAP(NEW): not scanned\n",
                "tools/gap_marks.py": "TOKEN = 'SPEC-GAP'\n",
            }
        )
        self.assertEqual(marks, [])
        (self.repo.root / "crates/a/b.bin").write_bytes(b"\xff\xfe SPEC-GAP")  # not text
        self.assertEqual(gap_marks.find_marks(self.repo.root), [])
        # M3: a `target` elsewhere is an ordinary directory and is scanned
        marks, problems = self.marks(
            {
                "crates/a/src/target/x.rs": "// SPEC-GAP(NEW): a module named target\n",
                "tools/target/y.py": "# SPEC-GAP(S-45): ok\n",
            }
        )
        self.assertEqual([m[0] for m in marks], ["crates/a/src/target/x.rs", "tools/target/y.py"])
        self.assertEqual(len(problems), 1, problems)

    def test_main(self):
        self.repo.write("crates/a/src/lib.rs", "// SPEC-GAP(S-45): x\n")
        self.assertEqual(quiet(gap_marks.main, ["--root", str(self.repo.root)]), 0)
        self.repo.write("crates/a/src/lib.rs", "// SPEC-GAP(NEW): x\n")
        self.assertEqual(quiet(gap_marks.main, ["--root", str(self.repo.root)]), 1)
        code, out = quiet_out(gap_marks.main, ["--root", str(self.repo.root)])
        self.assertIn("lib.rs:1: SPEC-GAP(NEW)", "\n".join(out))
        self.repo.write("crates/a/src/lib.rs", "// SPEC-GAP(S-99): x\n")  # the text names where the IDs are read
        code, out = quiet_out(gap_marks.main, ["--root", str(self.repo.root)])
        self.assertIn("S-99 is not in decisions/S/, issues/R/, decisions/A/", "\n".join(out))
        self.assertEqual(code, 1)

    def test_dropped(self):
        # X9-29: a mark that names a DROPPED S is told (PARENT), never failed; DECIDED, OPEN and a mention are not
        self.repo.write_id("S-50", "OPEN")
        self.assertEqual(gap_marks.dropped_ids(docs_tool.Index.of(self.repo.root)), {"S-15"})
        text = "// SPEC-GAP(S-15): x\n// SPEC-GAP(S-45): y\n// SPEC-GAP(S-50): z\n// S-15 was dropped\n"
        self.repo.write("crates/a/src/lib.rs", text)
        code, out = quiet_out(gap_marks.main, ["--root", str(self.repo.root)])
        said = "parent: crates/a/src/lib.rs:1: S-15 is DROPPED in decisions/S/; point the mark to the decision"
        self.assertEqual(code, gate_steps.PARENT, out)
        self.assertEqual([x for x in out if x.startswith("parent:")], [out[0]])
        self.assertTrue(out[0].startswith(said), out)
        self.assertEqual(out[-1], "3 SPEC-GAP mark(s) in crates, std, runtime, tools; 1 naming a dropped S")
        # with a problem the exit is the problem's; the dropped S is still only told
        self.repo.write("crates/a/src/lib.rs", text + "// SPEC-GAP(NEW): w\n")
        code, out = quiet_out(gap_marks.main, ["--root", str(self.repo.root)])
        self.assertEqual(code, 1, out)
        self.assertTrue(any(x.startswith(said) for x in out), out)


if __name__ == "__main__":
    unittest.main(verbosity=1)
