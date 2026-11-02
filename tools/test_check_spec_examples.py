#!/usr/bin/env python3
"""Self-tests of tools/check_spec_examples.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_check_spec_examples.py
"""
import sys
import tomllib
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_spec_examples as cse  # noqa: E402
import pending  # noqa: E402
import spec_blocks  # noqa: E402
from selftest_support import SPEC, entry, quiet, TempRepo  # noqa: E402


class SpecExamples(TempRepo):
    def setUp(self):
        super().setUp()
        self.first, self.fs_a, self.fs_b = self.repo.ids()

    def list_(self, *targets):
        self.repo.write("tests/pending.toml", "".join(entry("spec-example", t) for t in targets))

    def test_ids(self):
        self.assertRegex(self.first, r"^§3\.1 [0-9a-f]{8}: let a = x \+ y - z$")
        # the `#ifndef` inside the C fence is not a heading
        self.assertTrue(self.fs_a.startswith("§3.1 "), self.fs_a)
        self.assertTrue(self.fs_b.startswith("§17.4 "), self.fs_b)
        for sid in (self.first, self.fs_a, self.fs_b):
            self.assertIsNotNone(spec_blocks.parse_id(sid))
            self.assertRegex(sid, pending.TARGET_FORMS["spec-example"])

    def test_same_first_line_is_two_names(self):
        self.assertNotEqual(self.fs_a, self.fs_b)
        self.assertEqual(self.fs_a.split(": ", 1)[1], self.fs_b.split(": ", 1)[1])
        self.list_(self.fs_a)
        problems, notes = self.repo.check_spec()
        self.assertEqual(len(notes), 1)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("spec.md:28", problems[0])  # the current line of the second block
        self.assertIn(self.fs_b, problems[0])

    def test_unlisted_mismatch_fails(self):
        self.list_(self.fs_a)
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("not found verbatim", problems[0])
        self.assertIn(f'target = "{self.fs_b}"', problems[0])

    def test_listed_mismatches_pass(self):
        self.list_(self.fs_a, self.fs_b)
        problems, notes = self.repo.check_spec()
        self.assertEqual(problems, [])
        self.assertEqual(len(notes), 2)
        self.assertIn("spec.md:19", notes[0])

    def test_listed_but_found_fails(self):
        self.list_(self.first, self.fs_a, self.fs_b)
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("remove the entry", problems[0])
        self.assertIn("ops/groups.onsa", problems[0])

    def test_changed_block_fails(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("fn second() {}", "fn second() { }"))
        problems, _ = self.repo.check_spec()
        stale = [p for p in problems if "names no ```onsa block" in p]
        self.assertEqual(len(stale), 1, problems)
        self.assertIn(self.fs_b.split(" ")[0], stale[0])
        self.assertIn("now spec.md:28", stale[0])  # the hint: same section and first line
        # the changed block is unlisted now, so it fails too
        self.assertTrue(any("not found verbatim" in p for p in problems), problems)

    def test_removed_block_fails(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.split("## 17.")[0])
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("names no ```onsa block", problems[0])

    def test_renumbered_section_fails_with_hint(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("### 17.4 声", "### 17.5 声"))
        problems, _ = self.repo.check_spec()
        stale = [p for p in problems if "names no ```onsa block" in p]
        self.assertEqual(len(stale), 1, problems)
        self.assertIn("§17.5", stale[0])  # the hint: same hash

    def test_malformed_target_is_stale(self):
        self.list_(self.fs_a, self.fs_b, "not an id")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"not an id": names no ```onsa block', problems[0])

    def test_names_do_not_depend_on_lines_or_indentation(self):
        moved = SPEC.replace("# Spec\n", "# Spec\n\nmore text\n\nand more\n").replace("fn second() {}", "    fn second() {}")
        self.repo.write("spec.md", moved)
        self.assertEqual(self.repo.ids(), [self.first, self.fs_a, self.fs_b])

    def test_markers_and_indentation_of_the_copy_are_ignored(self):
        self.list_(self.fs_a, self.fs_b)
        problems, _ = self.repo.check_spec()
        self.assertEqual(problems, [])  # COPY_FIRST carries `//~` and indentation

    def test_match_is_by_whole_lines(self):
        # `let a = 1` is not in `let a = 10`, nor a line in the middle of another
        self.repo.write("spec.md", "## 1. x\n\n```onsa\nlet a = 1\n```\n\n```onsa\nb = 2\n```\n")
        self.repo.write("tests/spec/ops/groups.onsa", "let a = 10\nlet b = 2\n")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 2, problems)
        self.repo.write("tests/spec/ops/groups.onsa", "fn f() {\n  let a = 1\n}\nb = 2\n")
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_lines_must_be_consecutive(self):
        self.repo.write("spec.md", "## 1. x\n\n```onsa\nlet a = 1\nlet b = 2\n```\n")
        self.repo.write("tests/spec/ops/groups.onsa", "let a = 1\nlet c = 3\nlet b = 2\n")
        self.assertEqual(len(self.repo.check_spec()[0]), 1)

    def test_empty_block_fails(self):
        self.repo.write("spec.md", "## 1. x\n\n```onsa\n\n```\n")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("empty", problems[0])

    def test_unclosed_fence_fails(self):
        # a `c` fence left open would swallow the onsa block after it
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("#endif\n```\n", "#endif\n"))
        problems, _ = self.repo.check_spec()
        self.assertTrue(any("is not closed" in p for p in problems), problems)
        self.repo.write("spec.md", SPEC + "\n```onsa\nlet z = 1\n")
        problems, _ = self.repo.check_spec()
        self.assertTrue(any('"' + "`" * 3 + 'onsa" is not closed' in p for p in problems), problems)

    def test_onsa_like_fences_fail(self):
        self.list_(self.fs_a, self.fs_b)
        for opener, closer in [
            ("```onsa,x", "```"),
            ("````onsa", "````"),
            ("~~~onsa", "~~~"),
            ("```Onsa", "```"),
            ("``` onsa", "```"),
        ]:
            with self.subTest(opener=opener):
                self.repo.write("spec.md", SPEC + f"\n{opener}\nlet hidden = 1\n{closer}\n")
                problems, _ = self.repo.check_spec()
                self.assertEqual(len(problems), 1, problems)
                self.assertIn("looks like onsa", problems[0])
                self.assertIn("not silenced by the list", problems[0])

    def test_other_fences_are_fine(self):
        extra = "\n```toml\n[a]\n```\n\n```\nplain\n```\n\n~~~text\n```onsa\n~~~\n\n````md\n```onsa\nx\n```\n````\n"
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC + extra)
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_suggested_target_is_toml(self):
        self.repo.write("spec.md", '## 1. x\n\n```onsa\nlet s = "a\\\\b"  // é\n```\n')
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        line = problems[0].split("\n")[1].strip()
        parsed = tomllib.loads(line)["target"]
        self.assertEqual(parsed, self.repo.ids()[0])
        self.assertIn("é", line)  # non-ASCII is kept
        # pasted back into the list, the block is pending
        self.repo.write("tests/pending.toml", entry("spec-example", parsed))
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_cli(self):
        self.list_(self.fs_a)
        args = [str(self.repo.spec), str(self.repo.tests), "--pending", str(self.repo.pending)]
        self.assertEqual(quiet(cse.main, args), 1)
        self.list_(self.fs_a, self.fs_b)
        self.assertEqual(quiet(cse.main, args), 0)


if __name__ == "__main__":
    unittest.main(verbosity=1)
