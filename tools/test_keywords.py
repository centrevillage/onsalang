#!/usr/bin/env python3
"""Self-tests of tools/keywords.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_keywords.py
"""
import sys
import types
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import keywords  # noqa: E402
import repo  # noqa: E402


class Keywords(unittest.TestCase):
    """tools/keywords.py: the lexer's keywords against §2.2 (W3-02/b 12)."""

    SPEC = "# s\n## 2. 字句\n### 2.2 キーワード\n\n```\nfn let\nat clock\n```\n\n### 2.3 次\n"

    def test_the_block_of_2_2(self):
        self.assertEqual(keywords.spec_keywords(self.SPEC), ["fn", "let", "at", "clock"])
        with self.assertRaises(repo.RepoError):
            keywords.spec_keywords("# s\n### 2.2 キーワード\n\nno block\n")

    def test_differences_and_the_list(self):
        diffs = keywords.differences(["fn", "let", "at", "clock"], ["fn", "let", "loop"])
        self.assertEqual(sorted(diffs), ["at", "clock", "loop"])
        e = types.SimpleNamespace(until="W3-04")
        pend, problems = keywords.apply_list(diffs, {"at": e, "clock": e, "fn": e})
        self.assertEqual(len(pend), 2)
        self.assertTrue(any(p.startswith("keywords/loop:") for p in problems), problems)
        self.assertTrue(any(p.startswith("keywords/fn:") and "remove the entry" in p for p in problems), problems)
        self.assertEqual(len(problems), 2)


if __name__ == "__main__":
    unittest.main(verbosity=1)
