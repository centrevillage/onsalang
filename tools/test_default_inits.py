#!/usr/bin/env python3
"""Self-tests of tools/default_inits.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_default_inits.py
"""
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import default_inits  # noqa: E402
import repo  # noqa: E402
from selftest_support import quiet, split_spec  # noqa: E402


# The real `onsa_cases` from any directory: tools/default_inits.py runs it in the root it reads.
REAL_CASES = ("cargo", "run", "-q", "--manifest-path", str(repo.ROOT / "Cargo.toml"), *repo.CASES_BIN, "--")
INIT_FLOW = "pub flow f(x: F32 at sample, b: Bool at sample, s: F32 at init) -> F32 at sample {{\n  {}\n}}\n"


class DefaultInits(unittest.TestCase):
    """tools/default_inits.py: the documents write the omitted `init` (S-539 (c3a))."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def docs(self, spec, tools="", std=None, example=None):
        """A spec of one block (`spec/11-c.md`, its code from the line 7), `spec/tools.md`, one file of `std/`
        and of `examples/`."""
        split_spec(f"# s\n## 11. flow\n### 11.4 遅延\n\n本文の `prev~(^y, 0)` は読まない。\n\n```onsa\n{spec}```\n", self.root)
        self.write(repo.SPEC_TOOLS, tools)
        self.write("std/a.onsa", std if std is not None else INIT_FLOW.format("prev~(x)"))
        self.write("examples/b.onsa", example if example is not None else INIT_FLOW.format("delay~(x, 4)"))

    def check(self, cmd=REAL_CASES):
        return default_inits.check(self.root, cmd)[0]

    def test_an_init_equal_to_the_default_fails(self):
        self.docs(
            INIT_FLOW.format("let y = prev~(x, 0.0)\n  y"),
            tools="# t\n\n```onsa\n" + INIT_FLOW.format("delay~(b, 3, false)") + "```\n",
            std=INIT_FLOW.format("vdelay~(x, x, 8, 0x0_0) + prev~(x, (0e3))"),
            example="// c\n" + INIT_FLOW.format("delay~(x, 4, -0) + prev~(x, 00.00)"),
        )
        problems = self.check()
        shown = sorted(p.split("  ")[0] for p in problems)
        self.assertEqual(
            shown,
            ["examples/b.onsa:3", "examples/b.onsa:3", "spec/11-c.md:8", "spec/tools.md:5",
             "std/a.onsa:2", "std/a.onsa:2"],
            problems,
        )  # fmt: skip
        self.assertTrue(all("write the omitted form" in p for p in problems), problems)
        self.assertIn("`prev~` has the init `0.0`", "\n".join(problems))
        self.assertEqual(quiet(default_inits.main, [], self.root, REAL_CASES), 1)

    def test_the_omitted_form_and_other_values_pass(self):
        # the omitted form, values that are not 0, `-0.0` (not the default), a name, `true`; the text
        # outside the blocks names `prev~(^y, 0)` on purpose
        self.docs(
            INIT_FLOW.format("prev~(x) + prev~(x, 1.0) + prev~(x, -0.0) + delay~(x, 4, s) + vdelay~(x, x, 8, 0.5)"),
            tools="# t\n\n例の `prev~(^y, 0)`。\n\n```onsa\n" + INIT_FLOW.format("prev~(x, 2.0)") + "```\n",
            std=INIT_FLOW.format("delay~(b, 3, true)\n  x"),
        )
        problems, summary = default_inits.check(self.root, REAL_CASES)
        self.assertEqual(problems, [])
        # a block of each document is read (X-2 U7a: `spec/` and `spec/tools.md`, never 0)
        self.assertIn("1 spec/ blocks, 1 spec/tools.md blocks, 1 examples files, 1 std files; "
                      "8 delay calls", summary)  # fmt: skip
        self.assertEqual(quiet(default_inits.main, [], self.root, REAL_CASES), 0)

    def test_reading_nothing_fails(self):
        self.docs("fn f() {}\n", std="fn g() {}\n", example="fn h() {}\n")
        self.assertEqual([p for p in self.check() if "reading nothing" in p], [
            "no delay call in the documents; the check would pass reading nothing"])  # fmt: skip
        (self.root / "std" / "a.onsa").unlink()
        self.assertIn("no std files to read; the check would pass reading nothing", self.check())

    def test_a_source_the_compiler_cannot_read_fails(self):
        self.docs(INIT_FLOW.format("prev~(x)"))
        script = ("import json, sys; print(json.dumps([{'file': f, 'internal': 'boom'} for f in sys.argv[2:]]"
                  " + [{'file': 'other', 'calls': 1, 'hits': []}]))")  # fmt: skip
        problems = self.check((sys.executable, "-B", "-c", script))
        self.assertEqual(len([p for p in problems if "could not read it: boom" in p]), 3, problems)
        script = "import json; print(json.dumps([]))"
        problems = self.check((sys.executable, "-B", "-c", script))
        self.assertEqual(len([p for p in problems if "could not read it: no report" in p]), 3, problems)

    def test_a_fence_that_cannot_be_trusted_fails(self):
        self.docs(INIT_FLOW.format("prev~(x)"), tools="# t\n\n```Onsa\nprev~(x, 0.0)\n```\n")
        self.assertTrue(any(p.startswith("spec/tools.md:3") and "looks like onsa" in p for p in self.check()))

    def test_a_call_the_tree_does_not_hold_fails(self):
        # the item with a syntax error has no tree, nor has the spaced `prev ~(` (§2.6): the tokens count them
        broken = INIT_FLOW.format("let a = prev~(x, 0.0)\n  let b = )\n  a")
        self.docs(broken + INIT_FLOW.replace("flow f", "flow g").format("prev ~(x, 0.0)"))
        problems = self.check()
        self.assertEqual(problems, ["spec/11-c.md:7  2 of its 2 delay calls are not in the tree (an item with "
                                    "a syntax error); their init is not checked"])  # fmt: skip
        # a file of std/ with a syntax error fails by itself too, also when the tree holds all its calls
        self.docs(INIT_FLOW.format("prev~(x)"), std=broken)
        problems = self.check()
        self.assertEqual(sorted(p.split("  ")[1].split(";")[0] for p in problems),
                         ["1 of its 1 delay calls are not in the tree (an item with a syntax error)",
                          "has a diagnostic of the syntax stage (`onsa check` shows it)"], problems)  # fmt: skip
        self.docs(INIT_FLOW.format("prev~(x)"), example="fn g() -> I32 { 1 + }\n" + INIT_FLOW.format("delay~(x, 4)"))
        self.assertEqual([p.split("  ")[0] for p in self.check()], ["examples/b.onsa:1"])

    def test_the_counts_agree_without_a_call_in_the_spec(self):
        # no delay call in the blocks of the spec, some in std/: nothing unread, so it passes
        self.docs("fn f() {}\n")
        problems, summary = default_inits.check(self.root, REAL_CASES)
        self.assertEqual(problems, [])
        self.assertTrue(summary.endswith("; 2 delay calls"), summary)


if __name__ == "__main__":
    unittest.main(verbosity=1)
