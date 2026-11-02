#!/usr/bin/env python3
"""Self-tests of tools/crosscheck.py (tools/selftest.py runs every self-test): each check on a made-up root.

Alone: python3 -B tools/test_crosscheck.py
"""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import crosscheck  # noqa: E402
import docs as docs_tool  # noqa: E402
import gate_steps  # noqa: E402
import refactor  # noqa: E402
import work  # noqa: E402
from selftest_support import NEW_LAYOUT, json_cmd, quiet_out  # noqa: E402


def c_step(name, **kw):
    return gate_steps.Step(name, (*gate_steps.C_CHECK, name), **{"pendable": True, **kw})


class CrossCheck(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)

    def write(self, rel, text):
        (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
        (self.root / rel).write_text(text, encoding="utf-8")

    def test_c_items(self):
        steps = [gate_steps.Step("other", ("x",)), c_step("c-a"), c_step("c-b")]
        cmd = json_cmd({"--c-items": ["c-a", "c-b"]})
        self.assertEqual(crosscheck.c_items(self.root, cmd, steps), [])
        for rows, have, says in (
            (["c-b", "c-a"], steps, "are not the rows of onsa_tests::c::ITEMS in their order (c-b, c-a)"),
            (["c-a"], steps, "(c-a, c-b) are not the rows"),
            (["c-a", "c-b"], [c_step("c-a"), gate_steps.Step("c-b", (*gate_steps.C_CHECK, "c-x"), pendable=True)],
             "are not the rows"),
            (["c-a", "c-b"], [c_step("c-a"), c_step("c-b", pendable=False)], "the C item c-b is not pendable"),
            ([], [], "onsa_cases --c-items gives no item"),
        ):
            with self.subTest(says=says):
                problems = crosscheck.c_items(self.root, json_cmd({"--c-items": rows}), have)
                self.assertTrue(any(says in p for p in problems), problems)

    def test_budgets(self):
        rows = f"| 名前 | 値 |\n|---|---|\n| {refactor.BUDGET} | 関数は 100 行、ファイルは 1000 行 |\n"
        self.write("rules/budgets.md", rows + f"| {work.REFACTOR} | 見積もりの 3 倍を超え、かつ差が 100 行以上 |\n")
        self.assertEqual(crosscheck.budgets(self.root), [])
        self.write("rules/budgets.md", rows)
        self.assertTrue(any(work.REFACTOR in p for p in crosscheck.budgets(self.root)))

    def test_doc_fields(self):
        for rel, text in NEW_LAYOUT.items():
            self.write(rel, text)
        tree = docs_tool.Tree(self.root, [])
        tables = [tree.index.table(n) for n in tree.index.files]
        fields = {k for t in tables for k, f in t.fields.items() if f.base == "ID"}
        problems = crosscheck.doc_fields(self.root)
        self.assertEqual([p for p in problems if "RESTS_ON" in p], [])
        with mock.patch.object(docs_tool, "RESTS_ON", {**docs_tool.RESTS_ON, "nope": True}):
            self.assertIn("docs.RESTS_ON has `nope`, an ID field of no README", crosscheck.doc_fields(self.root))
        self.assertIn("the labels of the body of a work need one 持ち越し (`docs.py ticket`): none", problems)
        readme = self.root / "tasks/W/README.md"
        readme.write_text(readme.read_text("utf-8") + f"\n{docs_tool.LABELS_HEAD}\n\n- `持ち越し`: 後へ\n", "utf-8")
        with mock.patch.object(docs_tool, "RESTS_ON", {k: True for k in fields}):
            self.assertEqual(crosscheck.doc_fields(self.root), [])
        with mock.patch.object(docs_tool, "RESTS_ON", {k: True for k in sorted(fields)[1:]}):
            self.assertTrue(any("has no direction in docs.RESTS_ON" in p for p in crosscheck.doc_fields(self.root)))

    def test_test_modules(self):
        self.write("crates/a/src/lib.rs", "fn a() {}\n#[cfg(test)]\nmod t {\n    fn b() {}\n}\n")
        self.write("crates/a/src/x/tests.rs", "fn c() {}\n")
        self.write("crates/a/src/y.rs", "fn d() {}\n")
        self.write("crates/a/tests/t.rs", "fn e() {}\n")  # not below src/
        same = ["crates/a/src/lib.rs 2 3 4 5", "crates/a/src/x/tests.rs *"]
        note = "1 test files, 1 files with test modules"
        self.assertEqual(crosscheck.test_modules(self.root, json_cmd({"--test-items": same}), 1), ([], note))
        self.assertEqual(crosscheck.test_modules(self.root, json_cmd({"--test-items": same}))[0],
                         [f"onsa_cases --test-items: {note} (20 each at least)"])  # fmt: skip
        other = json_cmd({"--test-items": [same[1], "crates/a/src/lib.rs 2 3 4"]})
        problems, _ = crosscheck.test_modules(self.root, other)
        self.assertEqual(problems[1:], ["only the Rust scan: crates/a/src/lib.rs 2 3 4",
                                        "only tools/repo.py: crates/a/src/lib.rs 2 3 4 5"])  # fmt: skip
        problems, note = crosscheck.test_modules(self.root, json_cmd({"--test-items": []}), 0)
        self.assertEqual((problems, note), (["only tools/repo.py: " + x for x in same], "0 test files, 0 files with "
                                            "test modules"))  # fmt: skip

    def test_main(self):
        checks = (("ok", lambda root, cmd: []), ("bad", lambda root, cmd: ["x is wrong"]))
        self.assertEqual(quiet_out(crosscheck.main, [], self.root, None, checks), (1, ["ok: ok", "bad: x is wrong",
                         "cross-check: 2 check(s), 1 with problems"]))  # fmt: skip
        self.assertEqual(quiet_out(crosscheck.main, [], self.root, None, checks[:1])[0], 0)
        noted = (("n", lambda root, cmd: ([], "3 files")), ("m", lambda root, cmd: (["x", "y"], "1 file")))
        self.assertEqual(quiet_out(crosscheck.main, [], self.root, None, noted)[1][:3],
                         ["n: ok (3 files)", "m: x", "m: y (1 file)"])  # fmt: skip
        self.assertEqual(quiet_out(crosscheck.main, [], self.root, None, ())[0], 1)  # nothing checked fails
        broken = (("c", lambda root, cmd: crosscheck.repo.cases_json(root, ("false",), "--c-items")),)
        code, lines = quiet_out(crosscheck.main, [], self.root, None, broken)
        self.assertEqual(code, 1)
        self.assertTrue(lines[0].startswith("c: cannot check: `false --c-items` failed"), lines)


if __name__ == "__main__":
    unittest.main(verbosity=1)
