#!/usr/bin/env python3
"""Self-tests of tools/refactor.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_refactor.py
"""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import refactor  # noqa: E402
import repo  # noqa: E402
from selftest_support import quiet_out  # noqa: E402


class Refactor(unittest.TestCase):
    """tools/refactor.py sizes (X-9 U17, X9-74): the files and the fns over the limits of rules/budgets.md, without the
    test files and the test modules, the braces in the strings and the comments not counted; and the help."""

    LIB = "\n".join([
        "pub fn six() {", '    let s = "{";', "    let c = '}';", "    // }", '    /* { */ let r = r#"a"}"#;', "}",
        "fn sig(", "    x: [u8; 4],", ") -> u8 {", "    let y = x[0];", "    y", "}",
        "fn five() {", "    let a = 1;", "    let b = 2;", "    let c = 3;", "}",
        "pub trait T {", "    fn decl(&self, x: [u8; 2]);", "}",  # no body: not the struct's brace
        "struct S {", "    a: u8,", "    b: u8,", "    c: u8,", "}",
        "fn outer() {", "    fn inner() {", *[f"        let v{i} = {i};" for i in range(4)], "    }", "}",
        "#[cfg(test)]", "mod tests {", "    fn long_test() {", *[f"        let v{i} = {i};" for i in range(4)], "    }",
        "}", ""])  # fmt: skip

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        long_fn = "fn long() {\n" + "    let a = 1;\n" * 20 + "}\n"
        for rel, text in (("a/src/lib.rs", self.LIB), ("a/src/small.rs", "const A: u8 = 0;\n" * 12),
                          ("b/src/m.rs", "const A: u8 = 0;\n" * 13), ("a/tests/long.rs", long_fn),
                          ("a/src/x_tests.rs", long_fn), ("a/src/tests.rs", long_fn),
                          ("a/src/mostly.rs", "fn m() {}\n#[cfg(test)]\nmod tests {\n" + long_fn + "}\n")):  # fmt: skip
            (self.root / "crates" / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / "crates" / rel).write_text(text)
        (self.root / "rules").mkdir()
        self.budget("`crates/` の関数は 5 行、ファイルは 12 行を超えるもの（テストを除く）")

    def budget(self, value, name=refactor.BUDGET):
        (self.root / "rules/budgets.md").write_text(f"| 名前 | 値 |\n|---|---|\n| 他 | 関数は 1 行 |\n| {name} | {value} |\n")

    def sizes(self):
        return quiet_out(refactor.main, ["sizes", "--root", str(self.root)])

    def test_sizes(self):
        self.assertEqual(self.sizes(), (0, [
            "sizes: over 5 lines of a fn and 12 of a file (rules/budgets.md「リファクタリングの対象の大きさ」), in the .rs "
            "files of crates/ without the tests and the test modules",
            "files over 12 lines: 2 of 4 (lines without the test modules, all)",
            "      33 (    42)  crates/a/src/lib.rs",
            "      13 (    13)  crates/b/src/m.rs",
            "fns over 5 lines: 4 (from `fn` to its closing brace)",
            "       8  crates/a/src/lib.rs:26  outer",
            "       6  crates/a/src/lib.rs:1  six",
            "       6  crates/a/src/lib.rs:7  sig",
            "       6  crates/a/src/lib.rs:27  inner"]))  # fmt: skip
        self.budget("関数は 6 行、ファイルは 40 行")  # the limits are the row's
        self.assertEqual(self.sizes()[1][1:], ["files over 40 lines: 0 of 4 (lines without the test modules, all)",
                                               "fns over 6 lines: 1 (from `fn` to its closing brace)",
                                               "       8  crates/a/src/lib.rs:26  outer"])  # fmt: skip
        self.assertIsInstance(refactor.limits(repo.ROOT), dict)  # the row of this repository reads

    def test_no_limits_exit_2(self):
        for value, name, says in (("x", "他の行", "no row 「リファクタリングの対象の大きさ」"),
                                  ("関数は 5 行", refactor.BUDGET, "the row 「リファクタリングの対象の大きさ」 says no lines")):  # fmt: skip
            with self.subTest(says=says):
                self.budget(value, name)
                code, lines = self.sizes()
                self.assertEqual((code, len(lines)), (2, 1), lines)
                self.assertTrue(lines[0].startswith(f"sizes: rules/budgets.md: {says}"), lines)
        (self.root / "rules/budgets.md").unlink()
        self.assertEqual(self.sizes()[0], 2)
        self.budget("関数は 5 行、ファイルは 12 行")
        shutil.rmtree(self.root / "crates/a/src")
        shutil.rmtree(self.root / "crates/b")
        self.assertEqual(self.sizes(), (2, [f"sizes: no .rs file in {self.root}/crates/ but the tests; nothing listed"]))

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in refactor.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^refactor\.py {name}( |$)")
                code, lines = quiet_out(refactor.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        self.assertEqual(refactor.COMMANDS["sizes"].roles, ("parent", "i", "b", "advisor"))
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(refactor.main, ["help", "--role", role])
                want = [n for n, c in refactor.COMMANDS.items() if role in c.roles]
                self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        names = list(refactor.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(refactor.main, ["help"])[1][: len(names)]], names)


if __name__ == "__main__":
    unittest.main(verbosity=1)
