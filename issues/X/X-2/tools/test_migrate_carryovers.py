#!/usr/bin/env python3
"""The self-test of `migrate_carryovers.py` on a made-up tree (not a test of the gate, X-2 DT-8).

    python3 -B issues/X/X-2/tools/test_migrate_carryovers.py
"""
import contextlib
import io
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import migrate_carryovers as mc  # noqa: E402

README = """\
# 作業（W）

## 頭の欄

| キー | 形 | 値 | 要る | 意味 |
|---|---|---|---|---|
| `status` | 閉じた値 | `PLAN` / `DONE` | はい | 状態 |
"""
CARRY = """\
# 作業の持ち越し

前書き。

- 約束 1。
  続き。
- 約束 2。

- **W1-01（1 回目）:** a
  - 入れ子
    続き。
- **W1-02:** b W9-09
- **W1-01:** c
- **W1-02・W2-01（x）:** d
- **W1-01 の後:** e
- **W2 の終わり:** f
  - g
- **M6:** h
- **M6:** h2
- **W2-01** i
- **W2-01**: j
"""
W12 = '+++\nstatus = "PLAN"\n+++\n# W1-02 b\n\n- 内容: x\n- 持ち越し:\n  - 前から\n    続き。\n- 結果: y\n'
TREE = {
    "docs/carryovers.md": CARRY,
    "tasks/W/README.md": README,
    "tasks/W/W1-01.md": '+++\nstatus = "DONE"\n+++\n# W1-01 a\n\n- 内容: x\n',
    "tasks/W/W1-02.md": W12,
    "tasks/W/W2-01.md": '+++\nstatus = "PLAN"\n+++\n# W2-01 c\n\n- 内容: z\n',
}
OVER = '[to]\n"W1-02・W2-01（x）" = "W2-01"\n"M6 #2" = "W1-01"\n"M6" = "keep"\n'
DOC = "docs/carryovers.md"


class Carry(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)
        self.root = self.tmp / "after"
        for rel, text in TREE.items():
            self.write(rel, text)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def read(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    def edit(self, rel, old, new):
        text = self.read(rel)
        self.assertEqual(text.count(old), 1, old)
        self.write(rel, text.replace(old, new))

    def run_tool(self, *argv, overrides=None):
        argv = [*argv, "--root", str(self.root)]
        if overrides is not None:
            (self.tmp / "over.toml").write_text(overrides, encoding="utf-8")
            argv += ["--overrides", str(self.tmp / "over.toml")]
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = mc.main(argv)
        return code, out.getvalue()

    def test_plan(self):
        code, out = self.run_tool("plan")
        self.assertEqual(code, 0, out)
        self.assertEqual(out.splitlines(), [
            f"{DOC}: 10 units; 5 to 3 files, 5 stay (5 listed)", "W1-01\t2", "W1-02\t1", "W2-01\t2",
            "== many-ids (1)", "14\tmany-ids\tW1-02・W2-01（x）", "== id-words (1)", "15\tid-words\tW1-01 の後",
            "== stage (1)", "16\tstage\tW2 の終わり", "== other (2)", "18\tother\tM6", "19\tother\tM6 #2",
            "items: many-ids 1, id-words 1, stage 1, other 2"])  # fmt: skip
        self.assertEqual(self.read(DOC), CARRY)

    def test_overrides(self):
        code, out = self.run_tool("plan", overrides=OVER)
        self.assertEqual(code, 0, out)
        self.assertIn(f"{DOC}: 10 units; 7 to 3 files, 3 stay (2 listed)\nW1-01\t3\nW1-02\t1\nW2-01\t3\n", out)
        for over, why in [('[to]\n"M6 #3" = "keep"\n', "M6 #3: not in the list of the judgements"),
                          ('[to]\n"W1-02:" = "W1-02"\n', "W1-02:: not in the list of the judgements"),  # sent by its head
                          ('[to]\n"M6" = "S-1"\n', "M6: 'S-1' is not keep or an ID of W"),
                          ('[to]\n"M6" = "W3-01"\n', "M6: tasks/W/W3-01.md is not there"),
                          ('[to]\n"M6" = ["W1-01"]\n', "M6: ['W1-01'] is not keep or an ID of W"),
                          ('[M6]\nto = "W1-01"\n', "M6: not the table `[to]`")]:  # fmt: skip
            with self.subTest(over=over):
                self.assertEqual(self.run_tool("plan", overrides=over), (1, f"{why}\nmigrate_carryovers.py plan: refused; nothing is written\n"))

    def test_a_missing_w_refuses(self):
        (self.root / "tasks/W/W2-01.md").unlink()
        code, out = self.run_tool("apply")
        self.assertEqual(code, 1, out)
        self.assertIn(f"{DOC}:20: tasks/W/W2-01.md is not there\n{DOC}:21: tasks/W/W2-01.md is not there\n", out)
        self.assertEqual(self.read(DOC), CARRY)

    def test_apply(self):
        code, out = self.run_tool("apply", overrides=OVER)
        self.assertEqual(code, 0, out)
        self.assertIn("moved 7 units (9 lines) of docs/carryovers.md to 3 files; 3 stay", out)
        self.assertIn("== body-ref (1)\ntasks/W/W1-02.md:10: W9-09 is not found (tasks/W/)", out)
        self.assertEqual(self.read(DOC), "# 作業の持ち越し\n\n前書き。\n\n- 約束 1。\n  続き。\n- 約束 2。\n\n"
                         "- **W1-01 の後:** e\n- **W2 の終わり:** f\n  - g\n- **M6:** h\n")  # fmt: skip
        self.assertEqual(self.read("tasks/W/W1-01.md"), '+++\nstatus = "DONE"\n+++\n# W1-01 a\n\n- 内容: x\n- 持ち越し:\n'
                         "  - **W1-01（1 回目）:** a\n    - 入れ子\n      続き。\n  - **W1-01:** c\n  - **M6:** h2\n")  # fmt: skip
        self.assertEqual(self.read("tasks/W/W1-02.md"), W12.replace("    続き。\n", "    続き。\n  - **W1-02:** b W9-09\n"))
        self.assertTrue(self.read("tasks/W/W2-01.md").endswith("- 内容: z\n- 持ち越し:\n  - **W1-02・W2-01（x）:** d\n  - **W2-01** i\n  - **W2-01**: j\n"))

    def apply_and_keep_before(self, over=OVER):
        shutil.copytree(self.root, self.tmp / "before")
        self.assertEqual(self.run_tool("apply", overrides=over)[0], 0)

    def verify(self, before=None):
        return self.run_tool("verify", "--before", str(before or self.tmp / "before"))

    def test_nothing_moved_is_a_difference(self):
        self.write(DOC, "# 持ち越し\n\n- **M6:** h\n")  # the units of a W would be found to stay
        shutil.copytree(self.root, self.tmp / "before")
        self.assertEqual(self.verify(), (1, f"{DOC}: 1 units before, 0 moved, 1 stay; 0 files changed\n"
                                            f"{DOC}: no unit moved (is `--before` the tree before `apply`?)\n"
                                            "migrate_carryovers.py verify: 1 difference(s)\n"))  # fmt: skip

    def test_round_trip(self):
        for over in (OVER, None):
            with self.subTest(over=over):
                self.setUp()
                self.apply_and_keep_before(over)
                code, out = self.verify()
                self.assertEqual(code, 0, out)
                self.assertIn(f"{DOC}: 10 units before, {7 if over else 5} moved, {3 if over else 5} stay; 3 files changed", out)
                self.assertTrue(out.endswith("migrate_carryovers.py verify: the same\n"), out)

    def test_round_trip_of_a_git_revision(self):
        def git(*argv):
            subprocess.run(["git", "-C", str(self.root), *argv], check=True, capture_output=True, timeout=30)

        git("init", "-q")
        git("add", ".")
        git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "t")
        self.assertEqual(self.run_tool("apply", overrides=OVER)[0], 0)
        self.assertEqual(self.verify("HEAD")[0], 0)
        self.edit("tasks/W/W2-01.md", "  - **W2-01**: j\n", "")
        self.assertEqual(self.verify("HEAD")[0], 1)

    W11, W21 = "tasks/W/W1-01.md", "tasks/W/W2-01.md"
    CHANGES = [
        (W11, "**W1-01（1 回目）:** a", "**W1-01（1 回目）:** A", "a unit put in is not one taken out"),  # a character
        (W11, "    - 入れ子", "   - 入れ子", "a unit put in is not one taken out"),  # the indent of a line in it
        (W11, "  - **W1-01:** c\n", "  - **W1-01:**  c\n", "a unit put in is not one taken out"),
        (W11, "  - **W1-01:** c\n  - **M6:** h2\n", "  - **M6:** h2\n  - **W1-01:** c\n", "not in their order"),
        (W11, "\n- 持ち越し:\n", "\n- 持ち越し：\n", "not at the end of `- 持ち越し:`"),  # the label
        (W11, "  - **M6:** h2\n", "  - **M6:** h2\n    続き\n", "a unit put in is not one taken out"),  # a line going on more
        (W11, "  - **M6:** h2\n", "  - **M6:** h2\n- 結果: x\n", "not 2 spaces in"),  # a line not in
        (W11, "  - **M6:** h2\n", "", "taken out, not put in"),  # a unit lost
        (W11, "- 内容: x\n", "- 内容: y\n", "not lines put in at one place"),  # another line of the file
        ("tasks/W/W1-02.md", "- 結果: y\n", "- 結果: z\n", "not lines put in at one place"),
        ("tasks/W/W1-02.md", "  - **W1-02:** b W9-09\n- 結果", "- 結果", "taken out, not put in"),
        ("tasks/W/W1-02.md", "    続き。\n  - **W1-02:** b W9-09\n- 結果: y\n", "    続き。\n- 結果: y\n  - **W1-02:** b W9-09\n",
         "not at the end of `- 持ち越し:`"),  # put after another label
        (W21, "  - **W2-01**: j\n", "  - **W2-01**: j\n  - **W1-02:** b W9-09\n", "a unit put in is not one taken out"),  # a unit twice
        (DOC, "- 約束 1。", "- 約束一。", "not the one before with whole units taken out"),
        (DOC, "  続き。\n", "", "not the one before with whole units taken out"),
        (DOC, "- **M6:** h\n", "- **M6:** H\n", "carryovers.md:22: from this line"),  # a unit kept, changed
        (DOC, "- **M6:** h\n", "", "taken out, not put in"),  # a unit kept, lost
        (DOC, "- **M6:** h\n", "- **M6:** h\n\nx", "1 line(s) more at the end"),
        (DOC, "- **M6:** h\n", "- **M6:** h\n- **W1-02:** b W9-09\n", "not the one before with whole units taken out"),  # a moved unit left too
    ]

    def test_a_change_is_found(self):
        for rel, old, new, why in self.CHANGES:
            with self.subTest(rel=rel, old=old):
                self.setUp()
                self.apply_and_keep_before()
                self.edit(rel, old, new)
                code, out = self.verify()
                self.assertEqual(code, 1, out)
                self.assertIn(why, out)

    def test_a_unit_of_its_w_that_stays_is_found(self):
        self.apply_and_keep_before()
        self.write(DOC, (self.tmp / "before" / DOC).read_text(encoding="utf-8"))
        for rel in ("tasks/W/W1-01.md", "tasks/W/W1-02.md", "tasks/W/W2-01.md"):
            self.write(rel, (self.tmp / "before" / rel).read_text(encoding="utf-8"))
        code, out = self.verify()
        self.assertEqual(code, 1, out)
        self.assertIn(f"{DOC}:9: stays, but its head names W1-01", out)

    def test_a_unit_in_another_w_is_found(self):
        self.apply_and_keep_before()
        self.edit("tasks/W/W1-02.md", "  - **W1-02:** b W9-09\n", "")
        self.edit("tasks/W/W2-01.md", "  - **W2-01**: j\n", "  - **W2-01**: j\n  - **W1-02:** b W9-09\n")
        code, out = self.verify()
        self.assertEqual(code, 1, out)
        self.assertIn("2 files changed\ntasks/W/W2-01.md: - **W1-02:** b W9-09 goes to W1-02\n", out)  # W1-02.md is as before


if __name__ == "__main__":
    unittest.main()
