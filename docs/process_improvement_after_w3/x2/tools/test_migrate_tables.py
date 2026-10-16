#!/usr/bin/env python3
"""The self-test of `migrate_tables.py` on a made-up tree (not a test of the gate, X-2 DT-8).

    python3 -B docs/process_improvement_after_w3/x2/tools/test_migrate_tables.py
"""
import contextlib
import io
import shutil
import subprocess
import sys
import tempfile
import unittest
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import migrate_tables as mt  # noqa: E402

import docs  # noqa: E402  (on the path through migrate_tables)

PLAN_HEAD = """\
# 計画

`S` は 2026-10-02 に全て決定し（S-03 は取り下げ）、仕様へ反映した。

---

## 2. 仕様の空白（S）

前書き。

"""
ROWS = [
    "| S-01 ✅ | 名前の規則（§2.3） | E0320 にする | M1 |",
    "| S-02 ✅ | 外の書き方（§6.2） | 一つにする。2026-10-04 決定 | W2 |",
    "| S-03 | 生成の形 | 取り下げ。収録した | — |",
    "| S-173 ✅ | 経緯の語（§2.3、§9.9） | 決めた。親の案は取り下げた（2026-10-05、利用者）。S-02 の文を改めた | W1 |",
    "| S-174 | 位置の規則 | 決定（2026-10-08、利用者が了承。第 3 組: 前の位置） | W3 |",
    "| S-175 ✅ | 区切り `a \\| b` の形 | 取り下げ（2026-10-10、利用者）。`x \\| y` のまま | W1 |",
    "| S-176 | 二つの見出し | 案 | W1-02 |",
    "| S-177 ✅ | 長い行 | " + "文。" * 130 + "決定（2026-10-09、第 2 組。利用者） | M2 |",
]
TABLE = "| ID | 項目 | 提案 | 決める時期 |\n|---|---|---|---|\n" + "\n".join(ROWS) + "\n"
PLAN_TAIL = "\n---\n\n## 3. 共通の設計\n\n本文。\n"
README_FIELDS = """\
# 決定

## 頭の欄

| キー | 形 | 値 | 要る | 意味 |
|---|---|---|---|---|
| `status` | 閉じた値 | `OPEN` / `DECIDED` / `DROPPED` | はい | 状態 |
| `spec` | 節の並び | — | いいえ | 仕様の節 |
| `tasks` | ID の並び（W、T、P2） | — | いいえ | 担う作業 |
| `amends` | ID の並び（S、D、K、Q、A） | — | いいえ | 改めた前の決定 |
| `amended_by` | ID の並び（S、D、K、Q、A） | — | いいえ | 改めた後の決定 |
| `before` | ID（W） | — | いいえ | 期限の作業 |
| `group` | 整数 | — | いいえ | 組 |
| `decided` | 日付 | — | いいえ | 決めた日 |
"""
README_LABELS = """\
# 空白（S）

## 本文のラベル

- `空白`: 仕様が決めていないこと。
- `決定`: 決めたこと。
- `経緯`: 日付、誰が了承したか。

## 表から移した S

- `提案`: 提案の欄。
- `時期`: 決める時期の欄。
- `元の下書き`: 空白の資料の見出し。
"""
TREE = {
    "onsa-lang-spec-0.3.md": "# Spec\n\n## 2. 字句\n\n### 2.3 名前\n\n## 6. 型\n\n### 6.2 x\n",
    "docs/onsa-tools.md": "# tools\n\n## 3. 道具\n\n### 3.2 graph\n",
    "docs/implementation-tasks.md": PLAN_HEAD + TABLE + PLAN_TAIL,
    "docs/rework-phase1.md": "## 3. 段ごとの作業\n\n| ID | 作業 | 内容 | 実現する決定 | 依存 | 規模 | 役割・印 |\n"
                             "|---|---|---|---|---|---|---|\n| W1-01 ✅ | a | b | S-01、S-175 | — | S | 基盤 |\n"
                             "| W1-02 | c | d | S-176、S-173（一部） | W1-01 | M | メモ |\n\n## 4. 残り\n",
    "docs/onsa-0.3-changes.md": "## 4. 追記\n\n| ID | 内容 | 仕様 |\n|---|---|---|\n"
                                "| S-01 / S-02 | x | §2.3、onsa-tools.md §3.2 |\n| S-03 | y | — |\n\n## 5. 次\n",
    "docs/spec-gaps-w1.md": "# 空白\n\n## 第 2 組（2026-10-08）: S-176、S-177\n\n### S-176 一つ目の題\n\n### S-177 長い題\n\n"
                            "```\n### S-01 コードの中\n```\n\n## 第 3 組（2026-10-08）: S-176（書き直し）\n\n### S-176 二つ目の題\n\n"
                            "### S-174（確認だけ） 位置\n",
    "decisions/README.md": README_FIELDS,
    "decisions/S/README.md": README_LABELS,
}
PLAN = "docs/implementation-tasks.md"


class Tree(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        for rel, text in TREE.items():
            self.write(rel, text)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def run_tool(self, cmd, overrides=None):
        argv = [cmd, "--kind", "S", "--root", str(self.root)]
        if overrides is not None:
            argv += ["--overrides", str(self.write("over.toml", overrides))]
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = mt.main(argv)
        return code, out.getvalue() + err.getvalue()

    def items(self, out):
        """{(ID, class, keys)} of the lines of the list."""
        return {tuple(line.split("\t")[:3]) for line in out.splitlines() if line.count("\t") == 4}

    def results(self):
        units, _, _ = mt.read_table(self.root, mt.S_RULE)
        results, _ = mt.run(mt.S_RULE, units, mt.S_RULE.context(self.root), {})
        return {r.unit.id: r for r in results}

    def files(self):
        return sorted(p.name for p in (self.root / "decisions" / "S").glob("S-*.md"))


class Plan(Tree):
    LIST = {
        ("S-173", "spec", "spec"),
        ("S-173", "amends", "amends,amended_by (S-02)"),
        ("S-174", "status", "status,decided"),
        ("S-175", "status", "status,decided"),
        ("S-176", "group", "group"),
        ("S-176", "title", "title"),
        ("S-02", "nodest", ""),
    }

    def test_list(self):
        code, out = self.run_tool("plan")
        self.assertEqual(code, 0, out)
        self.assertEqual(self.items(out), self.LIST)
        self.assertIn("docs/implementation-tasks.md:11-20: 8 rows -> 8 files in decisions/S/", out)
        self.assertIn("nodest-open 1", out)  # S-174 (W3, no work of W3): only counted
        self.assertNotIn("\tnodest-open\t", out)

    def test_overrides_leave_out_what_they_fill(self):
        code, out = self.run_tool("plan", '[S-174]\nstatus = "DECIDED"\n[S-176]\ntitle = "二つ目の題"\n[S-02]\namended_by = ["S-173"]\n')
        self.assertEqual(code, 0, out)
        self.assertEqual(self.items(out), self.LIST - {
            ("S-174", "status", "status,decided"), ("S-176", "title", "title"), ("S-173", "amends", "amends,amended_by (S-02)"),
        })  # fmt: skip

    def test_refused(self):
        for over in ['[S-01]\nstatus = "OPEN"\n', '[S-176]\ntitle = "他の題"\n', '[S-174]\nstatus = "DONE"\n',
                     '[S-173]\nspec = "§2.3"\n', '[S-176]\nfound_by = "x"\n', 'S-01 = 1\n']:  # fmt: skip
            with self.subTest(over=over):
                code, out = self.run_tool("plan", over)
                self.assertEqual(code, 1, out)
                self.assertIn("refused", out)

    def test_no_rows(self):
        self.write(PLAN, PLAN_HEAD + PLAN_TAIL)
        self.assertEqual(self.run_tool("plan")[0], 1)

    def test_broken_table(self):
        for text in [PLAN_HEAD + TABLE.replace("決める時期", "時期") + PLAN_TAIL, PLAN_HEAD + TABLE + ROWS[0] + "\n" + PLAN_TAIL,
                     PLAN_HEAD + TABLE.replace("| M2 |", "| M2 | x |") + PLAN_TAIL]:  # fmt: skip
            with self.subTest(text=text[-80:]):
                self.write(PLAN, text)
                self.assertEqual(self.run_tool("plan")[0], 2)

    def test_context_read_nothing(self):
        for rel, text in [("docs/spec-gaps-w1.md", None), ("docs/onsa-0.3-changes.md", "## 4. 追記\n\n## 5. 次\n"),
                          ("docs/rework-phase1.md", "## 3. 段ごとの作業\n\n## 4. 残り\n")]:  # fmt: skip
            with self.subTest(rel=rel):
                self.setUp()
                if text is None:
                    (self.root / rel).unlink()
                else:
                    self.write(rel, text)
                self.assertEqual(self.run_tool("plan")[0], 2)


class Rules(Tree):
    def test_status_and_decided(self):
        r = self.results()
        got = {i: (r[i].values["status"], r[i].values["decided"]) for i in r}
        self.assertEqual(got, {
            "S-01": ("DECIDED", date(2026, 10, 2)),  # no date in the row, ✅ up to S-172
            "S-02": ("DECIDED", date(2026, 10, 4)),  # `YYYY-MM-DD 決定` before 2026-10-02
            "S-03": ("DROPPED", None),
            "S-173": ("DECIDED", None),  # `取り下げ` not at the head; its date is not `決定`
            "S-174": ("OPEN", None),  # `決定（` with no ✅: listed
            "S-175": ("DROPPED", None),  # ✅ and `取り下げ` at the head: listed
            "S-176": ("OPEN", None),
            "S-177": ("DECIDED", date(2026, 10, 9)),  # the last `決定（…）`
        })  # fmt: skip

    def test_spec_tasks_before_group(self):
        r = self.results()
        self.assertEqual(r["S-01"].values["spec"], ["§2.3", "tools.md §3.2"])  # the changes, `onsa-tools.md` as `tools.md`
        self.assertEqual(r["S-02"].values["spec"], ["§2.3", "tools.md §3.2"])  # the changes before the item
        self.assertIsNone(r["S-03"].values["spec"])  # a row of the changes with no `§`: not the item
        self.assertEqual(r["S-173"].values["spec"], ["§2.3"])  # the item; §9.9 is no heading
        self.assertEqual(r["S-175"].values["tasks"], ["W1-01"])
        self.assertEqual(r["S-173"].values["tasks"], ["W1-02"])
        self.assertEqual(r["S-176"].values["before"], "W1-02")
        self.assertIsNone(r["S-174"].values["before"])  # a stage is not a work
        self.assertEqual(r["S-177"].values["group"], 2)  # the heading and `決定（…）` agree
        self.assertEqual(r["S-174"].values["group"], 3)  # no heading: `決定（…）`
        self.assertIsNone(r["S-176"].values["group"])  # two headings: listed
        self.assertIsNone(r["S-01"].values["group"])

    def test_titles(self):
        r = self.results()
        self.assertEqual(r["S-177"].title, "長い題")
        self.assertEqual(r["S-174"].title, "（確認だけ） 位置")
        self.assertIsNone(r["S-176"].title)
        self.assertEqual(r["S-176"].extra["元の下書き"],
                         "`spec-gaps-w1.md` の「### S-176 一つ目の題」、`spec-gaps-w1.md` の「### S-176 二つ目の題」")  # fmt: skip
        self.assertIsNone(r["S-01"].title)  # a heading in a code block is not one
        self.assertEqual(r["S-01"].extra, {})


class Apply(Tree):
    def test_apply(self):
        code, out = self.run_tool("apply")
        self.assertEqual(code, 0, out)
        self.assertEqual(self.files(), [f"{i}.md" for i in sorted(r.split(" ")[1] for r in ROWS)])
        self.assertEqual((self.root / PLAN).read_text(encoding="utf-8"), PLAN_HEAD + PLAN_TAIL)
        self.assertIn("took out docs/implementation-tasks.md:11-20 (10 lines)", out)
        self.assertIn("== body-ref (1)\ndecisions/S/S-173.md:", out)  # §9.9 in the text: only reported
        s175 = (self.root / "decisions/S/S-175.md").read_text(encoding="utf-8")
        self.assertEqual(s175, '+++\nstatus = "DROPPED"\ntasks = ["W1-01"]\n+++\n# S-175\n\n- 空白: 区切り `a | b` の形\n'
                               "- 提案: 取り下げ（2026-10-10、利用者）。`x | y` のまま\n- 時期: W1\n")  # fmt: skip
        s177 = (self.root / "decisions/S/S-177.md").read_text(encoding="utf-8").split("\n")
        self.assertEqual(s177[:4], ["+++", 'status = "DECIDED"', "group = 2", "decided = 2026-10-09"])
        self.assertTrue(s177[8].startswith("- 提案: 文。") and s177[9].startswith("  文。"), s177[8:10])  # fmt_text
        self.assertEqual(s177[-2], "- 元の下書き: `spec-gaps-w1.md` の「### S-177 長い題」")
        with contextlib.redirect_stdout(io.StringIO()) as check:
            self.assertEqual(docs.main(["check", "--root", str(self.root)]), 1)
        self.assertIn("(tables 0, heads 0, refs 1, relations 0, links 0)", check.getvalue())

    def test_overrides(self):
        code, out = self.run_tool("apply", '[S-174]\nstatus = "DECIDED"\n[S-176]\ntitle = "二つ目の題"\ngroup = 3\n'
                                           '[S-173]\namends = ["S-02"]\n[S-02]\namended_by = ["S-173"]\n')  # fmt: skip
        self.assertEqual(code, 0, out)
        s174 = (self.root / "decisions/S/S-174.md").read_text(encoding="utf-8")
        self.assertTrue(s174.startswith('+++\nstatus = "DECIDED"\ngroup = 3\ndecided = 2026-10-08\n+++\n'), s174)
        self.assertIn("\n# S-176 二つ目の題\n", (self.root / "decisions/S/S-176.md").read_text(encoding="utf-8"))
        self.assertIn('amended_by = ["S-173"]', (self.root / "decisions/S/S-02.md").read_text(encoding="utf-8"))

    def assert_nothing_written(self, code, out):
        self.assertEqual(code, 1, out)
        self.assertEqual((self.root / PLAN).read_text(encoding="utf-8"), TREE[PLAN])
        self.assertEqual(self.files(), [])

    def test_check_before_writing_stops(self):
        for over in ['[S-173]\namends = ["S-02"]\n',  # (c): one side only
                     '[S-173]\nspec = ["§2.3", "§9.9"]\n']:  # (b) of the head fields: no heading
            with self.subTest(over=over):
                self.assert_nothing_written(*self.run_tool("apply", over))

    def test_refused_overrides_write_nothing(self):
        self.assert_nothing_written(*self.run_tool("apply", '[S-01]\nstatus = "OPEN"\n'))

    def test_conditions(self):
        self.write("decisions/S/S-09.md", "x\n")
        code, out = self.run_tool("apply")
        self.assertEqual(code, 1, out)
        self.assertEqual((self.root / PLAN).read_text(encoding="utf-8"), TREE[PLAN])
        (self.root / "decisions/S/S-09.md").unlink()
        (self.root / "decisions/README.md").unlink()
        self.assert_nothing_written(*self.run_tool("apply"))
        self.write("decisions/README.md", README_FIELDS)
        self.write("decisions/S/README.md", README_LABELS.replace("- `時期`", "- `期日`"))
        self.assert_nothing_written(*self.run_tool("apply"))


class Verify(Tree):
    def setUp(self):
        super().setUp()
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.before = Path(tmp.name) / "before"
        shutil.copytree(self.root, self.before)

    def verify(self, before=None):
        argv = ["verify", "--kind", "S", "--root", str(self.root), "--before", str(before or self.before)]
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = mt.main(argv)
        return code, out.getvalue()

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1, (rel, old))
        p.write_text(text.replace(old, new), encoding="utf-8")

    def test_round_trip(self):
        self.assertEqual(self.run_tool("apply")[0], 0)
        code, out = self.verify()
        self.assertEqual(code, 0, out)
        self.assertIn("normalized: the order of the rows", out)
        self.assertIn("round trip: 8 rows, 8 files read back; IDs 8; `tasks` of 4 S from the rework; ✅ and status apart", out)
        self.assertEqual([x for x in out.splitlines() if x.startswith("S-")], ["S-175: ✅ -> DROPPED"])

    def test_overrides_apart_only_for_the_items(self):
        self.assertEqual(self.run_tool("apply", '[S-174]\nstatus = "DECIDED"\n')[0], 0)
        code, out = self.verify()
        self.assertEqual(code, 0, out)
        self.assertEqual([x for x in out.splitlines() if x.startswith("S-")], ["S-174: no ✅ -> DECIDED", "S-175: ✅ -> DROPPED"])

    def test_escaped_bar_is_normalized(self):
        self.assertEqual(self.run_tool("apply")[0], 0)
        self.edit("decisions/S/S-175.md", "`a | b`", "`a \\| b`")
        self.assertEqual(self.verify()[0], 0)

    CHANGES = [
        ("decisions/S/S-01.md", "E0320 にする", "E0321 にする"),  # a character of a cell
        ("decisions/S/S-01.md", 'status = "DECIDED"', 'status = "OPEN"'),  # ✅ apart, not a `status` item
        ("decisions/S/S-02.md", None, None),  # the file removed
        ("decisions/S/S-03.md", "- 時期: —\n", "- 時期: —\n- 他: x\n"),  # a line more
        ("decisions/S/S-03.md", "- 空白: 生成の形\n", ""),  # a line less
        ("decisions/S/S-177.md", "\n# S-177 長い題\n", "\n# S-177 別の題\n"),  # a title of no draft
        ("decisions/S/S-01.md", "# S-01\n", "# S-01 題\n"),  # a title where there is no draft
        ("decisions/S/S-177.md", "の「### S-177 長い題」", "の「### S-177 題」"),  # the item of the draft
        ("decisions/S/S-175.md", 'tasks = ["W1-01"]', 'tasks = ["W1-02"]'),  # `tasks` not the rework's
        ("decisions/S/S-177.md", "\n  文。", "\n文。"),  # a broken line not going on
        ("decisions/S/S-03.md", "- 提案: 取り下げ", "- 提案:  取り下げ"),  # a space more
        (PLAN, "本文。", "本文"),  # outside the table
    ]

    def test_a_change_is_found(self):
        for rel, old, new in self.CHANGES:
            with self.subTest(rel=rel, old=old):
                self.setUp()
                self.assertEqual(self.run_tool("apply")[0], 0)
                if old is None:
                    (self.root / rel).unlink()
                else:
                    self.edit(rel, old, new)
                code, out = self.verify()
                self.assertEqual(code, 1, out)
                self.assertIn("difference(s)", out)

    def test_no_rows_before(self):
        self.assertEqual(self.run_tool("apply")[0], 0)
        (self.before / PLAN).write_text(PLAN_HEAD + PLAN_TAIL, encoding="utf-8")
        self.assertEqual(self.verify()[0], 1)

    def test_git_revision(self):
        git = ["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@example.com"]
        for argv in (["init", "-q"], ["add", "-A"], ["commit", "-q", "-m", "before"]):
            subprocess.run(git + argv, check=True, capture_output=True, timeout=60)
        self.assertEqual(self.run_tool("apply")[0], 0)
        code, out = self.verify("HEAD")
        self.assertEqual(code, 0, out)
        self.assertEqual(self.verify("no-such-rev")[0], 2)


if __name__ == "__main__":
    unittest.main()
