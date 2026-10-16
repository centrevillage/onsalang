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
    TREE, KIND = TREE, "S"

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        for rel, text in self.TREE.items():
            self.write(rel, text)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def run_tool(self, cmd, overrides=None, kind=None):
        argv = [cmd, "--kind", kind or self.KIND, "--root", str(self.root)]
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


class Before(Tree):
    """A copy of the tree before, and `verify` against it."""

    def setUp(self):
        super().setUp()
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.before = Path(tmp.name) / "before"
        shutil.copytree(self.root, self.before)

    def verify(self, before=None, kind=None):
        argv = ["verify", "--kind", kind or self.KIND, "--root", str(self.root), "--before", str(before or self.before)]
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = mt.main(argv)
        return code, out.getvalue()

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1, (rel, old))
        p.write_text(text.replace(old, new), encoding="utf-8")


class Verify(Before):
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


# ---------------------------------------------------------------- D, K, Q and A (U5)

PLAN_D_HEAD = "# 計画\n\n---\n\n## 1. 実装の判断（D）\n\n全て 2026-10-01 に案の通り決定。\n"
PLAN_D_TAIL = "\n---\n\n## 2. 仕様の空白（S）\n\n`decisions/S/` に移した。\n"
D_UNITS = """
### D-01 手書きの解析器

- 案: 手書き（§2.3）。
- 理由: (1) 文脈。
  (2) 続きの行。

### D-02 アリーナ

- 案: ID で指す。

```text
### D-09 コードの中
```

- 代替: 無し。

### D-16 テストの基盤

- 決定（2026-10-06、利用者）。層:
  1. 仕様から。
"""
REWORK_K = """\
# rework

## 1. 判断した点

前書き。

### K-01 段の構成

- 論点: 段。
- 決定: 推奨のとおり（2026-10-07）。

### K-02 写し

- 決定（2026-10-08、親）: (a)。
  続き。

### K-03 日付の無い決定

- 決定: 案のとおり。
  続き。
- 経緯: 2026-10-09 に確かめた。

## 2. 段の一覧

## 3. 段ごとの作業

| ID | 作業 | 内容 | 実現する決定 | 依存 | 規模 | 役割・印 |
|---|---|---|---|---|---|---|
| W1-01 ✅ | a | b | D-02、K-01、Q-01 | — | S | 基盤 |
| W1-02 | c | d | K-01、Q-01（一部）、A-01 | W1-01 | M | メモ |

## 4. 残り
"""
PROCESS_HEAD = "# 再発防止\n\n---\n\n## 2. 提案\n\n### A. 期待値（原因 a）\n\n前書き（Q-01〜Q-02）。\n"
Q_UNITS = """
#### Q-01 別の担当
- 案:
  - 分ける。
- 推奨: 採る。

#### Q-02 参照を二つ
- 推奨: 採る。
"""
PROCESS_MID = "\n### B. 安全網\n"
Q_UNIT3 = "\n#### Q-03 網\n- 推奨: 採る。\n"
PROCESS_TAIL = "\n---\n\n## 3. 順序\n\n本文。\n\n## 4. 決定の記録\n\n| ID | 決定 | 日付 |\n|---|---|---|\n"
Q_ROWS = ["| Q-01 | 採る。`a \\| b` の形 | 2026-10-06 |", "| Q-02 | 採る。" + "文。" * 130 + " | 2026-10-05 |"]
Q_KEPT_ROWS = ["| 雛形 | まとめる | 2026-10-06 |", "| Q-04 | 見出しの無い行 | 2026-10-06 |"]
PROCESS_END = "\nQ-01〜Q-03 は決定した。\n\n## 5. 点検表\n"
API_HEAD = "# 組込み API の候補\n\n前書き。\n\n## 候補\n\n| ID | 候補 | 状態 | 実例・理由 |\n|---|---|---|---|\n"
A_ROWS = [
    "| A-01 | `is_some` | 不採用（2026-10-03） | 使われていない（W1-02） |",
    "| A-03 | `Str` の検索 | 保留（第 2 期） | 用途 `a \\| b` |",
    "| A-04 | メソッド形 | 採用（2026-10-04、利用者） | 理由 |",
    "| A-05 | 何か | 検討中 | 新しい語 |",
]
API_TAIL = "\n後書き。\n"
PROCESS = PROCESS_HEAD + Q_UNITS + PROCESS_MID + Q_UNIT3 + PROCESS_TAIL
PROCESS += "\n".join([Q_ROWS[0], Q_KEPT_ROWS[0], Q_ROWS[1], Q_KEPT_ROWS[1]]) + "\n" + PROCESS_END
TREE_DKQA = {
    "onsa-lang-spec-0.3.md": TREE["onsa-lang-spec-0.3.md"],
    "docs/onsa-tools.md": TREE["docs/onsa-tools.md"],
    PLAN: PLAN_D_HEAD + D_UNITS + PLAN_D_TAIL,
    "docs/rework-phase1.md": REWORK_K,
    "docs/process-improvement-phase1.md": PROCESS,
    "docs/api-candidates.md": API_HEAD + "\n".join(A_ROWS) + "\n" + API_TAIL,
    "decisions/README.md": README_FIELDS,
    "decisions/D/README.md": "# D\n",
    "decisions/K/README.md": "# K\n",
    "decisions/Q/README.md": "# Q\n",
}
# placed just before `apply --kind A`: `decisions/A/` and the rows of A both there is an error of `repo.Layout`
A_README = ("decisions/A/README.md", "# A\n\n## 本文のラベル\n\n- `候補`: 候補の欄。\n- `決定`: 状態の欄。\n- `理由`: 実例・理由の欄。\n")
DOCS = {"D": PLAN, "K": "docs/rework-phase1.md", "Q": "docs/process-improvement-phase1.md", "A": "docs/api-candidates.md"}
A_OVER = '[A-05]\nstatus = "OPEN"\n'


class DKQA(Tree):
    TREE = TREE_DKQA

    def read(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    def ids(self, kind):
        return sorted(p.stem for p in (self.root / "decisions" / kind).glob(f"{kind}-*.md"))

    def apply(self, kind):
        if kind == "A":
            self.write(*A_README)
        code, out = self.run_tool("apply", A_OVER if kind == "A" else None, kind=kind)
        self.assertEqual(code, 0, out)

    def test_plan(self):
        want = {
            "D": ("docs/implementation-tasks.md: 3 ranges: 3 headings -> 3 files", {("D-16", "decided", "decided")}),
            "K": ("docs/rework-phase1.md: 3 ranges: 3 headings", {("K-03", "decided", "decided")}),
            "Q": ("docs/process-improvement-phase1.md: 5 ranges: 3 headings",
                  {("雛形", "other-row", ""), ("Q-04", "no-heading", ""), ("Q-03", "no-row", "")}),
            "A": ("docs/api-candidates.md:7-12: 4 rows -> 4 files in decisions/A/", {("A-05", "status", "status,decided")}),
        }  # fmt: skip
        for kind, (head, items) in want.items():
            with self.subTest(kind=kind):
                code, out = self.run_tool("plan", kind=kind)
                self.assertEqual(code, 0, out)
                self.assertIn(head, out)
                self.assertEqual(self.items(out), items)

    def test_status_of(self):
        code, out = self.run_tool("plan", '[status_of]\n"検討中" = "OPEN"\n"保留" = "DROPPED"\n', kind="A")
        self.assertEqual((code, self.items(out)), (0, set()), out)
        self.assertIn("status DECIDED 2, DROPPED 1, OPEN 1", out)
        for over, kind in (('[status_of]\n"保留" = "DONE"\n', "A"), ('[status_of]\n"保留" = "OPEN"\n', "D"), ("status_of = 1\n", "A")):
            with self.subTest(over=over, kind=kind):
                self.assertEqual(self.run_tool("plan", over, kind=kind)[0], 1)

    def test_broken(self):
        for rel, old, new in [
            (PLAN, "### D-02 アリーナ\n", "### D-02 アリーナ\n\n"),  # a blank line more under the heading
            (PLAN, "### D-16 テストの基盤", "### D-01 テストの基盤"),  # an ID twice
            ("docs/process-improvement-phase1.md", "#### Q-01 別の担当\n", "#### Q-01 別の担当\n\n"),  # Q has none
            ("docs/process-improvement-phase1.md", "| ID | 決定 | 日付 |", "| ID | 決定 |"),  # not the header
            ("docs/process-improvement-phase1.md", "| 2026-10-05 |", "|"),  # a row of two cells
        ]:  # fmt: skip
            with self.subTest(old=old):
                self.setUp()
                self.write(rel, self.read(rel).replace(old, new, 1))
                self.assertEqual(self.run_tool("plan", kind="Q" if "process" in rel else "D")[0], 2)

    def test_apply(self):
        for kind in "DKQA":
            self.apply(kind)
        self.assertEqual(self.read(PLAN), PLAN_D_HEAD + PLAN_D_TAIL)
        self.assertEqual(self.read(DOCS["Q"]), PROCESS_HEAD + PROCESS_MID + PROCESS_TAIL + "\n".join(Q_KEPT_ROWS) + "\n" + PROCESS_END)
        self.assertEqual(self.read(DOCS["A"]), "# 組込み API の候補\n\n前書き。\n\n## 候補\n\n" + API_TAIL)
        self.assertNotIn("### K-", self.read(DOCS["K"]))
        self.assertIn("## 1. 判断した点\n\n前書き。\n\n## 2. 段の一覧", self.read(DOCS["K"]))
        self.assertEqual([self.ids(k) for k in "DKQA"], [["D-01", "D-02", "D-16"], ["K-01", "K-02", "K-03"],
                                                          ["Q-01", "Q-02", "Q-03"], ["A-01", "A-03", "A-04", "A-05"]])  # fmt: skip
        self.assertEqual(self.read("decisions/D/D-01.md"), '+++\nstatus = "DECIDED"\ndecided = 2026-10-01\n+++\n'
                         "# D-01 手書きの解析器\n\n- 案: 手書き（§2.3）。\n- 理由: (1) 文脈。\n  (2) 続きの行。\n")  # fmt: skip
        self.assertIn("```text\n### D-09 コードの中\n```\n\n- 代替: 無し。\n", self.read("decisions/D/D-02.md"))
        self.assertIn('tasks = ["W1-01"]', self.read("decisions/D/D-02.md"))
        self.assertIn("decided = 2026-10-08", self.read("decisions/K/K-02.md"))
        self.assertNotIn("decided", self.read("decisions/K/K-03.md"))  # the date is not of the item `- 決定`
        self.assertEqual(self.read("decisions/Q/Q-01.md"), '+++\nstatus = "DECIDED"\ntasks = ["W1-01", "W1-02"]\ndecided = 2026-10-06\n'
                         "+++\n# Q-01 別の担当\n\n- 案:\n  - 分ける。\n- 推奨: 採る。\n- 決定: 採る。`a | b` の形\n")  # fmt: skip
        q2 = self.read("decisions/Q/Q-02.md").split("\n")
        self.assertTrue(q2[-3].startswith("- 決定: 採る。文。") and q2[-2].startswith("  文。"), q2[-4:])  # fmt_text
        self.assertTrue(self.read("decisions/Q/Q-03.md").endswith("# Q-03 網\n\n- 推奨: 採る。\n"))
        self.assertEqual(self.read("decisions/A/A-03.md"), '+++\nstatus = "OPEN"\n+++\n# A-03\n\n- 候補: `Str` の検索\n'
                         "- 決定: 保留（第 2 期）\n- 理由: 用途 `a | b`\n")  # fmt: skip
        self.assertIn('status = "DECIDED"\ntasks = ["W1-02"]\ndecided = 2026-10-03\n', self.read("decisions/A/A-01.md"))
        with contextlib.redirect_stdout(io.StringIO()) as check:
            self.assertEqual(docs.main(["check", "--root", str(self.root)]), 0, check.getvalue())

    def test_status_required(self):
        self.write(*A_README)
        code, out = self.run_tool("apply", kind="A")  # A-05: no status
        self.assertEqual(code, 1, out)
        self.assertEqual(self.ids("A"), [])

    def test_labels(self):
        self.write("decisions/A/README.md", "# A\n")
        self.assertEqual(self.run_tool("apply", A_OVER, kind="A")[0], 1)
        shutil.rmtree(self.root / "decisions/A")
        self.apply("D")  # the README of D lists no label

    def test_readme_of_a_before_its_rows_go(self):
        self.write(*A_README)
        self.assertEqual(self.run_tool("apply", kind="D")[0], 2)  # `repo.Layout`: A in both


class VerifyDKQA(Before):
    TREE = TREE_DKQA
    apply = DKQA.apply

    CHANGES = {
        "D": [("decisions/D/D-01.md", "(2) 続きの行。", "(2) 続きの行"),  # a character of the text
              ("decisions/D/D-01.md", "# D-01 手書きの解析器", "# D-01 手書き"),  # the title
              ("decisions/D/D-02.md", "# D-02 アリーナ\n\n", "# D-02 アリーナ\n"),  # no blank line after the heading
              ("decisions/D/D-02.md", 'tasks = ["W1-01"]\n', ""),  # `tasks` not the rework's
              ("decisions/D/D-16.md", None, None),  # the file removed
              (PLAN, "全て 2026-10-01", "全て 2026-10-02")],  # outside the units
        "K": [("decisions/K/K-02.md", "  続き。", "  続き"), ("decisions/K/K-03.md", "\n  続き。", "\n続き。")],
        "Q": [("decisions/Q/Q-01.md", "- 決定: 採る。`a | b` の形", "- 決定: 採る。`a | c` の形"),  # the cell of the row
              ("decisions/Q/Q-01.md", "decided = 2026-10-06", "decided = 2026-10-07"),  # the date of the row
              ("decisions/Q/Q-01.md", "- 決定: 採る。`a | b` の形\n", ""),  # the row
              ("decisions/Q/Q-03.md", "- 推奨: 採る。\n", "- 推奨: 採る。\n- 決定: x\n"),  # a row it had not
              ("decisions/Q/Q-02.md", "\n  文。", "\n文。"),  # a broken line not going on
              (DOCS["Q"], "| 雛形 | まとめる | 2026-10-06 |\n", "")],  # a row that stays
        "A": [("decisions/A/A-04.md", "- 理由: 理由", "- 理由: 理"), ("decisions/A/A-04.md", "- 理由: 理由\n", ""),
              (DOCS["A"], "後書き。", "後書き")],
    }  # fmt: skip

    def test_round_trip(self):
        for kind in "DKQA":
            self.apply(kind)
            code, out = self.verify(kind=kind)
            with self.subTest(kind=kind):
                self.assertEqual(code, 0, out)
                self.assertIn("verify: the same", out)
        self.assertIn("round trip: 5 headings and rows, 3 files read back; IDs 3; `tasks` of 1 Q from the rework", self.verify(kind="Q")[1])

    def test_escaped_bar_is_normalized(self):
        self.apply("A")
        self.edit("decisions/A/A-03.md", "`a | b`", "`a \\| b`")
        self.assertEqual(self.verify(kind="A")[0], 0)

    def test_a_change_is_found(self):
        for kind, changes in self.CHANGES.items():
            for rel, old, new in changes:
                with self.subTest(kind=kind, rel=rel, old=old):
                    self.setUp()
                    self.apply(kind)
                    if old is None:
                        (self.root / rel).unlink()
                    else:
                        self.edit(rel, old, new)
                    code, out = self.verify(kind=kind)
                    self.assertEqual(code, 1, out)
                    self.assertIn("difference(s)", out)

    def test_no_rows_before(self):
        self.apply("D")
        (self.before / PLAN).write_text(PLAN_D_HEAD + PLAN_D_TAIL, encoding="utf-8")
        self.assertEqual(self.verify(kind="D")[0], 1)


if __name__ == "__main__":
    unittest.main()
