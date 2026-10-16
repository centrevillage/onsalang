#!/usr/bin/env python3
"""Make issues/RF/ from the items of the carryovers (X-2, 36th session; the cuts the user agreed to, I-1 to I-6).

    python3 -I migrate_rf.py <root>       # writes <root>/issues/RF/*.md and takes the lines out of
                                          # <root>/docs/carryovers.md; prints the check
Each RF is a head line cut into parts (the parts joined are the line after `- `, so nothing is lost
or made up) and blocks of lines moved under a label (indent shifted, text the same). Lines only
dropped are listed. The check reads the files back: every part and every line moved is there.
"""
import hashlib
import sys
from pathlib import Path

DOC = Path("docs") / "carryovers.md"
LABELS = ("場所", "内容", "経緯", "判断")  # DF-5, the order in a file

# head: (line, [(dest, text)]); dest: "id", "title" (also in the title), "drop" (the glue: brackets,
# the punctuation of a list), a label, or "title+<label>" (the text is the title and the label's).
# title: the title, pieces of the head line joined (checked), when not given by the parts.
# blocks: (label, first, last): the lines moved under the label.  more: (label, text) of the parent.
UNIT1 = "2026-10-10 に利用者が範囲を了承した `foreign.rs` の深いリファクタリングの単位 1（`7fd6b15`、2026-10-10）で済んだ。"
UNIT2 = "2026-10-10 に利用者が範囲を了承した `foreign.rs` の深いリファクタリングの単位 2（`826fc8a`、2026-10-11）で済んだ。"
RFS = [
    dict(id="RF-1", status="DONE", head=(167, [("id", "RF-1 "), ("title", "行の情報をトークンの属性に"), ("drop", "、")]),
         more=[("経緯", UNIT1)]),
    dict(id="RF-2", status="DONE", head=(168, [("id", "RF-2 "), ("title", "規則の表の行の優先（R-206）"), ("drop", "、")]),
         more=[("経緯", UNIT2)]),
    dict(id="RF-3", status="DONE",
         head=(169, [("id", "RF-3 "), ("title", "層の向き"), ("drop", "（"),
                     ("内容", "`layout`↔`parser` の循環、`lower::class`、`interpolated` を字句の段へ"), ("drop", "）、")]),
         more=[("経緯", UNIT1)]),
    dict(id="RF-4", status="DONE", head=(170, [("id", "RF-4 "), ("title", "呼び先の判定を一つの述語に"), ("drop", "。")]),
         more=[("経緯", UNIT2)]),
    dict(id="RF-5", status="OPEN", title=["強弱の判断の 3 か所"],
         head=(231, [("id", "RF-5 "), ("内容", "強弱の判断の 3 か所（`parser` の `tighter`、`lower` の `chain()`、`groups` の `Order::tighter`）と `groups.rs` が AST を `Flat::new` で平らに戻して読み直すこと、パーサの高さと AST の高さを突き合わせるテスト（W3-07/b）。")])),
    dict(id="RF-6", status="OPEN",
         head=(232, [("id", "RF-6 "), ("title", "構文解析器の内部の重複"), ("drop", "（"),
                     ("内容", "`PatReader` と `parse_pattern_alt`、`parse_type` の三通り、`MoveExpr` の節を作る場所 4 つ、`dump` と `fmt` の `parens`、`operand()` が字句から読み直す W3-21/b の R-2"),
                     ("drop", "）。")]),
         blocks=[("内容", 191, 195)]),
    dict(id="RF-7", status="OPEN",
         title=["`Why::Differ` を理由の列挙型に", "、`list_fixes` の分岐を表に、`Parser::ends` を閉じた節から導く"],
         head=(233, [("id", "RF-7 "), ("内容", "`Why::Differ` を理由の列挙型に（R-6）、`list_fixes` の分岐を表に、`Parser::ends` を閉じた節から導く（(1) の候補の約束の論点の後）。")]),
         blocks=[("内容", 190, 190)]),
    dict(id="RF-8", status="OPEN",
         head=(234, [("id", "RF-8 "), ("title", "sema・core の `children()` の 3 か所と `Ty`/`Rate`/`FlowRate` の並行"),
                     ("drop", "（"), ("場所", "構文の crate の外"), ("drop", "）。")])),
    dict(id="RF-9", status="OPEN",
         head=(235, [("id", "RF-9 "), ("title", "W3-05 の壊す側の候補"), ("drop", "（"),
                     ("経緯", "単位 1・単位 2・直しの往復 1 の再確認。報告は 17 回目の scratchpad の `w305b1/`・`w305b2/`・`w305b3/handback_b.md`"),
                     ("drop", "）:")]),
         blocks=[("内容", 236, 241)]),
    dict(id="RF-10", status="OPEN",
         head=(242, [("id", "RF-10 "), ("title", "P-1・B-1・W3-22 の範囲の外"), ("drop", "（"), ("経緯", "19 回目"), ("drop", "）:")]),
         blocks=[("内容", 243, 246)]),
    dict(id="RF-11", status="OPEN",
         head=(247, [("id", "RF-11 "), ("title", "旧版と FAUST の行と文の整理"), ("drop", "（"),
                     ("判断", "2026-10-13、21 回目、利用者: 旧版は正式なリリースまで、FAUST の文法の形はこれから対象にしない。`rules/criteria.md` 7.32"),
                     ("drop", "）:")]),
         blocks=[("内容", 248, 255)]),
    dict(id="RF-12", status="OPEN",
         head=(257, [("id", "RF-12 "), ("title", "W3-24 の範囲の外"), ("drop", "（"),
                     ("経緯", "22 回目、W3-24/i の直し 1 と W3-24/b の再確認"), ("drop", "）:")]),
         blocks=[("内容", 258, 260)]),
    dict(id="RF-13", status="OPEN",
         head=(261, [("id", "RF-13 "), ("title", "W3-11 の U3c の範囲の外"), ("drop", "（"),
                     ("経緯", "25 回目、W3-11/b の U3c"), ("drop", "）:")]),
         blocks=[("内容", 262, 262)]),
    dict(id="RF-14", status="OPEN",
         head=(263, [("id", "RF-14 "), ("title", "fmt の速さ"), ("drop", "（"),
                     ("経緯", "27 回目、W3-11 の U3b/i と U5/i の測り"), ("drop", "）:")]),
         blocks=[("内容", 264, 265), ("経緯", 266, 266)]),
    dict(id="RF-15", status="OPEN", title=["括弧を外す走査を `Ast::without_parens`", "の一つにする"],
         head=(348, [("drop", "リファクタリングの候補（"), ("id", "RF-15"), ("drop", "）: "),
                     ("内容", "括弧を外す走査を `Ast::without_parens`（W3-13 の U3 で置いた）の一つにする。残りは `onsa_sema` の `modes.rs` の `strip` と `onsa_syntax` の `groups.rs` の同じ走査。")])),
    dict(id="RF-16", status="OPEN",
         head=(267, [("id", "RF-16 "), ("title", "実行ファイルの大きさ"), ("drop", "（"),
                     ("経緯", "2026-10-16、32 回目、利用者: 実行ファイルが大きすぎる。リファクタリングに関わるかもしれない"),
                     ("drop", "）:")]),
         blocks=[("内容", 268, 272), ("判断", 273, 274)]),
]
# The goal and the conditions of all the RF (one place, the README): the head cut, its items moved.
README_HEAD = (163, [("drop", "目的と条件（"), ("date", "2026-10-10、12 回目、利用者"), ("drop", "）:")])
README_BLOCK = (164, 165)
DROPPED = {275: "the README's 目的と条件 has it (RF-5〜RF-16 have the conditions of RF-1〜RF-4)"}
# The numbers inside the reports of the works that are spelled as IDs (`docs.py check` reads them as
# R-2, R-6, S-1): the hyphen out and 指摘 before (the user's I-5, 2026-10-17; S-537's `D-1 の (ii)`).
# R-6 is W3-21/b's: the carryovers' list of the candidates of the 9th session names it with W3-21/b's R-2.
REWRITES = [
    ("RF-6", "W3-21/b の R-2", "W3-21/b の指摘 R2"),
    ("RF-7", "（R-6）", "（W3-21/b の指摘 R6）"),
    ("RF-10", "W3-22/b の S-1", "W3-22/b の指摘 S1"),
]
BASE_REV = "ee25322"
BASE = "b32ad5c1c3188c95a5b17188626a030c44d5be4bcd04842c2bb2bcc08901a734"  # sha256 of its docs/carryovers.md

README = """\
# リファクタリング（RF）

（仮。目的の一段落は親が書き、利用者が了承する。）

## 頭の欄

| キー | 形 | 値 | 要る | 意味 |
|---|---|---|---|---|
| `status` | 閉じた値 | `OPEN` / `WONTFIX` / `DONE` | はい | 状態 |
| `severity` | 閉じた値 | `高` / `中〜高` / `中` / `低〜中` / `低` | いいえ | 重さ |
| `spec` | 節の並び | — | いいえ | 仕様の節 |
| `decisions` | ID の並び（S） | — | いいえ | 決定 |
| `fix` | ID の並び（W） | — | いいえ | 直す作業 |
| `found_by` | 文字列 | — | いいえ | 見つけた票 |

## 本文のラベル

- `場所`: 直す所。
- `内容`: 何を直すか。
- `経緯`: 見つけた票、日付、材料。
- `判断`: 決めたこと（日付、誰）。

## 目的と条件

全ての RF に共通する（{date}）。

{items}
## 持ち越しから移した RF

RF-1〜RF-16 は、持ち越し（`docs/carryovers.md`）の箇条から移した（2026-10-17）。
箇条の頭の字は題と、括弧の中の出所（`経緯`）か決定（`判断`）に分け、下の箇条は字を変えずに、ラベルの下に置いた。
"""


def body_of(lines, n):
    """The text of line n after its bullet `- ` and its indent; and the indent."""
    line = lines[n - 1]
    indent = len(line) - len(line.lstrip(" "))
    assert line[indent:].startswith("- "), (n, line)
    return line[indent + 2:], indent


def moved(lines, first, last):
    """The lines first..last, the indent of the first taken off (kept relative)."""
    base = len(lines[first - 1]) - len(lines[first - 1].lstrip(" "))
    out = []
    for n in range(first, last + 1):
        line = lines[n - 1]
        assert line[:base].strip() == "", (n, line)
        out.append(line[base:])
    return out


def render(rf, lines):
    n, parts = rf["head"]
    text, _ = body_of(lines, n)
    assert "".join(t for _, t in parts) == text, (rf["id"], "the parts are not the line")
    title = rf.get("title")
    if title:
        assert all(p in text for p in title), (rf["id"], "a piece of the title is not in the line")
        title = "".join(title)
    else:
        title = "".join(t for d, t in parts if d in ("title", "title+内容"))
    items = {lab: [] for lab in LABELS}
    for d, t in parts:
        lab = d.removeprefix("title+")
        if lab in LABELS:
            items[lab].append((t, []))
    for lab, first, last in rf.get("blocks", ()):
        sub = ["  " + x for x in moved(lines, first, last)]
        if items[lab]:
            items[lab][-1][1].extend(sub)
        else:
            items[lab].append(("", sub))
    for lab, t in rf.get("more", ()):
        items[lab].append((t, []))
    out = ["+++", f'status = "{rf["status"]}"', "+++", f"# {rf['id']} {title}", ""]
    for lab in LABELS:
        for t, sub in items[lab]:
            out.append(f"- {lab}: {t}".rstrip() if t else f"- {lab}:")
            out.extend(sub)
    return "\n".join(out) + "\n"


def main(root):
    root = Path(root)
    raw = (root / DOC).read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE:
        sys.exit(f"migrate_rf: {DOC} is not the one of {BASE_REV} (the line numbers are its); nothing written")
    if (root / "issues" / "RF").exists():
        sys.exit("migrate_rf: issues/RF/ is there already; nothing written")
    lines = raw.decode("utf-8").split("\n")
    taken = {}  # line -> where
    for rf in RFS:
        taken[rf["head"][0]] = rf["id"]
        for _, a, b in rf.get("blocks", ()):
            for n in range(a, b + 1):
                assert n not in taken, (n, taken.get(n), rf["id"])
                taken[n] = rf["id"]
    n, parts = README_HEAD
    text, _ = body_of(lines, n)
    assert "".join(t for _, t in parts) == text
    date = next(t for d, t in parts if d == "date")
    readme_items = moved(lines, *README_BLOCK)
    for k in [n, *range(README_BLOCK[0], README_BLOCK[1] + 1)]:
        assert k not in taken
        taken[k] = "README"
    for k in DROPPED:
        assert k not in taken
        taken[k] = "dropped"
    files = {rf["id"]: render(rf, lines) for rf in RFS}
    readme = README.format(date=date, items="\n".join(readme_items) + "\n")
    # check: every line taken is in its file (a head by its parts, a block line by its text)
    for k, where in sorted(taken.items()):
        if where == "dropped":
            continue
        dest = readme if where == "README" else files[where]
        text = lines[k - 1].strip()
        heads = {rf["head"][0]: rf for rf in RFS}
        if k in heads:
            for d, t in heads[k]["head"][1]:
                assert d in ("drop", "id") or t in dest, (k, t)
        elif k == README_HEAD[0]:
            assert date in dest
        else:
            assert text in dest, (k, text[:40])
    # the numbers of the reports spelled as IDs (I-5), after the check: each once in its file
    for id_, old, new in REWRITES:
        assert files[id_].count(old) == 1, (id_, old)
        files[id_] = files[id_].replace(old, new)
        print(f"  {id_}: {old} -> {new}")
    out = root / "issues" / "RF"
    out.mkdir(parents=True)
    for id_, text in files.items():
        (out / f"{id_}.md").write_text(text, encoding="utf-8")
    (out / "README.md").write_text(readme, encoding="utf-8")
    left = [line for i, line in enumerate(lines, 1) if i not in taken]
    (root / DOC).write_text("\n".join(left), encoding="utf-8")
    print(f"migrate_rf: {len(files)} files and the README; {len(taken)} lines taken out of {DOC} "
          f"({sum(1 for w in taken.values() if w == 'README')} to the README, {len(DROPPED)} dropped)")
    for k, why in DROPPED.items():
        print(f"  dropped {DOC}:{k}: {why}\n    {lines[k - 1].strip()}")


if __name__ == "__main__":
    main(sys.argv[1])
