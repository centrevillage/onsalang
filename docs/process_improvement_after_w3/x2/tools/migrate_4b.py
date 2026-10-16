#!/usr/bin/env python3
"""X-2 移行の段 (4b) の、表の切り出し（`migrate_tables.py --kind D|K|Q|A`）の後の親の直し。

    python3 -B migrate_4b.py docs <リポジトリ> <design の README> <記録>   # 設計を design/ へ、残りの節に移した先、経路の直し（onsa-docs）
    python3 -B migrate_4b.py code <リポジトリ> <記録>                     # 道具のコメントと文の経路（親）
    python3 -B migrate_4b.py verify <リポジトリ> <基のコミット>            # design/ の 6 ファイルが基の計画 §3 の節と一致する

- 設計（2026-10-17 の決定）: 計画 §3 の `### 3.N` の節を、見出しから字を変えずに `design/` の DESIGN のファイルへ移す。
  節の間は空行だけで、§3 の頭の一文は README の目的の段落に代わる。§3 には移した先を指す一行を残す。
- 残りの節（計画 §1・§3、rework §1、再発防止 §2・§4）に移した先を指す一文を置く。Q §4 の「Q-09（API への適用）」の行は Q-09 のファイルの末尾へ移す。
- `api-candidates.md` は、行が `decisions/A/` へ、頭の目的・方針・手順が `decisions/A/README.md` へ移った後に消す（方針の行が README にあることを確かめてから）。
- 経路の直し（利用者が了承、C-3）は EDITS の一意一致置換。どれかが一致しなければ何も書かずに止まる。移した決定の本文と記録の文書は直さない。
どれも、対象のファイルを一度ずつ読んで置換する一回の走査（字の数に線形）で、繰り返しは無い。
"""
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[4] / "tools"
sys.path.insert(0, str(TOOLS))
import docs as docs_tool  # noqa: E402

PLAN = "docs/implementation-tasks.md"
DESIGN = {"3.1": "01-diag.md", "3.2": "02-ast.md", "3.3": "03-types.md", "3.4": "04-core.md",
          "3.5": "05-flow-lowering.md", "3.6": "06-placement.md"}  # fmt: skip
DESIGN_HEAD = "## 3. 共通の設計\n\n計画 §2 を実装の型に落としたもの。クレートの境界で共有する。\n\n"
DESIGN_POINTER = "## 3. 共通の設計\n\n`design/` に移した（[`design/README.md`](../design/README.md) から読む）。\n\n"
API = "docs/api-candidates.md"
Q_REVIEW = "docs/process-improvement-phase1.md"
Q09_ROW_HEAD = "| Q-09（API への適用） | "
Q09_LINK = ("[`api-candidates.md`](api-candidates.md)", "`decisions/A/`")


def pointer(kind, what):
    return f"{what}は `decisions/{kind}/` に移した（[`decisions/{kind}/README.md`](../decisions/{kind}/README.md) から読む）。"


DOC_EDITS = {
    PLAN: [
        ("全て 2026-10-01 に案の通り決定。\n", "全て 2026-10-01 に案の通り決定。" + pointer("D", "D-01〜D-16 ") + "\n"),
    ],
    "docs/rework-phase1.md": [
        ("## 1. 判断した点\n\n", "## 1. 判断した点\n\n" + pointer("K", "K-01〜K-23 ") + "\n\n"),
        ("| W8-02 | 検証器の規則 | 計画 §3.4 の規則のうち", "| W8-02 | 検証器の規則 | `design/04-core.md` の規則のうち"),
        ("`init` の降下がそれを読む（計画 §3.5）。", "`init` の降下がそれを読む（`design/05-flow-lowering.md`）。"),
    ],
    Q_REVIEW: [
        ("## 2. 提案\n\n", "## 2. 提案\n\n" + pointer("Q", "Q-01〜Q-15 の本文") + "\n\n"),
        ("## 4. 決定の記録\n\n", "## 4. 決定の記録\n\nQ-01〜Q-15 の決定は、`decisions/Q/` の各ファイルの `決定` の箇条に移した。\n\n"),
    ],
    "rules/process.md": [
        ("（`docs/process-improvement-phase1.md` の Q-01、Q-04、Q-09〜Q-14、計画 D-15、D-16）", "（Q-01、Q-04、Q-09〜Q-14、D-15、D-16）"),
    ],
    "rules/criteria.md": [
        ("必要が確かめられていないものは、`docs/api-candidates.md` の候補にとどめる。", "必要が確かめられていないものは、`decisions/A/` の候補にとどめる。"),
        ("拒否で終わらせず、`docs/api-candidates.md` に候補として挙げる", "拒否で終わらせず、`decisions/A/` に候補として挙げる"),
    ],
    "rules/leader.md": [
        ("- 計画 `docs/implementation-tasks.md`（§1 の D、§2 の S、§5 の診断コード）。",
         "- 決定 `decisions/`（S・D・K・Q・A）。実装の共通の設計 `design/`。計画 `docs/implementation-tasks.md`（§5 の診断コード）。"),
        ("- 反映の作業 `docs/rework-phase1.md`（K の決定は §1、W の表は §3、改めた文書の記録は §5）。",
         "- 反映の作業 `docs/rework-phase1.md`（W の表は §3、改めた文書の記録は §5）。"),
        ("再発防止 `docs/process-improvement-phase1.md`。", "再発防止の原因の分析 `docs/process-improvement-phase1.md`。"),
        ("表示の約束 `spec/tools.md`。組込み API の候補 `docs/api-candidates.md`。", "表示の約束 `spec/tools.md`。"),
    ],
    "spec/06-functions.md": [
        ("[`docs/api-candidates.md`](../docs/api-candidates.md)", "[`decisions/A/`](../decisions/A/README.md)"),
    ] * 2,  # two places: the standard traits and the associated constants
    "spec/09-errors.md": [
        ("[`docs/api-candidates.md`](../docs/api-candidates.md)", "[`decisions/A/`](../decisions/A/README.md)"),
    ],
    "decisions/S/S-537.md": [
        ("（D-2 の (丙)。", "（W3-13 の判断の (丙)。"),
        ("（D-1 の (ii)。", "（W3-13 の判断の (ii)。"),
    ],
}
CODE_EDITS = {
    "tools/builtin_names.py": [
        ("belongs in one place (plan §3.6)", "belongs in one place (`design/06-placement.md`)"),
        ("the registry places of plan §3.6 (`REGISTRY`)", "the registry places of `design/06-placement.md` (`REGISTRY`)"),
        ("# The places of plan §3.6 that hold", "# The places of `design/06-placement.md` that hold"),
        ('"plan §3.6 instead of comparing the name here', '"`design/06-placement.md` instead of comparing the name here'),
    ],
    "tools/builtin_names.toml": [
        ("テストと計画 §3.6 の登録簿を除く所", "テストと `design/06-placement.md` の登録簿を除く所"),
        ("判断は計画 §3.6 の置き場所に置く。", "判断は `design/06-placement.md` の置き場所に置く。"),
    ],
}


def apply_edits(root, edits, texts, log):
    """Each (old, new) replaces the first `old` left, and must find one: one pair per place, in order."""
    for rel, pairs in edits.items():
        t = texts.get(rel)
        if t is None:
            t = (root / rel).read_text(encoding="utf-8")
        for old, new in pairs:
            n = t.count(old)
            if n == 0 or (n > 1 and pairs.count((old, new)) != n):
                raise SystemExit(f"{rel}: {n} match(es) of {old[:50]!r}; nothing written")
            t = t.replace(old, new, 1)
            log.append(f"{rel}: {old[:60]!r} -> {new[:60]!r}")
        texts[rel] = t


def split_design(plan_text):
    """(the plan with §3 pointing to design/, {file: text}) from the sections `### 3.N` of plan §3."""
    start = plan_text.index(DESIGN_HEAD)
    end = plan_text.index("\n---\n\n## 4. ", start) + 1
    body = plan_text[start + len(DESIGN_HEAD) : end].split("\n")
    files, cur = {}, None
    for line in body:
        if line.startswith("### 3."):
            num = line.split()[1]
            cur = DESIGN[num]
            files[cur] = []
        elif cur is None and line:
            raise SystemExit(f"{PLAN}: §3: text before the first `### 3.`: {line[:50]!r}")
        if cur is not None:
            files[cur].append(line)
    if list(files) != list(DESIGN.values()):
        raise SystemExit(f"{PLAN}: §3: the sections are {list(files)}, not {list(DESIGN.values())}")
    out = {}
    for name, lines in files.items():
        while lines and lines[-1] == "":
            lines.pop()
        out[name] = "\n".join(lines) + "\n"
    return plan_text[:start] + DESIGN_POINTER + plan_text[end:], out


def cmd_docs(root, readme, log_path):
    texts, log = {}, []
    plan, design = split_design((root / PLAN).read_text(encoding="utf-8"))
    texts[PLAN] = plan
    apply_edits(root, DOC_EDITS, texts, log)
    # Q §4: the row of Q-09 goes to the end of Q-09's file
    q = texts[Q_REVIEW].split("\n")
    rows = [i for i, line in enumerate(q) if line.startswith(Q09_ROW_HEAD)]
    if len(rows) != 1:
        raise SystemExit(f"{Q_REVIEW}: {len(rows)} row(s) of `Q-09（API への適用）`; nothing written")
    decision, date = (c.strip() for c in docs_tool.table_cells(q[rows[0]])[1:])
    if decision.count(Q09_LINK[0]) != 1:
        raise SystemExit(f"{Q_REVIEW}: the row of Q-09（API への適用） does not link api-candidates.md once")
    del q[rows[0]]
    texts[Q_REVIEW] = "\n".join(q)
    q09 = "decisions/Q/Q-09.md"
    item = f"- 決定（API への適用、{date}）: {decision.replace(*Q09_LINK)}"
    texts[q09] = (root / q09).read_text(encoding="utf-8").rstrip("\n") + "\n" + docs_tool.fmt_text(item)[0] + "\n"
    log.append(f"{Q_REVIEW}: the row of Q-09（API への適用） -> the end of {q09}")
    # api-candidates.md: only its head is left, which decisions/A/README.md has taken
    api = (root / API).read_text(encoding="utf-8")
    a_readme = (root / "decisions/A/README.md").read_text(encoding="utf-8")
    policy = api[api.index("## 方針\n") : api.index("## 手順\n")]
    if "|" in api[api.index("## 候補") :] or policy not in a_readme:
        raise SystemExit(f"{API}: rows are left, or decisions/A/README.md does not have its 方針; nothing written")
    readme_text = Path(readme).read_text(encoding="utf-8")
    if (root / "design").exists():
        raise SystemExit("design/: there already; nothing written")
    # all is made: write
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    (root / "design").mkdir()
    (root / "design/README.md").write_text(readme_text, encoding="utf-8")
    for name, t in design.items():
        (root / "design" / name).write_text(t, encoding="utf-8")
    log += [f"design/{name}: {t.count(chr(10))} lines from {PLAN} §3" for name, t in design.items()]
    (root / API).unlink()
    log.append(f"{API}: removed (the rows in decisions/A/, the head in decisions/A/README.md)")
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_4b docs: {len(texts)} file(s) edited, design/ with {len(design)} file(s) and README, {API} removed; log {log_path}")


def cmd_code(root, log_path):
    texts, log = {}, []
    apply_edits(root, CODE_EDITS, texts, log)
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_4b code: {len(log)} edit(s) in {len(texts)} file(s); log {log_path}")


def cmd_verify(root, base):
    old = subprocess.run(["git", "-C", str(root), "show", f"{base}:{PLAN}"], capture_output=True, text=True, check=True).stdout
    _, design = split_design(old)
    bad = [name for name, t in design.items() if (root / "design" / name).read_text(encoding="utf-8") != t]
    print(f"migrate_4b verify: design/ " + (f"differs in {', '.join(bad)}" if bad else f"the same as {base}:{PLAN} §3 ({len(design)} files)"))
    return 1 if bad else 0


def main(argv):
    if len(argv) == 4 and argv[0] == "docs":
        cmd_docs(Path(argv[1]), argv[2], argv[3])
    elif len(argv) == 3 and argv[0] == "code":
        cmd_code(Path(argv[1]), argv[2])
    elif len(argv) == 3 and argv[0] == "verify":
        return cmd_verify(Path(argv[1]), argv[2])
    else:
        raise SystemExit(__doc__)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
