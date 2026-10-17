#!/usr/bin/env python3
"""X-2 移行の段 (5b) の、表の切り出し（`migrate_tables.py --kind W`）と持ち越しの振り分けの後の親の直し。

    python3 -B migrate_5b.py docs <リポジトリ> <tasks の README> <記録>   # 段の一覧と目的、診断コードの表、移した先、地図（onsa-docs）
    python3 -B migrate_5b.py code <リポジトリ> <記録>                    # 道具とテストのコメントの経路（親）
    python3 -B migrate_5b.py verify <リポジトリ> <基のコミット>           # stages.md と diag-codes.md が基の rework §2・§3 と計画 §5 と一致する

- 段の一覧（2026-10-17 の決定）: rework §2 の表から作業の数の欄を除いた行と「W10 の後は …」の一文、rework §3 の段ごとの見出しと
  目的の段落を、字を変えずに `tasks/stages.md` へ（見出しは一段上げる）。§3 の頭の「役割・印」の一文は W の README へ（親の README の字）。
- 診断コードの表: 計画 §5 の見出しの下から `---` の前までを、字を変えずに `tasks/diag-codes.md` へ。
- 残りの節に移した先を指す一文を置く。経路の直しは EDITS の一意一致置換。どれかが一致しなければ何も書かずに止まる。
どれも、対象のファイルを一度ずつ読んで切り出す一回の走査（字の数に線形）で、繰り返しは無い。
"""
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[4] / "tools"
sys.path.insert(0, str(TOOLS))
import docs as docs_tool  # noqa: E402

REWORK = "docs/rework-phase1.md"
PLAN = "docs/implementation-tasks.md"
STAGES = "tasks/stages.md"
DIAG = "tasks/diag-codes.md"
S2_HEAD, S3_HEAD, S4_HEAD = "## 2. 段の一覧\n\n", "## 3. 段ごとの作業\n\n", "## 4. "
MARKS_LINE = "表の「役割・印」は、`rules/process.md` 8.6 の役割の例外と印だけを書く（空欄は三つの票の組）。\n\n"
P5_HEAD, P6_HEAD = "## 5. 診断コードの実装表\n\n", "\n---\n\n## 6. "
S2_POINTER = S2_HEAD + "段の一覧は `tasks/stages.md` に移した（作業の数は `python3 -B tools/docs.py list W --stage <段>`）。\n\n---\n\n"
S3_POINTER = S3_HEAD + "作業は `tasks/W/` に、段の目的は `tasks/stages.md` に移した（[`tasks/README.md`](../tasks/README.md) から読む）。\n\n---\n\n"
P5_POINTER = "診断コードの実装表（元の §5）は `tasks/diag-codes.md` に移した。\n"  # no `## 5.`: repo reads it as the table still here

DOC_EDITS = {
    # W3-13: the qualifier of its mark 基盤（U3） goes to 単位 (MG-4; its marks is 基盤 by the overrides)
    "tasks/W/W3-13.md": [("\n- 実現する決定: C-01、", "\n- 単位: 基盤（U3）\n- 実現する決定: C-01、")],
    "rules/leader.md": [
        ("計画 `docs/implementation-tasks.md`（§5 の診断コード）。", "計画 `docs/implementation-tasks.md`。"),
        ("- 反映の作業 `docs/rework-phase1.md`（W の表は §3、改めた文書の記録は §5）。",
         "- 作業 `tasks/W/`、段の一覧と目的 `tasks/stages.md`、診断コードの表 `tasks/diag-codes.md`。元の反映の作業 `docs/rework-phase1.md`（改めた文書の記録は §5）。"),
    ],
}
CODE_EDITS = {
    "tests/pending.toml": [
        ("（docs/rework-phase1.md §3 の W の ID か、計画 §4 の T の ID）", "（`tasks/W/` の W の ID か、計画 §4 の T の ID）"),
        ("第 2 期のコードは計画 §5 の\n", "第 2 期のコードは `tasks/diag-codes.md` の\n"),
    ],
    "tools/pending.py": [("a W ID of `docs/rework-phase1.md` §3", "a W ID of `tasks/W/`")],
    "crates/onsa_diag/src/codes.rs": [("the retired codes of the plan §5 (S-109)", "the retired codes of `tasks/diag-codes.md` (S-109)")],
}


def cut(text, start, end, name):
    """(before, the text between, from `end` on): `start` and `end` once each, in that order."""
    if text.count(start) != 1 or text.count(end) < 1:
        raise SystemExit(f"{name}: {start[:30]!r} or {end[:30]!r} not found once; nothing written")
    i = text.index(start) + len(start)
    j = text.index(end, i)
    return text[: i - len(start)], text[i:j], text[j:]


def stages_from(rework):
    """(the rework with §2 and §3 pointing to tasks/, the text of stages.md)."""
    head, s2, rest = cut(rework, S2_HEAD, "\n---\n\n" + S3_HEAD, REWORK)
    rows, tail = [], []
    for line in s2.strip("\n").split("\n"):
        if line.startswith("|"):
            cells = docs_tool.table_cells(line)
            rows.append("| " + " | ".join(c.strip() for c in cells[:-1]) + " |")
        elif line:
            tail.append(line.replace("（§4）", "（`docs/rework-phase1.md` §4）"))  # rework's §4, not the spec's
    if not rows or not rows[0].startswith("| 段 | 名前 |"):
        raise SystemExit(f"{REWORK}: §2: no table of the stages; nothing written")
    rows[1] = "|" + "---|" * (len(rows[0].split("|")) - 2)
    _, s3, after = cut(rest, S3_HEAD, "\n---\n\n" + S4_HEAD, REWORK)
    if not s3.startswith(MARKS_LINE):
        raise SystemExit(f"{REWORK}: §3 does not start with the line of 役割・印; nothing written")
    sections, cur = [], None
    for line in s3[len(MARKS_LINE):].split("\n"):
        if line.startswith("### W"):
            cur = [line.replace("### ", "## ", 1)]
            sections.append(cur)
        elif line.startswith("|"):
            raise SystemExit(f"{REWORK}: §3 still has a table row (run migrate_tables.py --kind W first); nothing written")
        elif line and cur is None:
            raise SystemExit(f"{REWORK}: §3: text before the first stage: {line[:40]!r}; nothing written")
        elif line:
            cur.append(line)
    stages = ("# 段\n\n" + "\n".join(rows) + "\n\n" + "\n".join(tail) + "\n"
              + "".join("\n" + sec[0] + "\n" + ("\n" + "\n".join(sec[1:]) + "\n" if sec[1:] else "") for sec in sections))
    return head + S2_POINTER + S3_POINTER + after[len("\n---\n\n"):], stages


def diag_from(plan):
    head, body, rest = cut(plan, P5_HEAD, P6_HEAD, PLAN)
    return head + P5_POINTER + rest, "# 診断コード\n\n" + body.strip("\n") + "\n"


def apply_edits(root, edits, texts, log):
    for rel, pairs in edits.items():
        t = texts.get(rel) or (root / rel).read_text(encoding="utf-8")
        for old, new in pairs:
            if t.count(old) != 1:
                raise SystemExit(f"{rel}: {t.count(old)} match(es) of {old[:50]!r}; nothing written")
            t = t.replace(old, new)
            log.append(f"{rel}: {old[:60]!r} -> {new[:60]!r}")
        texts[rel] = t


def cmd_docs(root, readme, log_path):
    if (root / STAGES).exists() or (root / DIAG).exists() or not (root / "tasks/W").is_dir():
        raise SystemExit("migrate_5b docs: run it once, after `migrate_tables.py apply --kind W`; nothing written")
    texts, log = {}, []
    texts[REWORK], stages = stages_from((root / REWORK).read_text(encoding="utf-8"))
    texts[PLAN], diag = diag_from((root / PLAN).read_text(encoding="utf-8"))
    apply_edits(root, DOC_EDITS, texts, log)
    texts[STAGES], texts[DIAG], texts["tasks/README.md"] = stages, diag, Path(readme).read_text(encoding="utf-8")
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    log += [f"{STAGES}: rework §2 (without 作業の数) and §3's stages", f"{DIAG}: plan §5", "tasks/README.md: the parent's"]
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_5b docs: {len(texts)} file(s) written ({STAGES}, {DIAG}, tasks/README.md new); log {log_path}")


def cmd_code(root, log_path):
    texts, log = {}, []
    apply_edits(root, CODE_EDITS, texts, log)
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_5b code: {len(log)} edit(s) in {len(texts)} file(s); log {log_path}")


def cmd_verify(root, base):
    def show(rel):
        return subprocess.run(["git", "-C", str(root), "show", f"{base}:{rel}"], capture_output=True, text=True, check=True).stdout

    rework = show(REWORK)
    s3 = rework[rework.index(S3_HEAD) : rework.index("\n---\n\n" + S4_HEAD)]
    rework = rework.replace(s3, "\n".join(line for line in s3.split("\n") if not line.startswith("|")))  # the W rows gone
    want = {STAGES: stages_from(rework)[1], DIAG: diag_from(show(PLAN))[1]}
    bad = [rel for rel, t in want.items() if (root / rel).read_text(encoding="utf-8") != t]
    print("migrate_5b verify: " + (f"differs in {', '.join(bad)}" if bad else f"{STAGES} and {DIAG} the same as {base}"))
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
