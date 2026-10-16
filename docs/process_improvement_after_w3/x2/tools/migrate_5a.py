#!/usr/bin/env python3
"""X-2 移行の段 (5a) の、表の切り出し（`migrate_tables.py --kind R`）の後の親の直し。

    python3 -B migrate_5a.py docs <リポジトリ> <記録>   # レビューの残りの節に移した先、規則の地図（onsa-docs）
    python3 -B migrate_5a.py code <リポジトリ> <記録>   # 道具とテストのコメントの経路（親）

- R の本文はレビュー §1〜§3・§5 の見出しの節から、§8 の行は各 R の末尾の `判断`・`反映` へ移った。残りの節に移した先を指す一文を置く。
- 経路の直しは EDITS の一意一致置換。どれかが一致しなければ何も書かずに止まる。移した R の本文と記録の文書は直さない。
どれも、対象のファイルを一度ずつ読んで置換する一回の走査（字の数に線形）で、繰り返しは無い。
"""
import sys
from pathlib import Path

REVIEW = "docs/review-impl-phase1.md"
POINTER = "は `issues/R/` に移した（[`issues/R/README.md`](../issues/R/README.md) から読む）。"


def after_heading(heading, what):
    return (f"{heading}\n\n", f"{heading}\n\n{what}{POINTER}\n\n")


DOC_EDITS = {
    REVIEW: [
        after_heading("## 1. 仕様とのずれ（観点 1）", "この節の R "),
        after_heading("## 2. 構造の健全性と保守性（観点 2）", "この節の R "),
        after_heading("## 3. 仕様に無い前提（観点 3）", "この節の R "),
        after_heading("## 5. テストの基盤", "R-113 "),
        ("ここには決定の要約と反映先を書く。\n",
         "ここには決定の要約と反映先を書く。\n\nR の行は、`issues/R/` の各ファイルの末尾の `判断`・`反映` の箇条に移した。\n"),
    ],
    "rules/leader.md": [
        ("- レビュー `docs/review-impl-phase1.md`（新しい R は §3 の末尾の本文と §8 の表）。",
         "- 問題 `issues/R/`（R）とリファクタリング `issues/RF/`（RF）。元のレビュー `docs/review-impl-phase1.md`。"),
    ],
}
CODE_EDITS = {
    "tests/pending.toml": [
        ("（一つ以上。計画 §2 の S、レビュー §8 の R）", "（一つ以上。`decisions/S/` の S、`issues/R/` の R）"),
    ],
    "tests/fuzz/allowed.toml": [
        ("the S numbers of plan §2 that put it outside the contract, or the R numbers of the review\n",
         "the S numbers (`decisions/S/`) that put it outside the contract, or the R numbers (`issues/R/`)\n"),
    ],
    "tools/fuzz.py": [
        ("`reasons` (S numbers of plan §2, or R numbers of\nthe review for a low harm recorded there)",
         "`reasons` (S numbers of `decisions/S/`, or R numbers of\n`issues/R/` for a low harm recorded there)"),
    ],
    "tools/gap_marks.py": [
        ("S (plan §2), R (review §8) or A\n(`docs/api-candidates.md`).", "S (`decisions/S/`), R (`issues/R/`) or A\n(`decisions/A/`)."),
    ],
}


def apply_edits(root, edits, log):
    """Each (old, new) must match once in its file; all are made before any is written."""
    texts = {}
    for rel, pairs in edits.items():
        t = (root / rel).read_text(encoding="utf-8")
        for old, new in pairs:
            if t.count(old) != 1:
                raise SystemExit(f"{rel}: {t.count(old)} match(es) of {old[:50]!r}; nothing written")
            t = t.replace(old, new)
            log.append(f"{rel}: {old[:60]!r} -> {new[:60]!r}")
        texts[rel] = t
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    return texts


def cmd(name, edits, root, log_path):
    if (root / REVIEW).read_text(encoding="utf-8").count("\n#### R-") or not (root / "issues/R").is_dir():
        raise SystemExit(f"migrate_5a {name}: run it after `migrate_tables.py apply --kind R`; nothing written")
    log = []
    texts = apply_edits(root, edits, log)
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_5a {name}: {len(log)} edit(s) in {len(texts)} file(s); log {log_path}")


def main(argv):
    if len(argv) == 3 and argv[0] in ("docs", "code"):
        cmd(argv[0], DOC_EDITS if argv[0] == "docs" else CODE_EDITS, Path(argv[1]), argv[2])
    else:
        raise SystemExit(__doc__)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
