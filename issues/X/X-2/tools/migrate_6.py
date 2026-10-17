#!/usr/bin/env python3
"""X-2 移行の段 (6) の、文書を履歴へ移す親の道具。

    python3 -B migrate_6.py move <リポジトリ> <README の置き場所> <記録>      # 履歴、索引、経路の直し（onsa-docs）
    python3 -B migrate_6.py verify <リポジトリ> <基のコミット> <README の置き場所>  # 履歴は基と一致、直しは EDITS だけ

- 履歴: `docs/` の文書（DOCS、16）と直下の古い版の仕様（OLD_SPECS、3）を、名前を変えずに `history/` へ（木が git なら
  `git mv`）。`docs/` を消す。`docs/` に DOCS の外のファイルがあれば、何も書かずに止まる。
- 索引: 直下の `README.md` と `history/README.md` を、README の置き場所の親の字にする。
- 経路の直し: EDITS の一意一致置換。今の規範・索引・コードとテストのコメントだけを直す（ID のファイルの本文と材料は記録なので
  直さず、`history/README.md` が読み方を言う）。段 (3)〜(5b) の後に古いまま残った経路（計画の §1・§3・§5、折り返した
  `docs/foreign-forms.toml`）も、今の置き場所にする。書く前に全ての一致を確かめ、どれかが一つに一致しなければ何も書かない。
どれも対象のファイルを一度ずつ読む一回の走査（字の数に線形）で、繰り返しは無い。
"""
import shutil
import subprocess
import sys
from pathlib import Path

DOCS = (
    "comparison-ori-kumi.md", "consistency-check-phase1.md", "impl-review-0.3.md", "implementation-plan.md",
    "implementation-tasks.md", "kumi-vs-rust.md", "onsa-0.2-changes.md", "onsa-0.3-changes.md",
    "process-improvement-phase1.md", "review-draft-0.1.md", "review-draft-0.2.md", "review-impl-phase1.md",
    "rework-phase1.md", "spec-gaps-w1.md", "spec-gaps-w2-w3.md", "spec-gaps-w3b.md",
)  # fmt: skip
OLD_SPECS = ("onsa-lang-spec-0.2.md", "kumi-lang-spec.md", "ori-lang-spec.md")
HISTORY = "history"
READMES = ("README.md", f"{HISTORY}/README.md")  # the parent's text (37 回目)
FOREIGN = "; docs/\n// foreign-forms.toml", "; spec/\n// foreign-forms.toml"  # wrapped, left by the stage (3)
EDITS = {
    "spec/README.md": [
        ("[`onsa-lang-spec-0.2.md`](../onsa-lang-spec-0.2.md)", "[`history/onsa-lang-spec-0.2.md`](../history/onsa-lang-spec-0.2.md)"),
        ("[`docs/review-draft-0.2.md`](../docs/review-draft-0.2.md)", "[`history/review-draft-0.2.md`](../history/review-draft-0.2.md)"),
        ("[`docs/onsa-0.3-changes.md`](../docs/onsa-0.3-changes.md)", "[`history/onsa-0.3-changes.md`](../history/onsa-0.3-changes.md)"),
    ],
    "tasks/stages.md": [("（`docs/rework-phase1.md` §4）", "（`history/rework-phase1.md` §4）")],
    "tests/review-phase1/README.md": [
        ("[`docs/review-impl-phase1.md`](../../docs/review-impl-phase1.md)", "[`history/review-impl-phase1.md`](../../history/review-impl-phase1.md)"),
    ],
    "issues/RF/README.md": [
        ("（仮。目的の一段落は親が書き、利用者が了承する。）",
         "構造の健全さと保守性のための直し（リファクタリング）の候補と、行うかの判断。壊す側・実装・親の確かめが見つけた候補を、親が登録する。"
         "行う作業は頭の欄の `fix` に書き、作業のファイルには書かない。\n\n- 一覧は `python3 -B tools/docs.py list RF`。"),
    ],
    # the comments of the code: where the plan's sections are now (§1 D → decisions/D, §3 → design/, §5 → tasks/, §4 → the history)
    "crates/onsa_backend_c/src/lib.rs": [("(docs/implementation-tasks.md §1 D-10)", "(D-10)")],
    "crates/onsa_backend_js/src/lib.rs": [("see `docs/implementation-tasks.md`.", "see `history/implementation-tasks.md`.")],
    "crates/onsa_backend_wasm/src/lib.rs": [("see `docs/implementation-tasks.md`.", "see `history/implementation-tasks.md`.")],
    "crates/onsa_lsp/src/lib.rs": [("see `docs/implementation-tasks.md`.", "see `history/implementation-tasks.md`.")],
    "crates/onsa_web/src/lib.rs": [("see `docs/implementation-tasks.md`.", "see `history/implementation-tasks.md`.")],
    "crates/onsa_core/src/ir.rs": [("(docs/implementation-tasks.md §3.4, D-03)", "(`design/04-core.md`, D-03)")],
    "crates/onsa_core/src/lib.rs": [("See `docs/implementation-tasks.md` §3.4 for the IR shape and §1 D-03 for",
                                     "See `design/04-core.md` for the IR shape and D-03 for")],
    "crates/onsa_core/src/lower/flow.rs": [("(T3-5; docs/implementation-tasks.md §1 D-03 and §3.5; spec",
                                            "(T3-5; D-03 and `design/05-flow-lowering.md`; spec")],
    "crates/onsa_diag/src/codes.rs": [("(spec §18.1, `docs/implementation-tasks.md` §5)", "(spec §18.1, `tasks/diag-codes.md`)")],
    "crates/onsa_driver/src/lib.rs": [("(`docs/implementation-tasks.md` §4)", "(`history/implementation-tasks.md` §4)")],
    "crates/onsa_sema/src/ty.rs": [("(spec §4, `docs/implementation-tasks.md` §3.3)", "(spec §4, `design/03-types.md`)")],
    # the comments of the tests: `docs/foreign-forms.toml` wrapped at the line end, left by the stage (3)
    **{f"tests/spec/fixes/{name}{ext}": [FOREIGN] for name in (
        "e0020_callee_literal_chain.onsa", "e0020_callee_literal_number.onsa", "e0020_callee_literal_places.onsa",
        "e0020_callee_literal_text.onsa", "e0020_leading_operator_heads.onsa") for ext in ("", ".fix1")},
    "tests/spec/negative/foreign_not_in_table.onsa": [("(docs/foreign-\n// forms.toml", "(spec/foreign-\n// forms.toml")],
    "tests/spec/ops/block_operand_parenthesized.onsa": [("keeps them (docs/\n// spec/tools.md §3.3)", "keeps them (spec/\n// tools.md §3.3)")],
}


def edited(root, rel, text=None):
    """The text of `rel` with its EDITS; SystemExit when one does not match once."""
    t = (root / rel).read_text(encoding="utf-8") if text is None else text
    for old, new in EDITS[rel]:
        if t.count(old) != 1:
            raise SystemExit(f"{rel}: {t.count(old)} match(es) of {old[:50]!r}; nothing written")
        t = t.replace(old, new)
    return t


LEADER = "rules/leader.md"
MAP_HEAD = "## 付録. 文書の地図\n"
MAP_NEW = MAP_HEAD + "\n文書の地図は直下の [`README.md`](../README.md) にある。\n"  # the map goes to the root's README (DS-6, DF-7)


def leader_text(text):
    """rules/leader.md with its appendix, the last section, made one line pointing to the root's README."""
    if text.count(MAP_HEAD) != 1 or "\n## " in text[text.index(MAP_HEAD) + len(MAP_HEAD):]:
        raise SystemExit(f"{LEADER}: the map is not the last section once; nothing written")
    return text[: text.index(MAP_HEAD)] + MAP_NEW


def cmd_move(root, readmes, log_path):
    root, readmes = Path(root), Path(readmes)
    found = sorted(p.name for p in (root / "docs").iterdir())
    if found != sorted(DOCS) or (root / HISTORY).exists() or not all((root / s).is_file() for s in OLD_SPECS):
        raise SystemExit(f"migrate_6 move: docs/ is not {len(DOCS)} documents, {HISTORY}/ is there, or an old spec is not; nothing written")
    texts, log = {}, []
    for rel in EDITS:
        texts[rel] = edited(root, rel)
        log += [f"{rel}: {o!r} -> {n!r}" for o, n in EDITS[rel]]
    texts[LEADER] = leader_text((root / LEADER).read_text(encoding="utf-8"))
    log.append(f"{LEADER}: the map -> one line to README.md")
    for rel in READMES:
        texts[rel] = (readmes / rel).read_text(encoding="utf-8")
    git = (root / ".git").exists()
    (root / HISTORY).mkdir()
    for src in [f"docs/{n}" for n in DOCS] + list(OLD_SPECS):
        dst = f"{HISTORY}/{Path(src).name}"
        if git:
            subprocess.run(["git", "-C", str(root), "mv", src, dst], check=True)
        else:
            shutil.move(str(root / src), str(root / dst))
        log.append(f"{src} -> {dst}")
    (root / "docs").rmdir()
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    log += [f"{rel}: the parent's text" for rel in READMES]
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_6 move: {len(DOCS) + len(OLD_SPECS)} document(s) to {HISTORY}/, docs/ removed, "
          f"{sum(len(p) for p in EDITS.values())} edit(s) in {len(EDITS)} file(s), the leader's map, {len(READMES)} README(s); log {log_path}")


def cmd_verify(root, base, readmes):
    root, readmes = Path(root), Path(readmes)

    def show(rel):
        return subprocess.run(["git", "-C", str(root), "show", f"{base}:{rel}"], capture_output=True, check=True).stdout

    bad = [p for p in ("docs", *OLD_SPECS) if (root / p).exists()]
    for src in [f"docs/{n}" for n in DOCS] + list(OLD_SPECS):
        dst = root / HISTORY / Path(src).name
        if not dst.is_file() or dst.read_bytes() != show(src):
            bad.append(dst.relative_to(root).as_posix())
    for rel in READMES:
        if (root / rel).read_bytes() != (readmes / rel).read_bytes():
            bad.append(rel)
    for rel in [*EDITS, LEADER]:
        before = show(rel).decode("utf-8")
        want = leader_text(before) if rel == LEADER else edited(root, rel, before)
        if (root / rel).read_text(encoding="utf-8") != want:
            bad.append(rel)
    print("migrate_6 verify: " + (f"differs in {', '.join(bad)}" if bad else
          f"{len(DOCS) + len(OLD_SPECS)} document(s) in {HISTORY}/ the same as {base}, docs/ gone, "
          f"the READMEs the parent's, {len(EDITS) + 1} file(s) the base with the edits only"))
    return 1 if bad else 0


def main(argv):
    if len(argv) == 4 and argv[0] == "move":
        cmd_move(argv[1], argv[2], argv[3])
    elif len(argv) == 4 and argv[0] == "verify":
        return cmd_verify(argv[1], argv[2], argv[3])
    else:
        raise SystemExit(__doc__)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
