#!/usr/bin/env python3
"""X-2 移行の段 (3): 仕様を `spec/` の章に分け、ツールの仕様と外の書き方の表を `spec/` へ移し、経路を直す。

    python3 -B migrate_spec.py docs <リポジトリ> <記録>   # 仕様を切って移し、文書の経路を直す（onsa-docs）
    python3 -B migrate_spec.py code <リポジトリ> <記録>   # 道具・コード・テストの経路を直す（親）
    python3 -B migrate_spec.py verify <リポジトリ> <基のコミット>

- 切り方は `tools/test_gate.py` の `split_spec` と同じ（README は `## 2.` の前と章の一覧、章は `## N.` から）。
  章のファイル名は CHAPTERS（利用者が了承、S3-1）。README の章の一覧は §・見出し・ファイルだけ（S3-2）。
- 往復: 切った直後に `repo.spec_text` が元の仕様とバイトで一致し、移した二つのファイルも元と一致する（一致しなければ何も書かずに止める）。
- 経路（S3-3）: 文書のリンクの行き先は、移る前の場所で解いて、移った後の場所から指し直す。文の中の経路の名指しは MENTIONS で直す。
  記録の文書（履歴へ行くもの、X の材料）と、今の配置を読む道具（`tools/repo.py`）と今の配置の作り物（`tools/test_gate.py`）は直さない。
- verify: 基のコミットの仕様に同じ経路の直しを当てたものと `repo.spec_text` が一致し、直す対象に古い経路が残っていない。
どれも、対象のファイルを一度ずつ読んで一行ずつ直す一回の走査（行の数に線形）で、繰り返しは無い。
"""
import posixpath
import re
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[4] / "tools"
sys.path.insert(0, str(TOOLS))
import docs as docs_tool  # noqa: E402
import repo  # noqa: E402

SPEC_OLD = "onsa-lang-spec-0.3.md"
CHAPTERS = {
    2: "lexical", 3: "operators", 4: "types", 5: "values", 6: "functions", 7: "control", 8: "effects", 9: "errors",
    10: "realtime", 11: "flow", 12: "memory", 13: "portability", 14: "ffi", 15: "modules", 16: "context",
    17: "examples", 18: "diagnostics", 19: "undecided", 20: "order",
}
MOVED = {  # 移る前 → 移った後（リンクの行き先を解くため。仕様の章はどれも spec/ の中なので README で代える）
    SPEC_OLD: "spec/README.md",
    "docs/onsa-tools.md": "spec/tools.md",
    "docs/foreign-forms.toml": "spec/foreign-forms.toml",
}
MENTIONS = [  # 文の中の経路の名指し（長いものから）
    ("docs/onsa-tools.md", "spec/tools.md"),
    ("docs/foreign-forms.toml", "spec/foreign-forms.toml"),
    ("onsa-tools.md", "spec/tools.md"),  # `docs/` の無い名指し（`tools.md §3.2` の節の参照は `onsa-` が無いので当たらない）
    (SPEC_OLD, "spec/"),
]
MENTION_RE = re.compile("|".join(re.escape(a) for a, _ in MENTIONS))
MENTION_TO = dict(MENTIONS)
# 一か所ずつの直し（ファイル、元の字、新しい字）。MENTIONS より先に当てる。どれも一度だけ当たること
MANUAL = [
    ("CLAUDE.md", "仕様は `onsa-lang-spec-0.3.md`。", "仕様は `spec/`（入口は `spec/README.md`）。"),
]
# 直さないもの
RECORDS = (  # 記録の文書（履歴へ行くもの、X の材料、古い版）
    "docs/spec-gaps-", "docs/onsa-0.2-changes.md", "docs/onsa-0.3-changes.md", "docs/review-draft-", "docs/consistency-check-phase1.md",
    "docs/process-improvement-phase1.md", "docs/impl-review-0.3.md", "docs/comparison-ori-kumi.md", "docs/kumi-vs-rust.md",
    "docs/implementation-plan.md", "docs/process_improvement_after_w3", "onsa-lang-spec-0.2.md",
)
OLD_LAYOUT_READERS = ("tools/repo.py", "tools/test_gate.py")
TEXT_SUFFIXES = (".md", ".py", ".rs", ".onsa", ".toml", ".sh", ".txt", ".h", ".c", ".json", ".fix1", ".fix2", ".fix3", ".fix4")


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True, text=True).stdout


def tracked(root):
    return [p for p in git(root, "ls-files", "-z").split("\0") if p]


def targets(root, part):
    """直す対象のファイル（根からの経路）。docs: 文書（.md と CLAUDE.md）、code: 道具・コード・テスト。"""
    out = []
    for rel in tracked(root):
        if rel.startswith(RECORDS) or rel.startswith(".claude/") or rel in OLD_LAYOUT_READERS:
            continue
        is_doc = rel.endswith(".md") and not rel.startswith(("tests/", "crates/", "tools/", "std/"))
        is_code = rel.startswith(("tests/", "crates/", "tools/", "std/")) and rel.endswith(TEXT_SUFFIXES)
        if (part == "docs" and is_doc) or (part == "code" and is_code):
            out.append(rel)
    return sorted(out)


def relink(target, old_file, new_file):
    """リンクの行き先 `target`（old_file から見た相対）を、new_file から見た相対に直す。外のリンクと錨はそのまま。"""
    if not target or docs_tool.EXTERNAL.match(target):
        return target
    path, sep, anchor = target.partition("#")
    resolved = posixpath.normpath(posixpath.join(posixpath.dirname(old_file), path))
    resolved = MOVED.get(resolved, resolved)
    if resolved == posixpath.normpath(posixpath.join(posixpath.dirname(new_file), path)):
        return target  # 行き先も自分も動かない
    return posixpath.relpath(resolved, posixpath.dirname(new_file) or ".") + sep + anchor


def rewrite_text(text, old_file, new_file, links):
    """文の中の名指しを直し、`links` なら Markdown のリンクの行き先も直す（コードブロックとコードの範囲の外だけ）。"""
    lines = text.split("\n")
    kinds = docs_tool.line_kinds(lines)[0] if links else None
    out = []
    for i, line in enumerate(lines):
        if links and kinds[i] == docs_tool.TEXT:
            spans = docs_tool.code_spans(line)

            def fix(m):
                if any(a <= m.start() < b for a, b in spans):
                    return m.group(0)
                return m.group(0).replace(f"({m.group(1)}", f"({relink(m.group(1), old_file, new_file)}", 1)

            line = docs_tool.LINK.sub(fix, line)
        line = MENTION_RE.sub(lambda m: MENTION_TO[m.group(0)], line)
        out.append(line)
    return "\n".join(out)


def split_spec(text):
    """{経路: 字}。README は `## 2.` の前と章の一覧、章は `## N.` から（コードブロックの中は見ない）。"""
    lines = text.split("\n")
    kinds = docs_tool.line_kinds(lines)[0]
    starts = [i for i, line in enumerate(lines) if kinds[i] == docs_tool.TEXT and re.match(r"## ([2-9]|\d\d+)\. ", line)]
    numbers = [int(re.match(r"## (\d+)", lines[i]).group(1)) for i in starts]
    assert numbers == sorted(CHAPTERS), numbers
    files, rows = {}, []
    for a, b, n in zip(starts, [*starts[1:], len(lines)], numbers):
        name = f"{n:02d}-{CHAPTERS[n]}.md"
        files[f"spec/{name}"] = "\n".join(lines[a:b]) + ("\n" if b < len(lines) else "")
        rows.append(f"| §{n} | {lines[a][len(f'## {n}. '):]} | [`{name}`]({name}) |")
    head = "\n".join(lines[: starts[0]]) + "\n"
    files["spec/README.md"] = head + repo.SPEC_INDEX_HEAD + "\n\n| § | 見出し | ファイル |\n|---|---|---|\n" + "\n".join(rows) + "\n"
    return files


def cmd_docs(root, log_path):
    root = Path(root)
    here = Path(__file__).resolve().parent.relative_to(root.resolve()).as_posix() + "/"
    dirty = [l for l in git(root, "status", "--porcelain").split("\n") if l and not l[3:].startswith(here)]
    if dirty:
        sys.exit("主のツリーに未コミットの変更がある。基の状態から始める: " + "; ".join(dirty[:5]))
    spec = (root / SPEC_OLD).read_text(encoding="utf-8")
    moved = {new: (root / old).read_bytes() for old, new in MOVED.items() if old != SPEC_OLD}
    files = split_spec(spec)
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text, encoding="utf-8")
    for new, data in moved.items():
        (root / new).write_bytes(data)
    for old in MOVED:
        (root / old).unlink()  # 索引には触らない（親がコミットの前に読む）
    # 往復（経路を直す前）
    if repo.spec_text(root) != spec:
        sys.exit("往復が一致しない: spec/ をつないだ字が元の仕様と違う（経路は直していない）")
    for new, data in moved.items():
        if (root / new).read_bytes() != data:
            sys.exit(f"往復が一致しない: {new}")
    print(f"切った: README と章 {len(files) - 1}、移した: {', '.join(moved)}。往復: 一致")
    # 経路の直し: 新しいファイルは移る前の経路から、他は同じ場所から
    back = {v: k for k, v in MOVED.items()}
    log = []
    for rel in sorted(set(targets(root, "docs")) | set(files) | {"spec/tools.md"}):
        if not rel.endswith(".md") and rel != "CLAUDE.md":
            continue
        old_file = back.get(rel, SPEC_OLD if rel.startswith("spec/") and rel != "spec/tools.md" else rel)
        log += rewrite_file(root, rel, old_file, links=True)
    write_log(log_path, log)


def cmd_code(root, log_path):
    root = Path(root)
    log = []
    for rel in targets(root, "code"):
        log += rewrite_file(root, rel, rel, links=False)
    write_log(log_path, log)


def rewrite_file(root, rel, old_file, links):
    p = root / rel
    try:
        text = p.read_text(encoding="utf-8")
    except (UnicodeDecodeError, FileNotFoundError):
        return []
    new = text
    for f, a, b in MANUAL:
        if f == rel:
            assert new.count(a) == 1, (rel, a)
            new = new.replace(a, b)
    if rel == str(repo.SPEC_README):  # 章の一覧は新しく書いた字で、もとから spec/ から見た経路
        at = new.index("\n" + repo.SPEC_INDEX_HEAD + "\n") + 1
        new = rewrite_text(new[:at], old_file, rel, links) + new[at:]
    else:
        new = rewrite_text(new, old_file, rel, links)
    if new == text:
        return []
    p.write_text(new, encoding="utf-8")
    olds, news = text.split("\n"), new.split("\n")
    assert len(olds) == len(news), rel
    return [f"{rel}:{i + 1}\n- {a.strip()}\n+ {b.strip()}\n" for i, (a, b) in enumerate(zip(olds, news)) if a != b]


def write_log(path, log):
    Path(path).write_text("\n".join(log), encoding="utf-8")
    print(f"変えた行 {len(log)}（記録 {path}）")


def cmd_verify(root, base):
    root = Path(root)
    spec = git(root, "show", f"{base}:{SPEC_OLD}")
    expected = rewrite_text(spec, SPEC_OLD, "spec/README.md", links=True)
    problems = []
    if repo.spec_text(root) != expected:
        problems.append("spec/ をつないだ字が、基の仕様に経路の直しだけを当てたものと違う")
    tools = git(root, "show", f"{base}:docs/onsa-tools.md")
    if (root / "spec/tools.md").read_text(encoding="utf-8") != rewrite_text(tools, "docs/onsa-tools.md", "spec/tools.md", links=True):
        problems.append("spec/tools.md が、基のツールの仕様に経路の直しだけを当てたものと違う")
    if (root / "spec/foreign-forms.toml").read_bytes() != git(root, "show", f"{base}:docs/foreign-forms.toml").encode():
        problems.append("spec/foreign-forms.toml が基と違う")
    for old in MOVED:
        if (root / old).exists():
            problems.append(f"{old} が残っている")
    for part in ("docs", "code"):
        for rel in targets(root, part):
            try:
                text = (root / rel).read_text(encoding="utf-8")
            except (UnicodeDecodeError, FileNotFoundError):
                continue
            for i, line in enumerate(text.split("\n")):
                if MENTION_RE.search(line):
                    problems.append(f"{rel}:{i + 1}: 古い経路が残っている: {line.strip()[:120]}")
    print("\n".join(problems) if problems else "verify: 一致、古い経路は残っていない")
    return 1 if problems else 0


if __name__ == "__main__":
    cmd, root, arg = sys.argv[1], sys.argv[2], sys.argv[3]
    if cmd == "docs":
        cmd_docs(root, arg)
    elif cmd == "code":
        cmd_code(root, arg)
    elif cmd == "verify":
        sys.exit(cmd_verify(root, arg))
    else:
        sys.exit(f"知らないコマンド: {cmd}")
