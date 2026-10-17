#!/usr/bin/env python3
"""X-2 移行の段 (5c) の、利用者の文書と X の材料を `issues/X/` へ移す親の道具（持ち越しの振り分けの前に回す）。

    python3 -B migrate_5c.py x <リポジトリ> <X の README> <記録>   # X-1・X-2、材料、README、経路の直し（onsa-docs）
    python3 -B migrate_5c.py verify <リポジトリ> <基のコミット>     # X の本文と材料が基と一致する
    python3 -B migrate_5c.py carry <リポジトリ> <行き先の表> <記録>   # 持ち越しを行の範囲で宛先へ、新しいファイル、経路（onsa-docs）
    python3 -B migrate_5c.py verify-carry <リポジトリ> <前の木> <行き先の表>   # 動かした行が宛先に一度ずつ、元の順に

- X: `docs/process_improvement_after_w3.md` の章 `# <n>. <題>` ごとに、頭の欄（`status`）、見出し `# X-<n> <題>`、章の本文（字を
  変えずに。章の末尾の空行だけ一つにする）、親の「決めたこと」の箇条を `issues/X/X-<n>.md` へ。元の文書は消す。
- 材料: `docs/process_improvement_after_w3/x<n>/` を、中の配置を変えずに `issues/X/X-<n>/` へ（木が git なら `git mv`）。
- 経路の直し: EDITS の一意一致置換で、今も読む経路だけ（報告 `adv/` と、移す前の場所を述べる字は直さない）。
  書く前に全ての一致を確かめ、どれかが一つに一致しなければ何も書かずに止まる。
- 持ち越し（`x` の後）: 行き先の表の `part`（基の `docs/carryovers.md` の行の範囲と宛先）で、単位（最上位の太字の箇条）の行を
  一度ずつ宛先へ動かし、`docs/carryovers.md` を消す。範囲は一つの単位の中にあり、全ての単位の行を一度ずつ覆う（頭の約束の行は
  文書と一緒に消える）。宛先: ID は LABELS のラベルの下へ（`migrate_carryovers.put` と同じ置き方。単位の頭の行を含まない範囲は、
  元の太字の頭 `- **…**` を写した下に、範囲の最初の行が一段下になるよう字下げをずらして置く）、`tasks/phase2.md` は末尾にそのまま、
  `drop` は消す。新しい宛先（NEW_FILES）は動かす前に作る。書く前に全てを確かめ、どれかが通らなければ何も書かない。
どれも対象のファイルを一度ずつ読む一回の走査（字の数に線形）で、繰り返しは無い。
"""
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path
from types import SimpleNamespace

TOOLS = Path(__file__).resolve().parents[4] / "tools"
sys.path.insert(0, str(TOOLS))
import docs as docs_tool  # noqa: E402
import repo  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import migrate_carryovers as mc  # noqa: E402

USER_DOC = "docs/process_improvement_after_w3.md"
OLD_DIR = "docs/process_improvement_after_w3"
X_DIR = "issues/X"
CHAPTER = re.compile(r"# (\d+)\. (.+)")
# the parent's text (the user's approval: 37 回目)
X_FILES = {
    1: ("DOING", [  # the check of the effect at the start of W4 is left
        "- 決めたこと（手順 2、2026-10-16）: gate とファズの基準 GF-1〜GF-4 を、ひとまずの基準にする（`X-1/step2_criteria.md`）。"
        "材料は手順 1 の実績 `X-1/step1_eval.md`。",
        "- 決めたこと（手順 3、2026-10-16）: 改善策 M-1〜M-8、単位 U1・U2 と値（`X-1/step3_measures.md` の「決定と効果の確かめ方」）。"
        "実装は `9329e97`・`b0a2739`。",
    ]),
    2: ("DOING", [
        "- 決めたこと（手順 2、2026-10-16）: 文書の構造 DS-1〜DS-10（`X-2/step2_structure.md`）。材料は手順 1 の洗い出し `X-2/step1_eval.md`。",
        "- 決めたこと（手順 3、2026-10-16）: 文書ごとの形 DF-1〜DF-10（`X-2/step3_format.md`）。",
        "- 決めたこと（手順 4、2026-10-16）: 道具 DT-0〜DT-10 と単位 U1〜U3（`X-2/step4_tools.md`）。",
        "- 決めたこと（手順 5、2026-10-16）: 管理の担当 `onsa-docs`（DM の項目、`X-2/step5_manager.md`）。",
        "- 決めたこと（手順 6、2026-10-16）: 移行の計画 MG-A〜MG-H（`X-2/step6_migration.md`。35・36 回目の改めは頭の決定の行）。",
    ]),
}
OLD, NEW = f"{OLD_DIR}/x1/", "issues/X/X-1/"
OLD2, NEW2 = f"{OLD_DIR}/x2/", "issues/X/X-2/"
EDITS = {  # by the paths before the move
    "docs/carryovers.md": [
        (f"（`{OLD2}step5_manager.md`。", f"（`{NEW2}step5_manager.md`。"),
        (f"（`{OLD}tools/` の `gate_runs.py`", f"（`{NEW}tools/` の `gate_runs.py`"),
        (f"（`{OLD2}tools/doc_usage.py`）", f"（`{NEW2}tools/doc_usage.py`）"),
        (f"材料は `{OLD}step1_eval.md`。", f"材料は `{NEW}step1_eval.md`。"),
        (f"（`{OLD2}step6_migration.md` の頭）", f"（`{NEW2}step6_migration.md` の頭）"),
        # the numbers inside the reports spelled as IDs (`docs.py check` reads them as R-2 …): the hyphen out
        # and 指摘 before (the user's I-5, 2026-10-17, as `migrate_rf.py`); R-3, R-4, R-6 are W3-21/b's too
        ("  - W3-21/b の R-2（", "  - W3-21/b の指摘 R2（"),
        ("  - R-3（検出の入口", "  - 指摘 R3（検出の入口"),
        ("  - R-4（`interpolated`", "  - 指摘 R4（`interpolated`"),
        ("  - R-6（`Why::Differ`", "  - 指摘 R6（`Why::Differ`"),
        ("  - W3-09/b の S-1 の 6（", "  - W3-09/b の指摘 S1 の 6（"),
    ],
    f"{OLD2}step3_format.md": [(f"（`{OLD2}step2_structure.md`、", f"（`{NEW2}step2_structure.md`、")],
    f"{OLD2}tools/test_migrate_carryovers.py": [(f"python3 -B {OLD2}tools/", f"python3 -B {NEW2}tools/")],
    f"{OLD2}tools/test_migrate_tables.py": [(f"python3 -B {OLD2}tools/", f"python3 -B {NEW2}tools/")],
}


CARRY = "docs/carryovers.md"
LABELS = {"W": "持ち越し", "X": "持ち越し", "RF": "内容", "S": "空白"}
PHASE2 = "tasks/phase2.md"
DROP = "drop"
# the destinations made before the move (the parent's text, 37 回目): their text before the moved lines
NEW_FILES = {
    **{f"issues/X/X-{n}.md": ("OPEN", f"X-{n} {title}") for n, title in (
        (3, "修正候補の約束を一段弱める案と、空白を規則の族ごとに決める案"),
        (4, "線形の時間の gate の項目と、allowed の `left` の一般の文面"),
        (5, "W3-13 の残り"),
        (6, "リファクタリング RF-5〜RF-14"),
        (7, "イベントのクロックと停止・再開・初期化の設計"),
        (8, "W4 の見積もりと範囲と単位の分け"),
        (9, "ツール化の候補と規則の読み飛ばし"),
        (10, "トークン効率化対策"),
    )},
    "issues/RF/RF-17.md": ("OPEN", "RF-17 手順の計画を API と C の写しに分ける（WASM の前、M6）"),
    "decisions/S/S-552.md": ("OPEN", "S-552"),
}
PHASE2_TEXT = "# 第 2 期の持ち越し\n\n第 2 期の作業を作るときに、各作業の `持ち越し` へ移す。\n"
CARRY_EDITS = {
    "rules/leader.md": [
        ("（改めた文書の記録は §5）。作業の持ち越し `docs/carryovers.md`。\n", "（改めた文書の記録は §5）。\n"),
        ("- 問題 `issues/R/`（R）とリファクタリング `issues/RF/`（RF）。",
         "- 問題 `issues/R/`（R）、リファクタリング `issues/RF/`（RF）、改善の項目 `issues/X/`（X）。"),
    ],
    "decisions/README.md": [("（`docs/carryovers.md` の「決定の関係の表し方」）", "（X-2 の `持ち越し` の「決定の関係の表し方」）")],
    "tasks/README.md": [("- `stages.md` には段の目的と前提だけを書き、作業ごとの細部は各 W に書く。\n",
                         "- `stages.md` には段の目的と前提だけを書き、作業ごとの細部は各 W に書く。\n"
                         "- 第 2 期の作業の持ち越しは、作業ができるまで [`phase2.md`](phase2.md) に置く。\n")],
}


def new_text(rel):
    """The text of a destination made before the move: the head, its heading and a blank line."""
    if rel == PHASE2:
        return PHASE2_TEXT + "\n"
    status, heading = NEW_FILES[rel]
    return docs_tool.render_head({"status": status}, ["status"]) + f"# {heading}\n\n"


def indent(line):
    return len(line) - len(line.lstrip(" "))


def read_parts(path, lines):
    """[(unit, first, last, to)] (0-based, inclusive) in the order of the lines; every line of every unit once."""
    units = mc.read_units(lines)
    owner = {i: u for u in units for i in range(u.at, u.at + len(u.lines))}
    parts, seen = [], set()
    for p in tomllib.loads(Path(path).read_text(encoding="utf-8"))["part"]:
        a, b = p["lines"][0] - 1, p["lines"][1] - 1
        u = owner.get(a)
        if u is None or owner.get(b) is not u or b < a or seen & set(range(a, b + 1)):
            raise SystemExit(f"{path}: lines {a + 1}-{b + 1}: not within one unit, or a line twice; nothing written")
        seen |= set(range(a, b + 1))
        parts.append((u, a, b, p["to"]))
    if seen != set(owner):
        raise SystemExit(f"{path}: the lines of the units not in a part: {sorted(i + 1 for i in set(owner) - seen)[:10]}")
    return sorted(parts, key=lambda p: p[1])


def moved_lines(lines, part):
    """The lines of a part as they go under a label, before `put` puts them two spaces in."""
    u, a, b, _ = part
    if a == u.at:
        return list(lines[a : b + 1])
    shift = 2 - indent(lines[a])
    if any(indent(x) + shift < 0 for x in lines[a : b + 1]):
        raise SystemExit(f"{CARRY}:{a + 1}-{b + 1}: a line less indented than the first; nothing written")
    return [f"- **{mc.BOLD.match(lines[u.at]).group(1)}**"] + [" " * (indent(x) + shift) + x.lstrip(" ") for x in lines[a : b + 1]]


def dest_rel(to):
    return Path(PHASE2) if to == PHASE2 else repo.path_of(to)


def carry_plan(root, path):
    """({rel: the text after}, the log): reads everything first, writes nothing."""
    lines = (root / CARRY).read_text(encoding="utf-8").split("\n")
    parts = read_parts(path, lines)
    by, log = {}, []
    for part in parts:
        to = part[3]
        if to == DROP:
            log.append(f"drop {CARRY}:{part[1] + 1}-{part[2] + 1}")
            continue
        by.setdefault(to, []).append(part)
    texts = {}
    for to, ps in by.items():
        rel = dest_rel(to).as_posix()
        made = rel in NEW_FILES or rel == PHASE2
        if made == (root / rel).exists():
            raise SystemExit(f"{rel}: {'there already' if made else 'not there'}; nothing written")
        text = new_text(rel) if made else (root / rel).read_text(encoding="utf-8")
        if rel == PHASE2:
            texts[rel] = text + "\n".join(x for p in ps for x in moved_lines(lines, p)) + "\n"
        else:
            units = [SimpleNamespace(lines=tuple(moved_lines(lines, p))) for p in ps]
            texts[rel] = mc.put(text, LABELS[repo.kind_of(to).name], units)
        log += [f"{CARRY}:{p[1] + 1}-{p[2] + 1} -> {rel}" + (" (new)" if made else "") for p in ps]
    for rel, pairs in CARRY_EDITS.items():
        t = texts.get(rel) or (root / rel).read_text(encoding="utf-8")
        for old, new in pairs:
            if t.count(old) != 1:
                raise SystemExit(f"{rel}: {t.count(old)} match(es) of {old[:50]!r}; nothing written")
            t = t.replace(old, new)
            log.append(f"{rel}: {old.strip()!r} -> {new.strip()!r}")
        texts[rel] = t
    return texts, log


def cmd_carry(root, path, log_path):
    texts, log = carry_plan(root, path)
    swaps = [s for rel in [CARRY, *texts] for s in docs_tool.swap_files_of(root / rel)]
    if swaps:
        raise SystemExit(f"a vim swap file: {swaps[0]}; nothing written")
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    (root / CARRY).unlink()  # changed by `x`'s paths: not `git rm`
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_5c carry: {sum(' -> ' in x and x.startswith(CARRY) for x in log)} part(s) to "
          f"{len(texts) - len(CARRY_EDITS)} file(s), {sum(x.startswith('drop') for x in log)} dropped, {CARRY} removed; log {log_path}")


def cmd_verify_carry(root, before, path):
    """Each destination is the one before (or NEW_FILES' text) with one block put in at one place, under its
    label: the parts' lines in order, two spaces in (a part without the unit's head: under the copied bold head,
    the first line four in); CARRY_EDITS' files the ones before with the edits; the document gone."""
    lines = (before / CARRY).read_text(encoding="utf-8").split("\n")
    parts = read_parts(path, lines)
    bad = [CARRY] if (root / CARRY).exists() else []
    by = {}
    for part in parts:
        if part[3] != DROP:
            by.setdefault(part[3], []).append(part)
    for to, ps in by.items():
        rel = dest_rel(to).as_posix()
        made = rel in NEW_FILES or rel == PHASE2
        old = (new_text(rel) if made else (before / rel).read_text(encoding="utf-8")).split("\n")
        new = (root / rel).read_text(encoding="utf-8").split("\n")
        block = []
        for u, a, b, _ in ps:
            pad = "" if rel == PHASE2 else "  "
            if a == u.at:
                block += [pad + x for x in lines[a : b + 1]]
            else:
                head = mc.BOLD.match(lines[u.at]).group(0)
                block += [pad + head] + [pad + " " * (indent(x) - indent(lines[a]) + 2) + x.lstrip(" ") for x in lines[a : b + 1]]
        if rel != PHASE2 and not any(mc.label_re(LABELS[repo.kind_of(to).name]).match(x) for x in old):
            block = [f"- {LABELS[repo.kind_of(to).name]}:"] + block
        # one place: a common head and tail around the block (the head and the tail found once each: linear)
        head = next((i for i, (x, y) in enumerate(zip(old, new)) if x != y), min(len(old), len(new)))
        tail = next((i for i, (x, y) in enumerate(zip(reversed(old), reversed(new))) if x != y), min(len(old), len(new)))
        at = len(old) - tail
        if not (len(new) == len(old) + len(block) and at <= head and new[at : at + len(block)] == block):
            bad.append(rel)
    for rel, pairs in CARRY_EDITS.items():
        t = (before / rel).read_text(encoding="utf-8")
        for o, w in pairs:
            t = t.replace(o, w)
        if rel not in {dest_rel(to).as_posix() for to in by} and (root / rel).read_text(encoding="utf-8") != t:
            bad.append(rel)
    n = sum(b - a + 1 for _, a, b, to in parts if to != DROP)
    print("migrate_5c verify-carry: " + (f"differs in {', '.join(bad)}" if bad else
          f"the same: {n} line(s) of {len(parts)} part(s) in {len(by)} file(s), "
          f"{sum(to == DROP for *_, to in parts)} part(s) dropped, the edits, {CARRY} gone"))
    return 1 if bad else 0


def chapters(text):
    """[(n, title, body)]: the body is the lines after the heading, its trailing blank lines made one end."""
    lines = text.split("\n")
    starts = [i for i, line in enumerate(lines) if CHAPTER.fullmatch(line)]
    if not starts or starts[0] != 0 or [int(CHAPTER.fullmatch(lines[i]).group(1)) for i in starts] != list(X_FILES):
        raise SystemExit(f"{USER_DOC}: not the chapters {list(X_FILES)} from the first line; nothing written")
    out = []
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        m = CHAPTER.fullmatch(lines[i])
        out.append((int(m.group(1)), m.group(2), "\n".join(lines[i + 1 : j]).rstrip("\n") + "\n"))
    return out


def x_text(n, title, body):
    status, decided = X_FILES[n]
    head = docs_tool.render_head({"status": status}, ["status"])  # the one field of the X README
    return head + f"# X-{n} {title}\n" + body + "\n" + "\n".join(decided) + "\n"


def cmd_x(root, readme, log_path):
    if (root / X_DIR).exists() or not (root / USER_DOC).is_file():
        raise SystemExit(f"migrate_5c x: {X_DIR} is there or {USER_DOC} is not; nothing written")
    parts = chapters((root / USER_DOC).read_text(encoding="utf-8"))
    texts, log = {}, []
    for rel, pairs in EDITS.items():  # every match checked before anything is written
        t = (root / rel).read_text(encoding="utf-8")
        for old, new in pairs:
            if t.count(old) != 1:
                raise SystemExit(f"{rel}: {t.count(old)} match(es) of {old[:50]!r}; nothing written")
            t = t.replace(old, new)
            log.append(f"{rel}: {old!r} -> {new!r}")
        texts[rel] = t
    for rel, t in texts.items():
        (root / rel).write_text(t, encoding="utf-8")
    (root / X_DIR).mkdir(parents=True)
    (root / X_DIR / "README.md").write_text(Path(readme).read_text(encoding="utf-8"), encoding="utf-8")
    for n, title, body in parts:
        (root / X_DIR / f"X-{n}.md").write_text(x_text(n, title, body), encoding="utf-8")
        log.append(f"{X_DIR}/X-{n}.md: chapter {n} of {USER_DOC}")
    git = (root / ".git").exists()
    for n in X_FILES:
        src, dst = f"{OLD_DIR}/x{n}", f"{X_DIR}/X-{n}"
        if git:
            subprocess.run(["git", "-C", str(root), "mv", src, dst], check=True)
        else:
            shutil.move(str(root / src), str(root / dst))
        log.append(f"{src}/ -> {dst}/")
    if git:
        subprocess.run(["git", "-C", str(root), "rm", "-q", USER_DOC], check=True)
    else:
        (root / USER_DOC).unlink()
    left = [p for p in (root / OLD_DIR).rglob("*") if p.is_file()]
    if left:
        raise SystemExit(f"migrate_5c x: {OLD_DIR} still has {left[0]} (not tracked?); left as it is")
    shutil.rmtree(root / OLD_DIR)
    Path(log_path).write_text("\n".join(log) + "\n", encoding="utf-8")
    print(f"migrate_5c x: X-1, X-2 and their materials in {X_DIR}/, {len(EDITS)} file(s) of paths; log {log_path}")


def cmd_verify(root, base):
    def show(rel):
        return subprocess.run(["git", "-C", str(root), "show", f"{base}:{rel}"], capture_output=True, text=True, check=True).stdout

    bad = []
    for n, title, body in chapters(show(USER_DOC)):
        rel = f"{X_DIR}/X-{n}.md"
        if (root / rel).read_text(encoding="utf-8") != x_text(n, title, body):
            bad.append(rel)
    names = subprocess.run(["git", "-C", str(root), "ls-tree", "-r", "--name-only", base, OLD_DIR + "/"],
                           capture_output=True, text=True, check=True).stdout.split()
    edits = {rel: pairs for rel, pairs in EDITS.items() if rel.startswith(OLD_DIR + "/")}
    moved = 0
    for old in names:
        if old == USER_DOC:
            continue
        new = re.sub(rf"^{OLD_DIR}/x(\d+)/", lambda m: f"{X_DIR}/X-{m.group(1)}/", old)
        raw = subprocess.run(["git", "-C", str(root), "show", f"{base}:{old}"], capture_output=True, check=True).stdout
        want = raw
        for o, w in edits.get(old, []):
            want = want.replace(o.encode(), w.encode())
        if not (root / new).is_file() or (root / new).read_bytes() != want:
            bad.append(new)
        moved += 1
    if (root / OLD_DIR).exists():
        bad.append(OLD_DIR)
    print("migrate_5c verify: " + (f"differs in {', '.join(bad)}" if bad
          else f"X-1, X-2 the same as the chapters of {base}; {moved} material file(s) the same but the edits"))
    return 1 if bad else 0


def main(argv):
    if len(argv) == 4 and argv[0] == "x":
        cmd_x(Path(argv[1]), argv[2], argv[3])
    elif len(argv) == 3 and argv[0] == "verify":
        return cmd_verify(Path(argv[1]), argv[2])
    elif len(argv) == 4 and argv[0] == "carry":
        cmd_carry(Path(argv[1]), argv[2], argv[3])
    elif len(argv) == 4 and argv[0] == "verify-carry":
        return cmd_verify_carry(Path(argv[1]), Path(argv[2]), argv[3])
    else:
        raise SystemExit(__doc__)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
