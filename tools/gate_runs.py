"""What the gate keeps in the main tree across runs (X-1): its history and the base binaries.

The history, `target/gate/history.jsonl`: one JSON line per gate run in the main tree
(`repo.tree_kind`; not `--quick`): `time`, `commit` (the full SHA of HEAD), `dirty` (`git
status --porcelain` shows something), `form` (`whole`, `stage-end W3`, `work W3-13`, `sweep 0/2`,
`only fuzz,static`), `works`, `verdict`, `seconds` (the sum of the items, without the wait for
the lock) and `items` ({name: [status, seconds]}). The next shard of a sweep follows the last
sweep of the same K (`next_shard`); a run that stopped half way writes no line, so its shard
runs again. A worktree keeps no history: its runs go with it.

The base binaries (`save_base`, `tools/gate.sh --save-base`, the first item of a sweep): the
`onsa` and `onsa_cases` of HEAD, built, in `narrowing.base_dir` with `COMMIT`, for the narrowed
fuzzing of the works after it (`narrowing.resolve_base`). Only in the main tree, and only when
the tracked files of what builds them have no change (`narrowing.code_changes`).
"""
import json
import os
import re
import shutil
import time
from pathlib import Path

import narrowing
import repo

HISTORY = Path("target") / "gate" / "history.jsonl"
BASE_NAME = re.compile(r"[0-9a-f]{%d}" % narrowing.SHORT)


def read_history(root):
    """(the rows, the count of lines that are not a JSON object); raises OSError when the
    file is there and cannot be read."""
    try:
        text = (Path(root) / HISTORY).read_text(encoding="utf-8")
    except FileNotFoundError:
        return [], 0
    rows, bad = [], 0
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except ValueError:
            row = None
        if isinstance(row, dict):
            rows.append(row)
        else:
            bad += 1
    return rows, bad


def record(root, form, works, items, verdict, seconds):
    """Add the line of a run; the reason it cannot (a str), or None."""
    try:
        row = {
            "time": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            "commit": narrowing.git(root, "rev-parse", "HEAD").strip(),
            "dirty": bool(narrowing.git(root, "status", "--porcelain").strip()),
            "form": form, "works": list(works), "verdict": verdict, "seconds": round(seconds, 1), "items": items,
        }  # fmt: skip
        path = Path(root) / HISTORY
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except (OSError, narrowing.NarrowError) as e:
        return str(e)
    return None


def _sweeps(rows, k):
    """[(shard, row)] of the sweeps of `k` shards, in their order."""
    out = []
    for row in rows:
        m = re.fullmatch(r"sweep (\d+)/(\d+)", str(row.get("form", "")))
        if m and int(m.group(2)) == k and int(m.group(1)) < k:
            out.append((int(m.group(1)), row))
    return out


def next_shard(rows, k):
    """The shard the next sweep runs: the one after the last sweep of `k` shards, else 0."""
    sweeps = _sweeps(rows, k)
    return (sweeps[-1][0] + 1) % k if sweeps else 0


def sweep_line(root, rows, bad, k):
    """`sweep: next 1/2 (0/2 last at 628f8ec, 3 commits ago; 1/2 never)`."""
    last = dict(_sweeps(rows, k))
    parts = []
    for i in range(k):
        row = last.get(i)
        if row is None:
            parts.append(f"{i}/{k} never")
            continue
        commit = str(row.get("commit", ""))
        try:
            narrowing.git(root, "merge-base", "--is-ancestor", commit, "HEAD")
            ago = int(narrowing.git(root, "rev-list", "--count", f"{commit}..HEAD").strip())
            when = f"{ago} commit{'' if ago == 1 else 's'} ago"
        except (narrowing.NarrowError, ValueError):
            when = "not an ancestor of HEAD"
        parts.append(f"{i}/{k} last at {commit[:narrowing.SHORT]}, {when}")
    tail = f"; {bad} unreadable line{'' if bad == 1 else 's'} in {HISTORY}" if bad else ""
    return f"sweep: next {next_shard(rows, k)}/{k} ({'; '.join(parts)}){tail}"


def save_base(root, keep, out=print, build=None, target_directory=None):
    """Copy the binaries of HEAD into `target/base/<SHA>`, keep the last `keep`. The exit:
    0 saved, 1 refused or failed, 2 not the main tree."""
    if build is None or target_directory is None:
        import fuzz  # the same builds and target directory as the fuzzing

        build, target_directory = build or fuzz.build, target_directory or fuzz.target_directory
    root = Path(root)
    if repo.tree_kind(root) != "main":
        out(f"save-base: {root} is not the main tree; the base binaries are the parent's (X-1 M-3)")
        return 2
    try:
        changed = narrowing.code_changes(root)
        full = narrowing.git(root, "rev-parse", "HEAD").strip()
    except narrowing.NarrowError as e:
        out(f"save-base: {e}")
        return 1
    if changed:
        out(f"save-base: refused: the tracked files have changes not committed: {' '.join(changed)}")
        return 1
    target = target_directory(root)
    if target is None or not build(root) or not build(root, cases=True):
        out("save-base: cannot build onsa and onsa_cases (cargo build; cargo metadata)")
        return 1
    dest = narrowing.base_dir(root, full)
    tmp = dest.parent / f".tmp-{os.getpid()}"
    try:
        shutil.rmtree(tmp, ignore_errors=True)
        tmp.mkdir(parents=True)
        for name in narrowing.BASE_FILES:
            shutil.copy2(Path(target) / "debug" / name, tmp / name)
        (tmp / "COMMIT").write_text(full + "\n", encoding="utf-8")
        if dest.exists():
            shutil.rmtree(dest)
        tmp.rename(dest)
        removed = _prune(dest.parent, keep)
    except OSError as e:
        shutil.rmtree(tmp, ignore_errors=True)
        out(f"save-base: cannot copy the binaries: {e}")
        return 1
    out(f"save-base: {dest} ({full}); removed: {' '.join(removed) or 'none'}")
    return 0


def _prune(base, keep):
    """Remove the oldest saved bases (by the time of their COMMIT) past `keep`; nothing else."""
    saved = [d for d in base.iterdir() if d.is_dir() and BASE_NAME.fullmatch(d.name) and (d / "COMMIT").is_file()]
    saved.sort(key=lambda d: ((d / "COMMIT").stat().st_mtime, d.name))
    gone = saved[: max(len(saved) - keep, 0)]
    for d in gone:
        shutil.rmtree(d)
    return [d.name for d in gone]
