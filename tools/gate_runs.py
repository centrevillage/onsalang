"""What the gate keeps across runs (X-1): its history, the base binaries and the auto sweep.

The history, `target/gate/history.jsonl` of each tree: one JSON line per gate run in a git tree
(`repo.tree_kind`; in the main tree not `--quick`, in a worktree every form): `time`, `commit` (the full SHA of HEAD), `dirty` (`git
status --porcelain` shows something), `form` (`whole`, `stage-end W3`, `work W3-13`, `sweep 0/2`,
`only fuzz,static`, `quick`), `works`, `verdict`, `seconds` (the sum of the items, without the wait
for the lock), `items` ({name: [status, seconds]}), `tree` (the git tree the items read,
`repo.tree_hash`: the whole of a worktree, `narrowing.SWEPT` of the main tree; null when it changed
while they ran or cannot be made), in a worktree `code_tree` (the hash of its `narrowing.SWEPT`,
null with `tree`: `tools/take.py patch` tells a change of the documents after the check from one of
the code and the cases, X-1 U5) and `tree_changed`. The next shard of a sweep follows the last
sweep of the same K (`next_shard`); a run that stopped half way writes no line, so its shard
runs again. A whole run (`whole`, `stage-end …`) of a clean tree counts as every shard, and a run
whose tree changed counts as none (`_sweeps`). A worktree keeps its own history, `--quick` too, for `tools/take.py patch` (X-1 U3);
it goes with the worktree.

The base binaries (`save_base`, `tools/gate.sh --save-base`, the first item of a sweep): the
`onsa` and `onsa_cases` of HEAD, built, in `narrowing.base_dir` with `COMMIT`, for the narrowed
fuzzing of the works after it (`narrowing.resolve_base`). Only in the main tree, and only when
the tracked files of what builds them have no change (`narrowing.code_changes`); a whole run
of the main tree saves them at its end too (`tools/gate.py`).

The auto sweep (`tools/after_commit.py`, X-1 U4) in `target/gate/auto/`: `request` (the last
commit of the code or the cases: `time`, `commit`, `now`), `state` (what the runner does: `time`,
`state` waiting / waiting-clean / held / skipped / running / done, and its fields), `lock` (held
by the runner while it lives), `request.lock` (short: every read and write of `request` and every
try of `lock` are made under it, so a request is never left with no runner told), `job/` (bg.py)
and `runs/` (the output of the last RUNS_KEPT sweeps). `target/gate/hold` stops it. `auto_line`
is the line `auto sweep: …` of the gate's summary and of `take.py patch`; it starts with `hook not
set` when `core.hooksPath` does not name `HOOKS` (`hook_set`; the setting is the clone's, X-1 U5).
"""
import contextlib
import datetime
import fcntl
import json
import os
import re
import shutil
import time
from pathlib import Path

import narrowing
import repo

HISTORY = Path("target") / "gate" / "history.jsonl"
AUTO = Path("target") / "gate" / "auto"
HOLD = Path("target") / "gate" / "hold"
HOOKS = Path("tools") / "hooks"
RUNS_KEPT = 10
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


def at_start(root):
    """`commit` and `dirty` of the row of a run, taken before its items run: a commit made meanwhile
    is not what the run checked (X-1 U4). Raises NarrowError when git fails."""
    return {"commit": narrowing.git(root, "rev-parse", "HEAD").strip(),
            "dirty": bool(narrowing.git(root, "status", "--porcelain").strip())}  # fmt: skip


def record(root, form, works, items, verdict, seconds, tree=None, tree_changed=False, start=None, code_tree=None):
    """Add the line of a run (`start`: `at_start` before the items; else taken now; `code_tree` in a
    worktree only); the reason it cannot (a str), or None."""
    try:
        row = {
            "time": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            **(start or at_start(root)),
            "form": form, "works": list(works), "verdict": verdict, "seconds": round(seconds, 1), "items": items,
            "tree": None if tree_changed else tree, "tree_changed": tree_changed,
        }  # fmt: skip
        if code_tree is not None:
            row["code_tree"] = None if tree_changed else code_tree
        path = Path(root) / HISTORY
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except (OSError, narrowing.NarrowError) as e:
        return str(e)
    return None


def whole_form(form):
    """`form` (a `form` of the history) runs every item whole."""
    return form == "whole" or form.startswith("stage-end ")


def whole_run(row):
    """A row of a whole run that counts as every shard: a clean tree that did not change meanwhile."""
    return whole_form(str(row.get("form", ""))) and not row.get("dirty") and not row.get("tree_changed")


def epoch(row):
    """The `time` of a row in seconds (0 when it is not of the form)."""
    try:
        return datetime.datetime.strptime(str(row.get("time")), "%Y-%m-%dT%H:%M:%S%z").timestamp()
    except ValueError:
        return 0.0


def _sweeps(rows, k):
    """[(shard, row)] of the sweeps of `k` shards and the whole runs (every shard), in their order."""
    out = []
    for row in rows:
        m = re.fullmatch(r"sweep (\d+)/(\d+)", str(row.get("form", "")))
        if row.get("tree_changed"):
            continue
        if m and int(m.group(2)) == k and int(m.group(1)) < k:
            out.append((int(m.group(1)), row))
        elif whole_run(row):
            out += [(i, row) for i in range(k)]
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
        parts.append(f"{i}/{k} last at {commit[:narrowing.SHORT]}, {_ago(root, commit)}")
    tail = f"; {bad} unreadable line{'' if bad == 1 else 's'} in {HISTORY}" if bad else ""
    return f"sweep: next {next_shard(rows, k)}/{k} ({'; '.join(parts)}){tail}"


def _ago(root, commit):
    try:
        narrowing.git(root, "merge-base", "--is-ancestor", commit, "HEAD")
        ago = int(narrowing.git(root, "rev-list", "--count", f"{commit}..HEAD").strip())
    except (narrowing.NarrowError, ValueError):
        return "not an ancestor of HEAD"
    return f"{ago} commit{'' if ago == 1 else 's'} ago"


@contextlib.contextmanager
def request_lock(root):
    """The short lock of the auto sweep (the docstring): wait for it, hold it a moment."""
    path = Path(root) / AUTO / "request.lock"
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a", encoding="utf-8") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        yield


def try_runner(root):
    """Under `request_lock`: the runner's lock, taken (an open file: closing it lets it go), or None
    when a runner holds it. The system lets it go when the process ends, however it ends."""
    f = open(Path(root) / AUTO / "lock", "a", encoding="utf-8")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        f.close()
        return None
    return f


def read_json(root, name):
    """The JSON of `target/gate/auto/<name>`: None when it is not there, {} when it is not an object."""
    try:
        value = json.loads((Path(root) / AUTO / name).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except (OSError, ValueError):
        return {}
    return value if isinstance(value, dict) else {}


def write_json(root, name, value):
    path = Path(root) / AUTO / name
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{name}.tmp")
    tmp.write_text(json.dumps(value) + "\n", encoding="utf-8")
    tmp.replace(path)


def _clock(t):
    return time.strftime("%m-%d %H:%M:%S", time.localtime(t)) if isinstance(t, (int, float)) else "?"


def hook_set(root):
    """`core.hooksPath` names the tree's `HOOKS` (relative or not); False when git cannot read it."""
    try:
        path = narrowing.git(root, "config", "--get", "core.hooksPath").strip()
    except narrowing.NarrowError:
        return False
    return bool(path) and (Path(root) / path).resolve() == (Path(root) / HOOKS).resolve()


def auto_line(root, rows, k):
    """`auto sweep: <what the runner does>; <the outcome of the sweeps>` (X-1 U4): the part of now
    from the hold, the request, the runner's lock and its state; the outcome from the last row of
    each shard (`_sweeps`; one shard's failure stays until that shard passes)."""
    root, live = Path(root), [] if hook_set(root) else [f"hook not set (git config core.hooksPath {HOOKS})"]
    short = lambda c: str(c or "?")[:narrowing.SHORT]  # noqa: E731
    req, runner = None, None
    if (root / AUTO).is_dir():  # nothing written before the first commit of the code
        with request_lock(root):
            runner = try_runner(root)
            if runner is not None:
                runner.close()
            req = read_json(root, "request")
    state, now = read_json(root, "state") or {}, "tools/after_commit.py --now"
    if (root / HOLD).exists():
        at = f", request at {short(req.get('commit'))}" if req is not None else ""
        live.append(f"held since {_clock((root / HOLD).stat().st_mtime)}{at} (remove {HOLD}, then {now})")
    elif (root / AUTO).is_dir() and runner is None:
        s = state.get("state")
        live.append(f"waiting (quiet until {_clock(state.get('until'))})" if s == "waiting" else
                    f"waiting for a clean tree (uncommitted {state.get('path')}, until {_clock(state.get('until'))})"
                    if s == "waiting-clean" else
                    f"running at {short(state.get('commit'))} since {_clock(state.get('time'))}" if s == "running"
                    else "the runner is on")  # fmt: skip
    elif req is not None:
        if state.get("state") == "skipped" and state.get("time", 0) >= req.get("time", 0):
            live.append(f"skipped at {short(state.get('commit'))}: uncommitted {state.get('path')} ({now})")
        else:
            live.append(f"requested at {short(req.get('commit'))} {_clock(req.get('time'))}, no runner "
                        f"({AUTO / 'job' / 'out'}; {now})")  # fmt: skip
    elif state.get("state") == "done" and state.get("code") not in (0, 1):
        live.append(f"gate exit {state.get('code')} at {short(state.get('commit'))} ({state.get('out')})")
    last, order = dict(_sweeps(rows, k)), {id(r): i for i, r in enumerate(rows)}
    if not last:
        return "auto sweep: " + "; ".join(live + ["no sweep yet"])
    failed = sorted((r for r in last.values() if r.get("verdict") != "PASS"), key=lambda r: order[id(r)])
    if failed:
        r, commit = failed[-1], str(failed[-1].get("commit", ""))
        items = ", ".join(n for n, v in r.get("items", {}).items() if v[:1] == ["FAIL"])
        outs = sorted((root / AUTO / "runs").glob(f"*-{commit[:narrowing.SHORT]}.out"))
        live.append(f"FAILED at {short(commit)}: {items} ({outs[-1] if outs else 'no output kept'})")
    else:
        r = max(last.values(), key=lambda r: order[id(r)])
        live.append(f"last PASS at {short(r.get('commit'))} ({_ago(root, str(r.get('commit', '')))})")
    return "auto sweep: " + "; ".join(live)


def debug_dir_warning(target, limit):
    """The warning when `<target>/debug` takes more than `limit` bytes on the disk, else None. Cargo
    does not remove the outputs of the builds before; `cargo clean --profile dev` does."""
    debug = Path(target) / "debug"
    size = 0
    for dirpath, _, names in os.walk(debug):
        for name in names:
            try:
                size += os.lstat(os.path.join(dirpath, name)).st_blocks * 512
            except OSError:
                continue  # removed meanwhile
    if size <= limit:
        return None
    return f"warning: {debug} takes {size / 2**30:.1f} GB, over {limit / 2**30:.0f} GB: run `cargo clean --profile dev`"


def save_base(root, keep, out=print, build=None, target_directory=None, debug_limit=None):
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
    warning = debug_dir_warning(target, debug_limit) if debug_limit is not None else None
    if warning:
        out(warning)
    return 0


def _prune(base, keep):
    """Remove the oldest saved bases (by the time of their COMMIT) past `keep`; nothing else."""
    saved = [d for d in base.iterdir() if d.is_dir() and BASE_NAME.fullmatch(d.name) and (d / "COMMIT").is_file()]
    saved.sort(key=lambda d: ((d / "COMMIT").stat().st_mtime, d.name))
    gone = saved[: max(len(saved) - keep, 0)]
    for d in gone:
        shutil.rmtree(d)
    return [d.name for d in gone]
