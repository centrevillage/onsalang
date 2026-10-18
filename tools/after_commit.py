#!/usr/bin/env python3
"""After a commit of the code or the cases in the main tree, run the sweep of the gate (X-1 U4).

    python3 -B tools/after_commit.py            the post-commit hook calls it (tools/hooks/post-commit)
    python3 -B tools/after_commit.py --now      by hand: run the sweep of HEAD now
    python3 -B tools/after_commit.py --drive    the runner (the hook starts it; not by hand)

The hook (`git config core.hooksPath tools/hooks`) returns at once. It does nothing in a worktree
or after a commit that touches no file of `narrowing.SWEPT` (the code and the cases). Else it
writes the request (HEAD, the time) and, unless `target/gate/hold` is there, starts the runner
when none runs (`bg.py run target/gate/auto/job`, `nice -n 10`). The environment loses every
`GIT_*` first: the hook's `GIT_INDEX_FILE` (relative) and `GIT_DIR` would mislead the git of the
gate.

The runner (one at a time: the lock `target/gate/auto/lock`) waits QUIET seconds after the last
request (commits in a row run once), waits up to CLEAN_WAIT seconds for the code and the cases
to have no change not committed (else the state is `skipped`: a dirty tree is not the HEAD), then
runs `tools/gate.sh --sweep` (the base binaries, the static items, the next shard) with its output
in `target/gate/auto/runs/`, and again when a commit came meanwhile. A whole run of the gate on
the same clean HEAD after the request does the request. The files and the line that shows them
(`auto sweep: …`) are in `gate_runs` (its docstring). A worktree whose tree has no such file runs
no hook at all.
"""
import argparse
import contextlib
import io
import os
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import bg  # noqa: E402
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import narrowing  # noqa: E402
import repo  # noqa: E402

ROOT = TOOLS.parent
QUIET = 180  # seconds after the last request before the sweep runs
CLEAN_POLL = 60  # seconds between two looks at a dirty tree
CLEAN_WAIT = 3600  # seconds a request waits for a clean tree before it is skipped
NAP = 5  # the longest sleep while waiting for the quiet (a new request moves it)
GATE = ("tools/gate.sh", "--sweep")

EPILOG = f"""\
when to use it by hand:
  --now     after a restart of the machine, after removing {gate_runs.HOLD}, after `skipped`, or
            right after setting the hook up (no base saved yet): runs the sweep of HEAD in the
            background (not while {gate_runs.HOLD} is there)
  stop it:  touch {gate_runs.HOLD} (commits still write the request); remove it, then --now
  see it:   the line `auto sweep: …` of the summary of tools/gate.sh (the main tree) and of
            tools/work.py patch; the output of each sweep in {gate_runs.AUTO / 'runs'}/
the line `auto sweep:` says, when one applies:
  hook not set (…)             core.hooksPath of this clone does not name {gate_runs.HOOKS}: commits
                               start nothing (set it with the command in the line)
  held since …                 {gate_runs.HOLD} is there
  waiting (quiet until …)      the runner waits {QUIET} s after the last commit
  waiting for a clean tree …   the code or the cases have changes not committed
  running at <commit> since …  the sweep runs
  skipped at <commit>: …       the tree stayed dirty {CLEAN_WAIT} s; commit or clean it, then --now
  requested at …, no runner    the runner is gone (a restart, a failure: {gate_runs.AUTO / 'job' / 'out'}); --now.
                               For a few seconds right after --now it says so too: the runner has
                               not taken its lock yet
  gate exit N at <commit>      the gate could not run
and then the outcome: FAILED at <commit>: <items> (<output>) / last PASS at <commit> / no sweep yet
when it says FAILED:
  read      the output the line points to (in {gate_runs.AUTO / 'runs'}/) and the inputs the fuzzing
            made small, in target/fuzz/new/ (the gate's `fuzz new: …` lists those not sorted yet)
  marked    a class the fuzzing marks `(pre-existing: the base <commit> (the code before HEAD)
            shows it)` was there at that commit, before the code of HEAD: not one the commit
            brought (the fuzzing line says `base unknown` when no base tells them apart)
  it stays  a shard that fails on a class known before stays FAILED until the class is in
            tests/fuzz/allowed.toml or in an R; the commit of that touches tests/, so it starts a
            sweep. The line clears when that shard passes; a sweep runs the next shard, so it can
            take {gate_steps.SHARDS} sweeps (more commits of the code or the cases, or --now)
example: python3 -B tools/after_commit.py --now"""


def heavy(root):
    """The commit at HEAD touches the code or the cases."""
    names = narrowing.git(root, "diff-tree", "-r", "--no-commit-id", "--name-only", "--root", "HEAD", "--",
                          *narrowing.SWEPT)  # fmt: skip
    return bool(names.strip())


def uncommitted(root):
    """The paths of the code and the cases with changes not committed, untracked ones too."""
    fields = narrowing.git(root, "status", "--porcelain=v1", "-z", "--untracked-files=all", "--",
                           *narrowing.SWEPT).split("\0")  # fmt: skip
    paths, i = [], 0
    while i < len(fields):
        if fields[i]:
            paths.append(fields[i][3:])
        i += 2 if fields[i][:1] in ("R", "C") else 1
    return paths


def head(root):
    return narrowing.git(root, "rev-parse", "HEAD").strip()


def start_runner(root):
    """Start the runner with bg.py. Called only when the runner's lock was free: no runner lives, so
    the files of the job before go first (a pid of before may be another process now)."""
    job = Path(root) / gate_runs.AUTO / "job"
    job.mkdir(parents=True, exist_ok=True)
    for name in bg.FILES:
        (job / name).unlink(missing_ok=True)
    cmd = ["nice", "-n", "10", sys.executable, "-B", str(Path(__file__).resolve()), "--drive", "--root", str(root)]
    with contextlib.redirect_stdout(io.StringIO()):
        bg.run(job, cmd)


def request(root, now=False):
    """Write the request of HEAD; start the runner when none runs and there is no hold. What happened."""
    with gate_runs.request_lock(root):
        gate_runs.write_json(root, "request", {"time": time.time(), "commit": head(root), "now": now})
        if (Path(root) / gate_runs.HOLD).exists():
            return "requested; held"
        lock = gate_runs.try_runner(root)
        if lock is None:
            return "requested; the runner is on"
        lock.close()
    start_runner(root)
    return "requested; the runner starts"


def _state(root, state, **fields):
    gate_runs.write_json(root, "state", {"time": time.time(), "state": state, **fields})


def _leave(root, lock, req):
    """Let the runner's lock go unless a new request came: then the runner goes on (False)."""
    with gate_runs.request_lock(root):
        if (gate_runs.read_json(root, "request") or {}).get("time") != (req or {}).get("time"):
            return False
        lock.close()
        return True


def _done(root, commit, since):
    """A whole run of the gate on `commit`, clean, after `since`, is in the history."""
    rows = gate_runs.read_history(root)[0]
    return any(r.get("commit") == commit and gate_runs.whole_run(r) and gate_runs.epoch(r) >= since for r in rows)


def run_gate(root, commit):
    """Run the sweep with its output in `runs/`, keep the last RUNS_KEPT; (the output, the exit)."""
    runs = Path(root) / gate_runs.AUTO / "runs"
    runs.mkdir(parents=True, exist_ok=True)
    out = runs / f"{time.strftime('%Y%m%d-%H%M%S')}-{commit[:narrowing.SHORT]}.out"
    with open(out, "wb") as f:
        try:
            code = subprocess.run([str(Path(root) / GATE[0]), *GATE[1:]], cwd=root, stdin=subprocess.DEVNULL,
                                  stdout=f, stderr=subprocess.STDOUT).returncode  # fmt: skip
        except OSError as e:
            f.write(f"after_commit: the gate does not start: {e}\n".encode())
            code = 127
    for old in sorted(runs.glob("*.out"))[:-gate_runs.RUNS_KEPT]:
        old.unlink()
    return out, code


def drive(root):
    """The runner: the states and the loop of the docstring. It ends when no new request comes."""
    with gate_runs.request_lock(root):
        lock = gate_runs.try_runner(root)
    if lock is None:
        return 0  # another runner lives; it takes the request
    seen, dirty_since = None, None
    while True:
        with gate_runs.request_lock(root):
            req = gate_runs.read_json(root, "request")
        if (req or {}).get("time") != (seen or {}).get("time"):
            seen, dirty_since = req, None
        if req is None or (Path(root) / gate_runs.HOLD).exists():
            if req is not None:
                _state(root, "held")
            if _leave(root, lock, req):
                return 0
            continue
        quiet = req.get("time", 0) + QUIET - time.time()
        if not req.get("now") and quiet > 0:
            _state(root, "waiting", until=req.get("time", 0) + QUIET)
            time.sleep(min(quiet, NAP))
            continue
        dirty = uncommitted(root)
        if dirty:
            dirty_since = dirty_since or time.time()
            left = dirty_since + CLEAN_WAIT - time.time()
            if not req.get("now") and left > 0:
                _state(root, "waiting-clean", path=dirty[0], until=dirty_since + CLEAN_WAIT)
                time.sleep(min(CLEAN_POLL, left))
                continue
            _state(root, "skipped", commit=head(root), path=dirty[0])
            if _leave(root, lock, req):
                return 0
            continue
        commit, t0 = head(root), time.time()
        if not _done(root, commit, req.get("time", 0)):
            _state(root, "running", commit=commit)
            out, code = run_gate(root, commit)
            _state(root, "done", commit=commit, code=code, out=str(out))
        with gate_runs.request_lock(root):
            if (gate_runs.read_json(root, "request") or {}).get("time", 0) <= t0:
                (Path(root) / gate_runs.AUTO / "request").unlink(missing_ok=True)


def main(argv=None):
    for name in [k for k in os.environ if k.startswith("GIT_")]:
        del os.environ[name]  # the hook's: the git of the gate must find the tree from its cwd
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0] + " The post-commit hook calls it; "
                                 "by hand, use --now.", epilog=EPILOG,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)  # fmt: skip
    ap.add_argument("--now", action="store_true", help="run the sweep of HEAD now, in the background (after a "
                    "restart, after removing the hold, after `skipped`); refused while the hold is there")
    ap.add_argument("--drive", action="store_true", help="be the runner (the hook starts it; not by hand)")
    ap.add_argument("--root", default=str(ROOT), help="the main tree (default the tree of this file)")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    if repo.tree_kind(root) != "main":
        if args.now or args.drive:
            print(f"after_commit: {root} is not the main tree; the sweep is the parent's", file=sys.stderr)
            return 2
        return 0  # a worktree's commit (the WIP of an agent)
    try:
        if args.drive:
            return drive(root)
        if args.now and (root / gate_runs.HOLD).exists():
            print(f"after_commit: {gate_runs.HOLD} is there; remove it first", file=sys.stderr)
            return 1
        if args.now or heavy(root):
            print(f"auto sweep: {request(root, now=args.now)}")
            if args.now:
                print(gate_runs.auto_line(root, gate_runs.read_history(root)[0], gate_steps.SHARDS))
        return 0
    except (narrowing.NarrowError, OSError) as e:
        print(f"after_commit: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
