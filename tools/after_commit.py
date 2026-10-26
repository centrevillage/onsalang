#!/usr/bin/env python3
"""After a commit of the code or the cases in the main tree, run the sweep of the gate (X-1 U4, U13).

    python3 -B tools/work.py commit … [--no-sweep]   the parent's commit calls `on_commit`
    python3 -B tools/after_commit.py --now          by hand: run the sweep of HEAD now
    python3 -B tools/after_commit.py --drive        the runner (`on_commit` starts it; not by hand)

`on_commit` returns at once with the line `auto sweep: …` of what it did. It does nothing in a worktree
or after a commit that touches no file of `narrowing.SWEPT` (the code and the cases). Else it
writes the request (HEAD, the time) and, unless `target/gate/hold` is there, starts the runner
when none runs (`bg.py run target/gate/auto/job`, `nice -n 10`). With `--no-sweep` the request is
of the base binaries alone (`tools/gate.sh --save-base`), and only when the commit touches the code
(`narrowing.BUILT_FROM`; after one of the cases alone, `narrowing.resolve_base` takes the base of the
same code before); a request of the sweep not run yet stays one (the sweep saves the base too).

The runner (one at a time: the lock `target/gate/auto/lock`) waits QUIET seconds after the last
request (commits in a row run once), waits up to CLEAN_WAIT seconds for the code and the cases
to have no change not committed (else the state is `skipped`: a dirty tree is not the HEAD), then
runs `tools/gate.sh --sweep` (the base binaries, the static items, the next shard), or `--save-base`,
with its output in `target/gate/auto/runs/`, and again when a commit came meanwhile. A whole run of
the gate on the same clean HEAD after the request does the request. The files and the line that show
them (`auto sweep: …`) are in `gate_runs` (its docstring). The environment loses every `GIT_*` first:
a git's `GIT_INDEX_FILE` (relative) and `GIT_DIR` would mislead the git of the gate.
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
GATE = "tools/gate.sh"

EPILOG = f"""\
commits start it: tools/work.py commit (the main tree; --no-sweep: the base binaries alone)
when to use it by hand:
  --now     after a restart of the machine, after removing {gate_runs.HOLD}, after `skipped`:
            runs the sweep of HEAD in the background (not while {gate_runs.HOLD} is there)
  stop it:  touch {gate_runs.HOLD} (commits still write the request); remove it, then --now
  see it:   the line `auto sweep: …` of the summary of tools/gate.sh (the main tree) and of
            tools/work.py patch; the output of each sweep in {gate_runs.AUTO / 'runs'}/
the line `auto sweep:` says, when one applies:
  held since …                 {gate_runs.HOLD} is there
  waiting (quiet until …)      the runner waits {QUIET} s after the last commit
  waiting for a clean tree …   the code or the cases have changes not committed
  running at <commit> since …  the sweep runs
  saving the base at <commit> … the base binaries are built and kept (--no-sweep)
  skipped at <commit>: …       the tree stayed dirty {CLEAN_WAIT} s; commit or clean it, then --now
  requested at …, no runner    the runner is gone (a restart, a failure: {gate_runs.AUTO / 'job' / 'out'}); --now.
                               For a few seconds right after --now it says so too: the runner has
                               not taken its lock yet
  gate exit N at <commit>      the gate could not run
  save-base exit N at <commit> the base binaries were not saved (the output in the line)
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


def touches(root, paths):
    """The commit at HEAD touches `paths` (pathspecs)."""
    names = narrowing.git(root, "diff-tree", "-r", "--no-commit-id", "--name-only", "--root", "HEAD", "--", *paths)
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


def request(root, now=False, sweep=True):
    """Write the request of HEAD (of the sweep, or of the base alone unless a request of the sweep waits); start
    the runner when none runs and there is no hold. What happened."""
    with gate_runs.request_lock(root):
        old = gate_runs.read_json(root, "request")
        kept = not sweep and old is not None and not old.get("taken") and old.get("sweep", True)
        what = "requested" + (" (with the sweep asked for before)" if kept else "")
        gate_runs.write_json(root, "request", {"time": time.time(), "commit": head(root), "now": now,
                                               "sweep": sweep or kept})  # fmt: skip
        if (Path(root) / gate_runs.HOLD).exists():
            return f"{what}; held"
        lock = gate_runs.try_runner(root)
        if lock is None:
            return f"{what}; the runner is on"
        lock.close()
    start_runner(root)
    return f"{what}; the runner starts"


def on_commit(root, sweep=True):
    """The request after a commit (`tools/work.py commit`, `--no-sweep`: not `sweep`), as the docstring says; the
    line `auto sweep: …` of what it did."""
    if repo.tree_kind(root) != "main":
        return "auto sweep: nothing (not the main tree; the sweep is the parent's)"
    if not touches(root, narrowing.SWEPT if sweep else narrowing.BUILT_FROM):
        return ("auto sweep: nothing (the commit touches neither the code nor the cases)" if sweep else
                "auto sweep: left out (--no-sweep); no change of the code, no base to save")  # fmt: skip
    if sweep:
        return f"auto sweep: {request(root)}"
    return f"auto sweep: left out (--no-sweep); the base {request(root, sweep=False)}"


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


def run_gate(root, commit, sweep=True):
    """Run the sweep (or save the base) with its output in `runs/` (`-base.out`: not a sweep's, which `auto_line`
    looks for), keep the last RUNS_KEPT; (the output, the exit)."""
    runs = Path(root) / gate_runs.AUTO / "runs"
    runs.mkdir(parents=True, exist_ok=True)
    out = runs / f"{time.strftime('%Y%m%d-%H%M%S')}-{commit[:narrowing.SHORT]}{'' if sweep else '-base'}.out"
    with open(out, "wb") as f:
        try:
            code = subprocess.run([str(Path(root) / GATE), "--sweep" if sweep else "--save-base"], cwd=root,
                                  stdin=subprocess.DEVNULL,
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
            sweep = req.get("sweep", True)
            with gate_runs.request_lock(root):  # a request after it does not take its sweep (`request`)
                if (gate_runs.read_json(root, "request") or {}).get("time") == req.get("time"):
                    gate_runs.write_json(root, "request", {**req, "taken": True})
            _state(root, "running", commit=commit, sweep=sweep)
            out, code = run_gate(root, commit, sweep)
            _state(root, "done", commit=commit, code=code, out=str(out), sweep=sweep)
        with gate_runs.request_lock(root):
            if (gate_runs.read_json(root, "request") or {}).get("time", 0) <= t0:
                (Path(root) / gate_runs.AUTO / "request").unlink(missing_ok=True)


def main(argv=None):
    for name in [k for k in os.environ if k.startswith("GIT_")]:
        del os.environ[name]  # a git's: the git of the gate must find the tree from its cwd
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0] + " tools/work.py commit calls it; "
                                 "by hand, use --now.", epilog=EPILOG,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)  # fmt: skip
    how = ap.add_mutually_exclusive_group(required=True)
    how.add_argument("--now", action="store_true", help="run the sweep of HEAD now, in the background (after a "
                     "restart, after removing the hold, after `skipped`); refused while the hold is there")
    how.add_argument("--drive", action="store_true", help="be the runner (a commit starts it; not by hand)")
    ap.add_argument("--root", default=str(ROOT), help="the main tree (default the tree of this file)")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    if repo.tree_kind(root) != "main":
        print(f"after_commit: {root} is not the main tree; the sweep is the parent's", file=sys.stderr)
        return 2
    try:
        if args.drive:
            return drive(root)
        if (root / gate_runs.HOLD).exists():
            print(f"after_commit: {gate_runs.HOLD} is there; remove it first", file=sys.stderr)
            return 1
        print(f"auto sweep: {request(root, now=True)}")
        print(gate_runs.auto_line(root, gate_runs.read_history(root)[0], gate_steps.SHARDS))
        return 0
    except (narrowing.NarrowError, OSError) as e:
        print(f"after_commit: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
