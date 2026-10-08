#!/usr/bin/env python3
"""The one check command (Q-08, plan D-16 7). Run it as `tools/gate.sh`.

Runs every item of `gate_steps.STEPS`, even after a failure, and prints a
summary. Exit 0 if every item passes, 1 if one fails, 2 on a usage error.

    tools/gate.sh [--work ID]... [--stage-end STAGE]
    tools/gate.sh --quick

--work W3-11    also runs the items listed whole whose `until` is W3-11
                (may repeat). Pass the ID of the work at hand.
--stage-end W3  also fails when `tests/pending.toml` still has entries whose
                `until` is a work of W3 (plan §8.6, the end of a stage), and
                runs every item listed whole.
                Without it, the summary shows what is left per stage.
--quick         leaves out the slow items (`Step.slow`: the fuzzing, the
                self-test, the C, the fmt properties) for a check in the middle
                of a work. Its last line is `gate (quick): ...`: it is not the
                gate's verdict (plan §8.3 8).

A pendable gate item listed in `tests/pending.toml` (kind `gate`, target =
the item's name) is expected to fail: its failure is shown as pending, and its
passing fails the gate (remove the entry). Listed whole, it is known to fail,
so it runs only for its work (`--work`) or at a stage end, and is SKIPPED
otherwise (2026-10-08). An item that cannot run (exit `CANNOT_RUN`, 2: a usage
error, a tool it needs is missing) fails even when listed: the list holds what
fails, not what does not run (W1-06). An `info` item shows something; it fails
only when it cannot.

One gate runs at a time on the machine: the main tree and its git worktrees
share a lock in the common git directory, and a gate that finds it taken says
whose it is and waits (2026-10-08). The items use every core, and gates that
run side by side only slow each other down.

Golden files (Q-04): the expectations that `UPDATE_GOLDEN=1` rewrites, and
their inputs, live under `tests/golden/`. The summary lists every file there
that differs from HEAD (modified, added, deleted, untracked) for the parent
to read and approve; a difference does not fail the gate. The gate checks; it
never rewrites, so it refuses to run with `UPDATE_GOLDEN` set.
"""
import argparse
import contextlib
import fcntl
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import gate_steps  # noqa: E402
import pending  # noqa: E402

ROOT = TOOLS.parent
GOLDEN_DIR = "tests/golden"
# The exit code of an item that cannot run; the list never makes it pending.
CANNOT_RUN = 2
# The lock of the one gate that runs on the machine, in the common git directory.
LOCK = "onsa-gate.lock"


@dataclass
class Result:
    step: gate_steps.Step
    argv: list
    code: int
    seconds: float
    pending: object = None  # the `gate` entry, when listed
    skipped: str = None  # why the item did not run

    @property
    def status(self):
        if self.skipped is not None:
            return "SKIPPED"
        if self.step.info:
            return "INFO" if self.code == 0 else "FAIL"
        if self.pending is not None:
            return "PENDING" if self.code not in (0, CANNOT_RUN) else "FAIL"
        return "PASS" if self.code == 0 else "FAIL"

    @property
    def failed(self):
        return self.status == "FAIL"

    def describe(self):
        if self.skipped is not None:
            return self.skipped
        if self.pending is not None and self.code == 0:
            return f"passes but is listed in tests/pending.toml (until {self.pending.until}); remove the entry"
        if self.pending is not None and self.code == CANNOT_RUN:
            return f"exit {self.code}: the item cannot run (the list does not hold that)"
        if self.pending is not None:
            return f"fails as expected (until {self.pending.until}: {self.pending.note})"
        return "" if self.code == 0 else f"exit {self.code}"


def run_steps(steps, listed, stage_end=None, cwd=ROOT, out=sys.stdout, works=(), quick=False):
    """Run each step and return the results. `listed` maps item names to the
    entries that list them whole. `works` are the IDs of `--work`."""
    pendable = ",".join(gate_steps.pendable(steps))
    results = []
    for step in steps:
        argv = list(step.argv)
        if step.gate_steps:
            argv += ["--gate-steps", pendable]
        if step.stage_args and stage_end is not None:
            argv += ["--stage-end", stage_end]
        entry = listed.get(step.name) if step.pendable and not step.info else None
        skipped = _skipped(step, entry, stage_end, works, quick)
        if skipped is not None:
            results.append(Result(step, argv, 0, 0.0, entry, skipped))
            continue
        print(f"\n=== {step.name}: {' '.join(argv)}", file=out, flush=True)
        t0 = time.monotonic()
        try:
            code = subprocess.run(argv, cwd=cwd, env=_env()).returncode
        except OSError as e:
            print(f"cannot run: {e}", file=out, flush=True)
            code = 127
        results.append(Result(step, argv, code, time.monotonic() - t0, entry))
    return results


def _skipped(step, entry, stage_end, works, quick):
    """Why `step` does not run in this gate, or None."""
    if quick and step.slow:
        return "left out by --quick"
    if entry is not None and stage_end is None and entry.until not in works:
        return f"listed until {entry.until}: runs with --work {entry.until} or --stage-end"
    return None


def lock_path(root):
    """The lock of the gate of `root`: in the common git directory when `root`
    is the top of a git work tree (the main tree and its worktrees share it),
    else in `root` (the self-tests' made-up roots)."""
    try:
        top = _git(root, "rev-parse", "--show-toplevel").strip()
        if Path(top).resolve() == Path(root).resolve():
            return Path(_git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").strip()) / LOCK
    except (subprocess.CalledProcessError, OSError):
        pass
    return Path(root) / f".{LOCK}"


@contextlib.contextmanager
def one_gate(root, out=sys.stdout):
    """Hold the lock of the gate; wait, and say so, while another gate holds it.
    The system drops the lock when the process ends, however it ends."""
    path = lock_path(root)
    with open(path, "a+", encoding="utf-8") as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            f.seek(0)
            holder = f.read().strip() or "unknown"
            print(f"gate: another gate runs ({holder}); waiting for it to end", file=out, flush=True)
            t0 = time.monotonic()
            fcntl.flock(f, fcntl.LOCK_EX)
            print(f"gate: waited {time.monotonic() - t0:.0f}s", file=out, flush=True)
        f.seek(0)
        f.truncate()
        f.write(f"pid {os.getpid()} in {Path(root).resolve()} since {time.strftime('%H:%M:%S')}\n")
        f.flush()
        yield


def _env():
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def summary(results, entries, golden_lines, stage_end=None, list_ok=True, quick=False):
    lines = ["", "=== summary"]
    width = max((len(r.step.name) for r in results), default=0)
    for r in results:
        lines.append(f"  {r.status:<7} {r.step.name:<{width}}  {r.seconds:6.1f}s  {r.describe()}".rstrip())
    lines.append("  " + pending.stages_line(entries) + ("" if list_ok else " (the list has errors, see `pending`)"))
    if stage_end is not None:
        left = len(pending.stage_end_errors(entries, stage_end))
        lines.append(f"  stage end {stage_end}: " + (f"{left} entr{'y' if left == 1 else 'ies'} left" if left else "nothing left"))
    if golden_lines is None:
        lines.append("  golden: cannot list (see `golden`)")
    else:
        lines.append("  golden: " + ("no file differs from HEAD" if not golden_lines else "differs from HEAD (read and approve):"))
        lines += [f"    {g}" for g in golden_lines]
    failed = [r.step.name for r in results if r.failed]
    head = "gate (quick):" if quick else "gate:"
    lines.append(f"{head} FAIL (" + ", ".join(failed) + ")" if failed else f"{head} PASS")
    return lines


def golden_changes(root=ROOT):
    """Files under tests/golden that differ from HEAD: modified, added, deleted,
    untracked. Raises CalledProcessError / OSError when git fails."""
    diff = _git(root, "diff", "HEAD", "--name-status", "--no-renames", "-z", "--", GOLDEN_DIR)
    others = _git(root, "ls-files", "--others", "--exclude-standard", "-z", "--", GOLDEN_DIR)
    fields = [f for f in diff.split("\0") if f]
    out = [f"{fields[i]} {fields[i + 1]}" for i in range(0, len(fields) - 1, 2)]
    out += [f"? {p}" for p in others.split("\0") if p]
    return sorted(out, key=lambda s: s.split(" ", 1)[1])


def _git(root, *args):
    return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, check=True).stdout


def golden_main(root):
    try:
        changes = golden_changes(root)
    except (subprocess.CalledProcessError, OSError) as e:
        err = getattr(e, "stderr", "") or ""
        print(f"cannot list the golden files: {e}\n{err}".rstrip())
        return 1
    print("\n".join(changes) if changes else "no golden file differs from HEAD")
    return 0


def main(argv=None, steps=None, root=ROOT, out=sys.stdout):
    ap = argparse.ArgumentParser(description="Run every check (Q-08).")
    ap.add_argument("--stage-end", metavar="STAGE", help="fail if tests/pending.toml has entries of STAGE (W3, M5)")
    ap.add_argument("--work", metavar="ID", action="append", default=[],
                    help="also run the items listed whole until this work (W3-11; may repeat)")  # fmt: skip
    ap.add_argument("--quick", action="store_true", help="leave out the slow items (not the gate's verdict)")
    ap.add_argument("--golden", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    if args.golden:
        return golden_main(Path.cwd())
    if "UPDATE_GOLDEN" in os.environ:
        print("UPDATE_GOLDEN is set: the gate only checks and would rewrite the golden files; unset it", file=sys.stderr)
        return 2
    if args.quick and (args.stage_end is not None or args.work):
        print("--quick leaves out items; it does not go with --stage-end or --work", file=sys.stderr)
        return 2
    if args.stage_end is not None or args.work:
        try:
            docs = pending.load_docs(root)
            problem = pending.stage_problem(args.stage_end, docs) if args.stage_end is not None else None
            unknown = [w for w in args.work if w not in docs.works]
            if problem is None and unknown:
                problem = "--work needs a W or T ID of the tables; unknown: " + ", ".join(unknown)
        except pending.DocsError as e:
            problem = f"cannot check the stage or the work: the document tables are not found: {e}"
        if problem:
            print(problem, file=sys.stderr)
            return 2
    steps = gate_steps.STEPS if steps is None else steps
    with one_gate(root, out):
        entries, load_errors = pending.load(root / pending.PENDING)
        listed = {e.target: e for e in pending.of_kind(entries, "gate") if "/" not in e.target}
        results = run_steps(steps, listed, args.stage_end, cwd=root, out=out, works=args.work, quick=args.quick)
        try:
            golden = golden_changes(root)
        except (subprocess.CalledProcessError, OSError):
            golden = None
        for line in summary(results, entries, golden, args.stage_end, not load_errors, args.quick):
            print(line, file=out)
    return 1 if any(r.failed for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
