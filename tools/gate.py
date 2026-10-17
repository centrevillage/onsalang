#!/usr/bin/env python3
"""The one check command (Q-08, plan D-16 7). Run it as `tools/gate.sh`.

Runs every item of `gate_steps.STEPS`, even after a failure, and prints a
summary. Exit 0 if every item passes, 1 if one fails, 2 on a usage error.

    tools/gate.sh [--work ID]... [--stage-end STAGE] [--only NAMES]
    tools/gate.sh --quick
    tools/gate.sh --sweep
    tools/gate.sh --save-base

--work W3-11    the work check: also runs the items listed whole whose `until`
                is W3-11 (may repeat; pass the ID of the work at hand), narrows
                the heavy items to the seeds of the diff and a sample salted with
                the first ID, and runs the self-test only when the diff touches
                `tools/` (`gate_steps`: the forms; X-1).
--stage-end W3  also fails when `tests/pending.toml` still has entries whose
                `until` is a work of W3 (plan §8.6, the end of a stage), and
                runs every item listed whole.
                Without it, the summary shows what is left per stage.
--quick         leaves out the slow items (`Step.slow`: the fuzzing, the
                fix loop, the self-test, the C, the fmt properties) for a check in the middle
                of a work. Its last line is `gate (quick): ...`: it is not the
                gate's verdict (plan §8.3 8).
--sweep         the main tree only: saves the base binaries, runs the static
                items, the self-test and the next shard of the heavy items (the
                history, `gate_runs`). Its last line is `gate (sweep k/K): ...`.
--only NAMES    runs the items named (`a,b`; `static`: the static items) as the
                other options would; the last line is `gate (only): ...`.
--save-base     the main tree only: copies the binaries of HEAD to
                `target/base/` (`gate_runs.save_base`); takes no lock.

The work check and the sweep warn, right before the last line, when the items
took longer than `gate_steps.BUDGET_WORK` / `BUDGET_SWEEP` seconds (the wait for
the lock does not count); the warning does not fail. A run in the main tree adds
a line to `target/gate/history.jsonl` and shows the shards of the sweep.

An item marked `stage_end_only` (the deep fuzzing, `fuzz.py --deep`) runs only
with `--stage-end` and is SKIPPED otherwise: it is heavy on the machine (W3-03).

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
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import narrowing  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = TOOLS.parent
GOLDEN_DIR = "tests/golden"
# The exit code of an item that cannot run; the list never makes it pending.
CANNOT_RUN = 2
# The lock of the one gate that runs on the machine, in the common git directory.
LOCK = "onsa-gate.lock"
STATIC = "static"  # the name of the static items for `--only`


@dataclass
class Form:
    """How this run builds its items (X-1; `gate_steps`: the forms)."""

    works: tuple = ()
    stage_end: str = None
    quick: bool = False
    sweep: tuple = None  # (k, K): the shard of the heavy items
    only: tuple = None  # the names given to `--only`
    changed: frozenset = None  # the paths the diff touches, when a work check read them
    diff_error: str = None  # why it could not

    @property
    def work(self):
        """A work check: the heavy items narrowed."""
        return bool(self.works) and self.stage_end is None and self.sweep is None

    def names(self, steps):
        """The items `--only` names (`static` expanded), or None."""
        if self.only is None:
            return None
        return {n for o in self.only for n in (gate_steps.static_names(steps) if o == STATIC else [o])}

    def label(self):
        if self.sweep is not None:
            return f"sweep {self.sweep[0]}/{self.sweep[1]}"
        if self.only is not None:
            return "only " + ",".join(self.only)
        if self.stage_end is not None:
            return f"stage-end {self.stage_end}"
        return "work " + ",".join(self.works) if self.works else "whole"


@dataclass
class Result:
    step: gate_steps.Step
    argv: list
    code: int
    seconds: float
    pending: object = None  # the `gate` entry, when listed
    skipped: str = None  # why the item did not run
    note: str = ""  # how it ran: narrowed, whole, a shard

    @property
    def status(self):
        if self.skipped is not None:
            return "SKIPPED"
        if self.step.info:
            return "INFO" if self.code == 0 else "FAIL"
        if self.pending is not None:
            return "PENDING" if self.code not in (0, CANNOT_RUN) else "FAIL"
        if self.step.parent and self.code == gate_steps.PARENT:
            return "PARENT"
        return "PASS" if self.code == 0 else "FAIL"

    @property
    def failed(self):
        return self.status == "FAIL"

    def describe(self):
        if self.skipped is not None:
            return self.skipped
        return "; ".join(x for x in (self.note, self._outcome()) if x)

    def _outcome(self):
        if self.pending is not None and self.code == 0:
            return f"passes but is listed in tests/pending.toml (until {self.pending.until}); remove the entry"
        if self.pending is not None and self.code == CANNOT_RUN:
            return f"exit {self.code}: the item cannot run (the list does not hold that)"
        if self.pending is not None:
            return f"fails as expected (until {self.pending.until}: {self.pending.note})"
        if self.status == "PARENT":
            return f"waits for the parent (the lines `parent:` of {self.step.name})"
        return "" if self.code == 0 else f"exit {self.code}"


def run_steps(steps, listed, stage_end=None, cwd=ROOT, out=sys.stdout, works=(), quick=False, form=None):
    """Run each step of the form and return the results. `listed` maps item names to the
    entries that list them whole. `works` are the IDs of `--work`; `form` (a `Form`)
    stands for `stage_end`, `works` and `quick` when given."""
    form = form or Form(tuple(works), stage_end, quick)
    pendable = ",".join(gate_steps.pendable(steps))
    named = form.names(steps)
    results = []
    for step in steps:
        if not _in_form(step, form, named):
            continue
        argv = list(step.argv)
        if step.gate_steps:
            argv += ["--gate-steps", pendable]
        if step.stage_args and form.stage_end is not None:
            argv += ["--stage-end", form.stage_end]
        extra, note = _narrowing(step, form)
        argv += extra
        entry = listed.get(step.name) if step.pendable and not step.info else None
        skipped = _skipped(step, entry, form, named)
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
        results.append(Result(step, argv, code, time.monotonic() - t0, entry, note=note))
    return results


def _in_form(step, form, named):
    """`step` is in this run (listed in the summary, run or skipped)."""
    if named is not None:
        return step.name in named
    if form.sweep is not None:
        return step.sweep or step.static or bool(step.narrows)
    return not step.sweep_only


def _narrowing(step, form):
    """The options of a heavy item in this form, and the note of how it runs."""
    if not step.narrows:
        return [], ""
    if form.sweep is not None:
        return ["--shard", f"{form.sweep[0]}/{form.sweep[1]}"], f"shard {form.sweep[0]}/{form.sweep[1]}"
    if not form.work:
        return [], ""
    if form.changed is None:
        return [], "whole: the diff is not known"
    hit = sorted(p for p in form.changed if narrowing.under(p, step.narrows))
    if hit:
        return [], f"whole: the diff touches {hit[0]}"
    sample = ["--sample", str(gate_steps.SAMPLE), "--salt", form.works[0]]
    return ["--changed-since", "auto", *sample], f"narrowed (sample {gate_steps.SAMPLE}, salt {form.works[0]})"


def _skipped(step, entry, form, named=None):
    """Why `step` does not run in this gate, or None."""
    if form.quick and step.slow:
        return "left out by --quick"
    if step.stage_end_only and form.stage_end is None:
        return "runs only with --stage-end"
    if entry is not None and form.stage_end is None and entry.until not in form.works:
        return f"listed until {entry.until}: runs with --work {entry.until} or --stage-end"
    if step.touches and form.work and named is None and form.changed is not None:
        if not any(narrowing.under(p, step.touches) for p in form.changed):
            return f"the diff does not touch {', '.join(step.touches)}"
    return None


def read_diff(steps, form, root):
    """Read the paths of the diff when the work check has an item that needs them."""
    named = form.names(steps)
    if form.work and any(_in_form(s, form, named) and (s.narrows or s.touches) for s in steps):
        try:
            form.changed = frozenset(narrowing.changed_paths(root, narrowing.merge_base(root)))
        except narrowing.NarrowError as e:
            form.diff_error = str(e)


def lock_path(root):
    """The lock of the gate of `root`: in the common git directory when `root`
    is the top of a git work tree (the main tree and its worktrees share it),
    else in `root` (the self-tests' made-up roots)."""
    dirs = repo.git_dirs(root)
    return dirs[1] / LOCK if dirs else Path(root) / f".{LOCK}"


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


def summary(results, entries, golden_lines, stages, stage_end=None, list_ok=True, quick=False, form=None, notes=()):
    """The summary (`stages`: `repo.Layout.stages`); `notes` come right before the warning of the time and the last line."""
    form = form or Form((), stage_end, quick)
    lines = ["", "=== summary"]
    width = max((len(r.step.name) for r in results), default=0)
    for r in results:
        lines.append(f"  {r.status:<7} {r.step.name:<{width}}  {r.seconds:6.1f}s  {r.describe()}".rstrip())
    lines.append("  " + pending.stages_line(entries, stages) + ("" if list_ok else " (the list has errors, see `pending`)"))
    if stage_end is not None:
        left = len(pending.stage_end_errors(entries, stage_end, stages))
        lines.append(f"  stage end {stage_end}: " + (f"{left} entr{'y' if left == 1 else 'ies'} left" if left else "nothing left"))
    if golden_lines is None:
        lines.append("  golden: cannot list (see `golden`)")
    else:
        lines.append("  golden: " + ("no file differs from HEAD" if not golden_lines else "differs from HEAD (read and approve):"))
        lines += [f"    {g}" for g in golden_lines]
    lines += [f"  {n}" for n in notes]
    warning = time_warning(results, form)
    if warning:
        lines.append(warning)
    failed = [r.step.name for r in results if r.failed]
    head = "gate:"
    if form.quick:
        head = "gate (quick):"
    elif form.sweep is not None:
        head = f"gate (sweep {form.sweep[0]}/{form.sweep[1]}):"
    elif form.only is not None:
        head = "gate (only):"
    lines.append(f"{head} FAIL (" + ", ".join(failed) + ")" if failed else f"{head} PASS")
    return lines


def time_warning(results, form):
    """The warning when the items of a work check or a sweep took longer than their budget."""
    if form.only is not None or form.quick:
        return None
    if form.sweep is not None:
        what, budget = "the sweep", gate_steps.BUDGET_SWEEP
    elif form.work:
        what, budget = "the work check", gate_steps.BUDGET_WORK
    else:
        return None
    total = sum(r.seconds for r in results)
    if total <= budget:
        return None
    top = sorted(results, key=lambda r: -r.seconds)[:3]
    longest = ", ".join(f"{r.step.name} {r.seconds:.1f}s" for r in top)
    return f"warning: {what} took {total:.0f}s, {total - budget:.0f}s over its {budget}s; the longest: {longest}"


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


def _form_problem(args, steps, only, kind, root):
    """The usage error of the options of the form, or None."""
    if args.quick and (args.stage_end is not None or args.work or only is not None):
        return "--quick leaves out items; it does not go with --stage-end, --work or --only"
    if args.sweep and (args.stage_end is not None or args.work or args.quick or only is not None):
        return "--sweep goes alone"
    if args.sweep and kind != "main":
        return f"--sweep runs only in the main tree; {root} is {'a worktree' if kind else 'not a git work tree'}"
    if only is not None:
        known = [s.name for s in steps if not s.sweep_only] + [STATIC]
        unknown = [n for n in only if n not in known]
        if not only or unknown:
            return f"--only takes names of items: {', '.join(known)}; unknown: {', '.join(unknown) or '(none)'}"
    return None


def main(argv=None, steps=None, root=ROOT, out=sys.stdout):
    ap = argparse.ArgumentParser(description="Run every check (Q-08).")
    ap.add_argument("--stage-end", metavar="STAGE", help="fail if tests/pending.toml has entries of STAGE (W3, M5)")
    ap.add_argument("--work", metavar="ID", action="append", default=[],
                    help="also run the items listed whole until this work (W3-11; may repeat)")  # fmt: skip
    ap.add_argument("--quick", action="store_true", help="leave out the slow items (not the gate's verdict)")
    ap.add_argument("--sweep", action="store_true", help="the main tree only: the static items and the next shard")
    ap.add_argument("--only", metavar="NAMES", help=f"run only these items (a,b; {STATIC}: the static items)")
    ap.add_argument("--save-base", action="store_true", help="the main tree only: keep the binaries of HEAD")
    ap.add_argument("--golden", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    if args.golden:
        return golden_main(Path.cwd())
    others = args.stage_end is not None or bool(args.work) or args.quick or args.sweep or args.only is not None
    if args.save_base:
        if others:
            print("--save-base goes alone", file=sys.stderr)
            return 2
        return gate_runs.save_base(root, gate_steps.BASES_KEPT, out=lambda line: print(line, file=out),
                                   debug_limit=gate_steps.DEBUG_DIR_LIMIT)
    if "UPDATE_GOLDEN" in os.environ:
        print("UPDATE_GOLDEN is set: the gate only checks and would rewrite the golden files; unset it", file=sys.stderr)
        return 2
    steps = gate_steps.STEPS if steps is None else steps
    kind = repo.tree_kind(root)
    only = tuple(n for n in args.only.split(",") if n) if args.only is not None else None
    problem = _form_problem(args, steps, only, kind, root)
    if problem:
        print(problem, file=sys.stderr)
        return 2
    try:  # the stages order the summary; the stage and the works are checked when given
        stages = repo.Layout(root).stages()
        if args.stage_end is not None or args.work:
            docs = pending.load_docs(root)
            problem = pending.stage_problem(args.stage_end, docs) if args.stage_end is not None else None
            unknown = [w for w in args.work if w not in docs.works]
            if problem is None and unknown:
                problem = f"--work needs a W ID of {docs.works_at}; unknown: " + ", ".join(unknown)
    except pending.DocsError as e:
        problem = f"cannot check the stage or the work: the document tables are not found: {e}"
    if problem:
        print(problem, file=sys.stderr)
        return 2
    with one_gate(root, out):
        entries, load_errors = pending.load(root / pending.PENDING)
        listed = {e.target: e for e in pending.of_kind(entries, "gate") if "/" not in e.target}
        form = Form(tuple(args.work), args.stage_end, args.quick, only=only)
        if args.sweep:
            try:
                form.sweep = (gate_runs.next_shard(gate_runs.read_history(root)[0], gate_steps.SHARDS), gate_steps.SHARDS)
            except OSError as e:
                print(f"--sweep cannot read the history to find its shard: {e}", file=sys.stderr)
                return 2
        read_diff(steps, form, root)
        results = run_steps(steps, listed, cwd=root, out=out, form=form)
        try:
            golden = golden_changes(root)
        except (subprocess.CalledProcessError, OSError):
            golden = None
        failed = any(r.failed for r in results)
        notes = [f"diff: cannot read it ({form.diff_error}); the narrowable items run whole"] if form.diff_error else []
        if kind == "main" and not form.quick:
            notes += _history(root, form, results, failed)
        for line in summary(results, entries, golden, stages, args.stage_end, not load_errors, args.quick, form, notes):
            print(line, file=out)
    return 1 if failed else 0


def _history(root, form, results, failed):
    """Add the line of this run to the history of the main tree; the notes of the summary."""
    items = {r.step.name: [r.status, round(r.seconds, 1)] for r in results}
    seconds = sum(r.seconds for r in results)
    error = gate_runs.record(root, form.label(), form.works, items, "FAIL" if failed else "PASS", seconds)
    notes = [f"history: cannot write it ({error})"] if error else []
    try:
        rows, bad = gate_runs.read_history(root)
    except OSError as e:
        return notes + [f"history: cannot read it ({e})"]
    notes.append(gate_runs.sweep_line(root, rows, bad, gate_steps.SHARDS))
    warning = gate_runs.debug_dir_warning(Path(root) / "target", gate_steps.DEBUG_DIR_LIMIT)
    return notes + ([warning] if warning else [])


if __name__ == "__main__":
    sys.exit(main())
