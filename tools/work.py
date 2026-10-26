#!/usr/bin/env python3
"""The work of an agent's worktree (X-9, X9-13 to X9-17): make it, take its work into the main tree, and clean it up.

    tools/work.py new <name> [--main DIR]
    tools/work.py take <worktree> [--base B] [--estimate N] [--go] [--out FILE] [--main DIR]
    tools/work.py patch <worktree> <base> <out.patch> [--main DIR]
    tools/work.py check <patch> [--to DIR]
    tools/work.py apply <patch> [--to DIR]
    tools/work.py done <worktree> [--discard] [--session ID] [--scratchpad DIR] [--main DIR]
    tools/work.py close [--dry-run] [--session ID] [--scratchpad DIR] [--main DIR]
    tools/work.py remove <path> [--session ID] [--scratchpad DIR] [--main DIR]
    tools/work.py sync [--apply PATCH] [-m SUBJECT] [--tree DIR]
    tools/work.py lines [--base B] [--estimate N] [--tree DIR]
    tools/work.py commit -m SUBJECT [-m TEXT ...] [-F FILE] [PATH ...] [--done ID] [--docs-checked A..B WORK]
                         [--co-author "NAME <MAIL>"] [--no-sweep] [--tree DIR]
    tools/work.py help [--role ROLE] [COMMAND]

`new` makes the worktree `<main>/.claude/worktrees/<name>` (`WORKTREES`) of the main tree of DIR (default
this repository) on a new branch `worktree-<name>` (`branch_of`, one place: the cleaning up uses it too)
from `dev` by name, not from a HEAD, after `git worktree prune`, and prints its path as the last line (the
hook `WorktreeCreate` of `tools/hooks/claude_hook.py` calls `new`). It stops when the branch or the path is
there already: an old branch is never taken again unawares.

`take` runs `patch` and `check`, and goes on to apply only when the patch applies plain, the main tree
(`--main`) has no uncommitted change in the files of the patch, and the line `work check: …` does not ask
for the work check again; else it stops after the check (exit 1) and `--go` applies it the way `apply`
does. The worktree is a path or a name under `<main>/.claude/worktrees/`; the base is by default
`git merge-base dev <its HEAD>`, and the patch `<main>/target/work/<name>-<time>.patch`. It adds to the
summary the hunks of the patch in `REGISTRIES` as they are; with `--estimate N`, the ratio of the lines
added to the code (without the tests and the data, as the summary counts them) to N and whether it is over
the size to refactor, read from the row `REFACTOR` of rules/budgets.md of the main tree (`lines`: of the worktree;
without the row or its numbers, the line says why it is not judged, and nothing stops); and when the check is
3-way and the patch has `tests/pending.toml`, the line that says to rebuild it from dev's version
(rules/leader.md 3.4).

`patch` and an `apply` that exits 0 each add a line to `<the main tree>/target/work/taken.jsonl` (`TAKEN`,
`record`; the cleaning up reads it, X9-16): `{"time", "kind": "patch", "worktree", "branch", "base",
"tree" (`repo.tree_hash` of the worktree, untracked files too), "patch"}` and `{"time", "kind": "apply",
"patch", "to", "head" (of the tree applied to)}`, the paths absolute. A failure to write it prints a line
and fails nothing.

`patch` runs, in the worktree (`git -C`, no `cd`), `add -A`,
`diff --cached --binary <base>` into the patch and `reset` (the index of the
worktree is left empty). It stops when the base is not an ancestor of the
worktree's HEAD. When the HEAD of the main tree (`--main`, default this
repository) differs from the base, it prints the files that differ between
them and the files of the patch among them (3.3: when only documents moved,
the patch from the base still applies). It prints the lines added and removed
per file, the new files, the totals, and the totals without the tests and
the data (`is_code`: the files ending in `CODE_SUFFIXES` that are not under
`tests/` or `crates/*/tests/`, not `tests.rs` nor `*_tests.rs`, and not
`tools/test_*.py` nor `tools/*/test_*.py`; in a Rust file of the code, the
lines of a `#[cfg(test)] mod … { … }` block are tests too, on the new side for
the added lines and on the old side for the removed ones: `repo.test_lines`).
Its second line, `work check: …`, reads the last work check of the worktree (its
`target/gate/history.jsonl`, `tools/gate.py`) and says whether the parent need run it
again in the main tree (rules/process.md 8.5; `work_check_line`). Its third line is the auto
sweep of the main tree (`gate_runs.auto_line`, `tools/after_commit.py`). Its fourth line,
`fuzz inputs: …`, says which inputs the fuzzing of the worktree kept (`fuzz.new_inputs`:
`<target>/fuzz/new/*.onsa`, named by the hash of the text) it copied into the main tree's,
those of a name not there yet, so that they are not lost with the worktree (X-1 U8;
`copy_fuzz_inputs`); a failure to copy does not fail the patch.

`check` (`--to`, default this repository) says whether `git apply --check`
passes, else whether `git apply --check -3` does (and whether with
conflicts; or that the patch is already there: its reverse applies), and lists the files of the patch that have uncommitted changes
or are untracked in the tree. `apply` applies the patch the way `check`
found; after `-3` it runs `git restore --staged` on the files of the patch,
so nothing of it stays in the index. It prints the applied files.

`done` (one worktree), `close` (all the worktrees directly under WORKTREES and the BRANCH_PREFIX branches no
worktree checks out) and `remove` (the hook WorktreeRemove) pass one verdict (`judge`), the first that holds:
a live agent's stays (Claude Code's record `subagents/agent-<ID>.meta.json` names its path or branch and has no
`finished`, or Claude Code's lock `LIVE_LOCK` is on it; with `--session`, only that session's records count,
and a session with none keeps all; a record that cannot be read or is not of the form known keeps it); with no
change it goes and its branch, checked to be in dev (no commit after dev, and what it holds, untracked files
too, is its HEAD's tree); taken, it goes with `-D` (TAKEN has the patch of what it holds and then its apply to
the main tree, or its patch from the base applies in reverse in the main tree); else it stays, with the files
changed and the commits after dev. One that would go with ignored files outside `target/` stays too. Before a
removal: the registrations of a directory gone are pruned, the saved reports of its agents looked for under
`--scratchpad` (a line when none, and one for each with no body, `handback.no_body`; not looked for without
it), its fuzzing inputs copied (a failure keeps it), what it holds read again (changed after the verdict: it
stays), its lock taken off. Only a BRANCH_PREFIX branch it checked out goes, with the hash of its tip
printed; dev, main and the main tree never. `done --discard` removes a changed one too (or one with ignored
files, listed), after writing its last patch from the base under `<main>/DISCARDED`. `close --dry-run`
removes and prunes nothing. `done` and `remove` exit 1 when it stays (`remove` with the reason on stderr; 0
when neither the worktree nor its branch is there); `close` exits 1 when a removal failed. Claude Code's
records are under `$ONSA_CLAUDE_RECORDS` (`RECORDS_ENV`), else `handback.PROJECT`.

`sync` (an agent, in its worktree `--tree`, default the tree of this tool; X9-14) does nothing and exits 1 in
the main tree, out of a git tree, on no branch or in a merge (MERGE_HEAD). Else: when DEV is in HEAD, nothing is
to take in; when the branch has no commit after DEV and no uncommitted change (untracked files too), `git merge
--ff-only dev`; else a WIP commit of all (`add -A`; the subject `-m`, default SYNC_WIP) when there are changes,
then `git merge --no-edit dev`, which stops in the merge on a conflict, the files listed, exit 1 (the agent
resolves them: rules/common.md 2.2). Then `--apply` checks and applies the patch the way `check` and `apply` do
(recorded alike) and commits its files alone (`-m`, default APPLY_WIP); one already there does nothing; one with
uncommitted changes in its files is not applied; one that does not apply, or applies 3-way with conflicts, is not
committed (exit 1). Last, a line: the branch, HEAD and DEV, the commits after DEV, the commits of DEV taken in,
the uncommitted changes. git runs inside the command (no shell chains: rules/common.md 1.7), no editor opened.

`lines` (an agent, in its tree `--tree`, default the tree of this tool; X9-20, X-17) prints the lines of what the
tree holds (uncommitted changes and untracked files too) from a base (`--base`): in a worktree by default the base
`take` takes (`base_of`; an agent who took over a unit passes the WIP commit of the unit before: rules/common.md
2.4), in the main tree by default HEAD (an agent there commits nothing: rules/common.md 2.3). It counts them as
`patch` counts them (`staged_diff`, `summary`: the same lines, the index left empty alike), and with `--estimate N`
prints the line `estimate: …` of `take`. It does nothing and exits 1 out of a git tree or in a merge (`in_merge`:
the `add -A` and `reset` of `staged_diff` would end it); `patch` (and so `take`) stops alike in a worktree in a
merge.

`commit` (the parent, in the main tree `--tree`; X9-17) commits the named paths alone, as they are now (untracked
files and removals too; `git commit --only`): the changes of the other paths and the index stay. A named path
with no change is listed; with none at all, nothing is committed (exit 1). The message is the `-m` paragraphs and
then `-F`'s. `--done ID` writes `status=DONE` the way `docs.py set` does (the swap files checked) and adds its
file to the paths. `--docs-checked A..B WORK` (both ends commits of the tree: the range checked, the HEAD of then at both ends
for an uncommitted diff) writes the trailer
`<docs.DOCS_CHECKED>: A..B (WORK, onsa-docs)`, the ends as short hashes (X-12), and checks after the commit that `docs.last_docs_check` reads it,
a line when not; `--co-author` writes `Co-Authored-By:` after it. When the commit fails, the untracked files
it added to the index leave it and the file of `--done` gets back what it held. Then a line: the commit, the
branch, its files, the uncommitted changes not in it. Last, the line `auto sweep: …` of what it started in the
main tree (`after_commit.on_commit`): the sweep after a commit of the code or the cases, with `--no-sweep` the
base binaries alone after a commit of the code, else nothing (exit 1 when it cannot ask: the commit stays).

But for the worktree `new` makes, the removals above, `sync` and `commit`, nothing here commits, stashes, resets
the tree or checks paths out. Exit 0 on success, 1 when a step fails, the patch does not apply or `take` stops
before applying, 2 on a usage error.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import NamedTuple

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import after_commit  # noqa: E402
import docs  # noqa: E402
import fuzz  # noqa: E402
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import handback  # noqa: E402
import narrowing  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
DEV = "dev"  # the branch a worktree starts from and is taken against
WORKTREES = Path(".claude") / "worktrees"  # of the main tree; Claude Code's own are there too
BRANCH_PREFIX = "worktree-"  # Claude Code's own form, so that the cleaning up treats both alike
NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")  # a slug of WorktreeCreate (`bold-oak-a3f2`, `agent-<ID>`)
TAKEN = Path("target") / "work" / "taken.jsonl"  # the record of the patches and the applies, in the main tree
DISCARDED = Path("target") / "work" / "discarded"  # the last patches of the worktrees `done --discard` removed
RECORDS_ENV = "ONSA_CLAUDE_RECORDS"  # Claude Code's records of the sessions, if not handback.PROJECT (self-tests)
REGISTRIES = ("tools/builtin_names.toml", "tests/pending.toml")  # the hunks `take` shows (rules/leader.md 4.1)
PENDING = "tests/pending.toml"
REFACTOR = "リファクタリングに入る大きさ"  # the row of rules/budgets.md: 「… 見積もりの N 倍を超え、かつ差が M 行以上」
REFACTOR_FORM = re.compile(r"(\d+)\s*倍を超え.*?差が\s*(\d+)\s*行以上")  # (ratio, lines): over ratio times and lines more
AGAIN = "work check: run it again in the main tree"
CODE_SUFFIXES = (".rs", ".py", ".sh", ".c", ".h", ".js")
ALREADY = "already in the tree (its reverse applies); nothing to do"


class Failed(Exception):
    pass


def is_code(path):
    return path.endswith(CODE_SUFFIXES) and not repo.is_test_file(path)


HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def in_file_tests(tree, base, paths):
    """{path: [added, removed]}: the lines of the diff of the index of `tree` from `base`
    in the files `paths` that are in a test module of the file (`repo.test_lines`)."""
    out = {}
    if not paths:
        return out
    show = lambda rev: git(tree, "show", rev).stdout.decode(errors="replace")  # noqa: E731
    old = counts = None
    old_tests = new_tests = set()
    for line in git(tree, "diff", "--cached", "-U0", base, "--", *paths).stdout.decode(errors="replace").split("\n"):
        if line.startswith("--- "):
            old = line[6:] if line.startswith("--- a/") else None
        elif line.startswith("+++ "):
            new = line[6:] if line.startswith("+++ b/") else None
            old_tests = repo.test_lines(show(f"{base}:{old}")) if old else set()
            new_tests = repo.test_lines(show(f":{new}")) if new else set()
            counts = out.setdefault(new or old, [0, 0])
        elif line.startswith("@@ ") and counts is not None:
            m = HUNK.match(line)
            a, b = int(m[1]), int(m[2]) if m[2] is not None else 1
            c, d = int(m[3]), int(m[4]) if m[4] is not None else 1
            counts[0] += sum(k in new_tests for k in range(c, c + d))
            counts[1] += sum(k in old_tests for k in range(a, a + b))
    return out


def git(tree, *args, ok=(0,), input=None):
    r = subprocess.run(["git", "-C", str(tree), *args], capture_output=True, input=input)
    if r.returncode not in ok:
        raise Failed(f"git {' '.join(args)}: exit {r.returncode}: {r.stderr.decode(errors='replace').strip()}")
    return r


def numstat(tree, *args):
    """[(added, removed, path)] of `git <args> --numstat -z` (`-` for a binary file)."""
    fields, out = git(tree, *args, "--numstat", "-z").stdout.decode().split("\0"), []
    i = 0
    while i < len(fields) - 1:
        add, rm, path = fields[i].split("\t", 2)
        if path:
            i += 1
        else:  # a rename: the old and the new path follow
            path, i = fields[i + 2], i + 3
        out.append((add, rm, path))
    return out


def summary(stats, new, inner=None):
    """Print the lines per file and the totals; `inner` is `in_file_tests` of the code files. The lines added
    and removed without the tests and the data."""
    total, code = [0, 0], [0, 0]
    for add, rm, path in stats:
        print(f"  {add:>6} {rm:>6}  {path}{'  (new)' if path in new else ''}")
        for acc in (total, code) if is_code(path) else (total,):
            acc[0] += int(add) if add != "-" else 0
            acc[1] += int(rm) if rm != "-" else 0
    left = [sum(v[k] for v in (inner or {}).values()) for k in (0, 1)]
    files = sum(1 for v in (inner or {}).values() if any(v))
    note = f" (the test modules inside {files} file(s), +{left[0]} -{left[1]}, left out)" if files else ""
    print(f"  {len(stats)} file(s), +{total[0]} -{total[1]}; "
          f"without the tests and the data: +{code[0] - left[0]} -{code[1] - left[1]}{note}")
    return code[0] - left[0], code[1] - left[1]


def staged_diff(wt, base):
    """(the binary diff, `numstat`, the new files, `in_file_tests` of the Rust code) of all `wt` holds from `base`
    (`add -A`: untracked files too; the index is left empty): what `patch` writes and counts, and `lines` counts.
    It stops when `base` is not an ancestor of the HEAD."""
    if git(wt, "merge-base", "--is-ancestor", base, "HEAD", ok=(0, 1)).returncode:
        raise Failed(f"{base} is not an ancestor of the HEAD of {wt}")
    git(wt, "add", "-A")
    try:
        diff = git(wt, "diff", "--cached", "--binary", base).stdout
        stats = numstat(wt, "diff", "--cached", base)
        new = set(git(wt, "diff", "--cached", "--name-only", "--diff-filter=A", "-z", base).stdout.decode().split("\0"))
        inner = in_file_tests(wt, base, [p for _, _, p in stats if p.endswith(".rs") and is_code(p)])
    finally:
        git(wt, "reset", "-q")
    return diff, stats, new, inner


def patch(wt, base, out, main):
    """Make the patch and print its lines (the command `patch`); (the line `work check: …`, the lines added and
    removed without the tests and the data)."""
    wt = Path(wt)
    why = in_merge(wt)
    if why:
        raise Failed(f"patch: {wt}: {why}; nothing done")
    diff, stats, new, inner = staged_diff(wt, base)
    Path(out).write_bytes(diff)
    print(f"{out}: the patch of {wt} from {base}")
    line = work_check_line(wt, main, base, out)
    print(line)
    try:
        print(gate_runs.auto_line(main, gate_runs.read_history(main)[0], gate_steps.SHARDS))
    except OSError as e:
        print(f"auto sweep: cannot read the history of the main tree ({e})")
    print(copy_fuzz_inputs(wt, main))
    code = summary(stats, new, inner)
    head = git(main, "rev-parse", "HEAD").stdout.decode().strip()
    if git(main, "rev-parse", base).stdout.decode().strip() != head:
        moved = set(git(main, "diff", "--name-only", "-z", base, head).stdout.decode().split("\0")) - {""}
        both = sorted(moved & {p for _, _, p in stats})
        print(f"the main tree ({head[:9]}) differs from {base} in {len(moved)} file(s); of the patch: "
              + (", ".join(both) if both else "none"))
    record(main, "patch", lambda: {
        "worktree": str(wt.resolve()), "branch": git(wt, "rev-parse", "--abbrev-ref", "HEAD").stdout.decode().strip(),
        "base": git(wt, "rev-parse", base).stdout.decode().strip(), "tree": repo.tree_hash(wt),
        "patch": str(Path(out).resolve())})  # fmt: skip
    return line, code


def record(tree, kind, fields):
    """Add `{"time", "kind", **fields()}` to `TAKEN` of the main tree of `tree`; a line when it cannot."""
    try:
        row = {"time": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "kind": kind, **fields()}
        path = (repo.main_tree(tree) or Path(tree)) / TAKEN
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except (OSError, repo.RepoError, Failed) as e:
        print(f"record: the {kind} is not in {TAKEN} ({e})")


def copy_fuzz_inputs(wt, main, strict=False):
    """Copy the inputs the fuzzing of the worktree kept into the main tree's directory, those of a name
    not there yet (a name is the hash of the text, so one there is the same input: never overwritten);
    the line that says what it did. `strict`: a failure to copy raises Failed (the worktree is not removed)."""
    src, dest, done = fuzz.new_inputs(wt), fuzz.new_inputs(main), []
    try:
        names = sorted(p.name for p in src.glob("*.onsa"))
        if names and src.resolve() == dest.resolve():
            return f"fuzz inputs: {len(names)} in {dest}/, which the worktree shares with the main tree; none copied"
        if not names:
            return "fuzz inputs: none in the worktree"
        dest.mkdir(parents=True, exist_ok=True)
        for name in names:
            if not (dest / name).exists():
                shutil.copyfile(src / name, dest / name)
                done.append(name)
    except OSError as e:
        line = f"fuzz inputs: {len(done)} copied into {dest}/, then the copy failed ({e})"
        if strict:
            raise Failed(f"{line}; the worktree is not removed") from None
        return line
    if not done:
        return f"fuzz inputs: {len(names)} in the worktree, all in the main tree already"
    return f"fuzz inputs: {len(done)} copied from the worktree into {dest}/: {', '.join(done)}"


def work_check_line(wt, main, base, patch_file):
    """Whether the parent need run the work check again after the patch: the last `work` run of the
    worktree passed on the tree of the patch, the patch applies plain to files with no change, and the
    main tree moved from the base in no file of the code and the cases (`narrowing.SWEPT`). When only
    the files outside them moved, in the main tree or in the worktree after the check (its `code_tree`,
    X-1 U5), `--only static` does."""
    try:
        rows, tree, code_tree = gate_runs.read_history(wt)[0], repo.tree_hash(wt), repo.tree_hash(wt, narrowing.SWEPT)
        head = git(main, "rev-parse", "HEAD").stdout.decode().strip()
        base = git(main, "rev-parse", base).stdout.decode().strip()
        moved = [p for p in git(main, "diff", "--name-only", "-z", base, head).stdout.decode().split("\0") if p]
        code = [p for p in git(main, "diff", "--name-only", "-z", base, head, "--", *narrowing.SWEPT)
                .stdout.decode().split("\0") if p]  # fmt: skip
    except (OSError, repo.RepoError, Failed) as e:
        return f"{AGAIN}: cannot tell ({e})"
    works = [r for r in rows if str(r.get("form", "")).startswith("work ")]
    missing, last, why = [], works[-1] if works else None, []
    if last is None:
        quick = any(r.get("form") == "quick" for r in rows)
        missing.append("no work check in the worktree" + (" (only --quick)" if quick else ""))
    else:
        if last.get("verdict") != "PASS":
            bad = [n for n, v in last.get("items", {}).items() if v[:1] == ["FAIL"]]
            missing.append(f"the last work check failed ({last.get('form')}: {', '.join(bad)})")
        if last.get("tree") is None:
            missing.append("the tree changed during the check (or could not be read)")
        elif last["tree"] != tree and last.get("code_tree") == code_tree:
            why.append("the worktree changed outside the code and the cases after the check")
        elif last["tree"] != tree:
            missing.append("the tree changed after the check")
    if code:
        missing.append(f"the main tree moved in the code or the cases after the base ({', '.join(code[:3])})")
    try:
        how, _, notes = check(patch_file, main)
    except Failed:
        how, notes = "not at all", []
    if how != "plain":
        missing.append(f"the patch applies {how}")
    if notes:
        missing.append("the main tree has uncommitted changes in the files of the patch")
    if missing:
        return f"{AGAIN}: " + "; ".join(missing)
    did = f"{last['form']} PASS at {last.get('time')} on " + ("its code and cases" if why else "the tree of the patch")
    if moved:
        why.append(f"the main tree moved in {len(moved)} file(s) outside the code and the cases after the base "
                   f"{base[:7]}")  # fmt: skip
    if not why:
        return f"work check: no need to run it again ({did}; base = the main tree's HEAD; applies plain)"
    return ("work check: no need to run the heavy items again; run tools/gate.sh --only static ("
            + "; ".join([*why, did]) + ")")


def paths_of(tree, patch_file):
    return [p for _, _, p in numstat(tree, "apply", str(Path(patch_file).resolve()))]


def applies_in_reverse(to, *patch, input=None):
    """Whether the patch (a file, or `input`) is in the tree `to` already: its reverse applies (`check`, `judge`)."""
    return git(to, "apply", "--check", "-R", *patch, ok=(0, 1), input=input).returncode == 0


def check(patch_file, to):
    """("plain" | ALREADY | "3way" | "3way with conflicts", the files of the patch, problems of the tree)."""
    p = str(Path(patch_file).resolve())
    paths = paths_of(to, p)
    status = git(to, "status", "--porcelain=v1", "-z", "--", *paths).stdout.decode().split("\0")
    notes, i = [], 0
    while i < len(status) - 1:
        code, path = status[i][:2], status[i][3:]
        notes.append(f"{path}: {'untracked, already there' if code == '??' else f'uncommitted change ({code.strip()})'}")
        i += 2 if code[0] in "RC" else 1
    if git(to, "apply", "--check", p, ok=(0, 1)).returncode == 0:
        return "plain", paths, notes
    if applies_in_reverse(to, p):
        return ALREADY, paths, notes
    r = git(to, "apply", "--check", "-3", p, ok=(0, 1))
    err = r.stderr.decode(errors="replace")
    if r.returncode:
        raise Failed("\n".join([f"the patch does not apply, plain nor with -3:\n{err.strip()}", *notes]))
    return ("3way with conflicts" if "with conflicts" in err else "3way"), paths, notes


PATCH_EPILOG = """\
The second line compares the last work check of the worktree (tools/gate.sh --work, kept in
its target/gate/history.jsonl) with the patch and the main tree:
  work check: no need to run it again (...)            take the patch in without the gate
  work check: no need to run the heavy items again; run tools/gate.sh --only static (...)
                                                       the main tree moved outside the code and the cases
                                                       after the base, or the worktree after the check
  work check: run it again in the main tree: <what is missing>
                                                       no work check, only --quick, a failure, the code or
                                                       the cases of the worktree changed after it (or a
                                                       check before X-1 U5, which kept the whole tree only),
                                                       the main tree moved in the code
The third line, `auto sweep: …`, is the sweep a commit of the main tree starts (tools/after_commit.py
--help): read it before taking the patch in; FAILED points to the output of the sweep.
The fourth line, `fuzz inputs: …`, copies the inputs the fuzzing of the worktree kept for its new
classes (<target>/fuzz/new/*.onsa) into the main tree's, so that removing the worktree loses none:
  fuzz inputs: 2 copied from the worktree into <main>/target/fuzz/new/: 1a2b3c4d.onsa, 5e6f7a8b.onsa
  fuzz inputs: none in the worktree
  fuzz inputs: 3 in the worktree, all in the main tree already
                                                       nothing to copy (a name there is the same input)
  fuzz inputs: 3 in <dir>/, which the worktree shares with the main tree; none copied
                                                       one CARGO_TARGET_DIR for both
  fuzz inputs: 1 copied into <dir>/, then the copy failed (...)
                                                       the patch is made all the same
The parent sorts them later; nothing is written under tests/fuzz/.
example: tools/work.py patch .claude/worktrees/x1 2ce980a /tmp/x1.patch"""


def apply_patch(patch_file, to, how, paths):
    """Apply the patch the way `check` found (`how`, not ALREADY), print what it did and record it; (the exit,
    the files with conflicts)."""
    r = git(to, "apply", *(["-3"] if how != "plain" else []), str(Path(patch_file).resolve()), ok=(0, 1))
    conflicts = listed(to, "diff", "--name-only", "--diff-filter=U") if how != "plain" else []
    if how != "plain":
        git(to, "restore", "--staged", "--", *paths)
    print(r.stderr.decode(errors="replace").strip() or "applied")
    for path in paths:
        print(f"  {path}")
    if r.returncode == 0:
        record(to, "apply", lambda: {"patch": str(Path(patch_file).resolve()), "to": str(Path(to).resolve()),
                                     "head": git(to, "rev-parse", "HEAD").stdout.decode().strip()})  # fmt: skip
    return r.returncode, conflicts


def listed(tree, *args):
    """The paths `git <command> -z <the rest>` prints (`-z` before a `--`)."""
    return [p for p in git(tree, args[0], "-z", *args[1:]).stdout.decode().split("\0") if p]


def checked(patch_file, to):
    """`check`, printed: (how, the files of the patch, the problems of the tree)."""
    how, paths, notes = check(patch_file, to)
    print(f"applies: {how}")
    for n in notes:
        print(f"  {n}")
    return how, paths, notes


def branch_of(name):
    """The branch of the worktree `name` (`new` makes it; the cleaning up removes only these)."""
    return BRANCH_PREFIX + name


def new(name, where):
    """Make the worktree `name` of the main tree of `where` on `branch_of(name)` from DEV; its path."""
    main = repo.main_tree(where)
    if main is None:
        raise Failed(f"{where} is not the top of a git tree")
    if not NAME.fullmatch(name) or ".." in name or name.endswith(".lock"):
        raise Failed(f"{name!r} is not the name of a worktree (letters, digits, `.`, `_` and `-`)")
    path, branch = main / WORKTREES / name, branch_of(name)
    git(main, "worktree", "prune")
    if git(main, "rev-parse", "--verify", "--quiet", f"refs/heads/{branch}", ok=(0, 1)).returncode == 0:
        raise Failed(f"the branch {branch} is there already (an old one is not taken again; remove it or use "
                     "another name)")  # fmt: skip
    if path.exists() or path.is_symlink():
        raise Failed(f"{path} is there already")
    git(main, "worktree", "add", "-q", "-b", branch, str(path), DEV)
    return path


def hunks_of(text, path):
    """The lines of the hunks of `path` in the patch `text`, from its first `@@` on."""
    out, inside = [], False
    for line in text.split("\n"):
        if line.startswith("diff --git "):
            inside = line == f"diff --git a/{path} b/{path}"
        elif inside and (out or line.startswith("@@")):
            out.append(line)
    while out and out[-1] == "":
        out.pop()
    return out


def refactor_size(root):
    """(ratio, lines) of the row REFACTOR of rules/budgets.md in the tree `root`, or (a str) why not."""
    try:
        m = REFACTOR_FORM.search(repo.budget_value(root, REFACTOR))
    except repo.RepoError as e:
        return str(e)
    return (int(m[1]), int(m[2])) if m else f"{repo.BUDGETS}: the row 「{REFACTOR}」 says no 「N 倍を超え、かつ差が M 行以上」"


def estimate_line(lines, estimate, root):
    head = (f"estimate: +{lines} of the code (without the tests and the data) against {estimate}: "
            f"{lines / estimate:.2f} times; ")
    size = refactor_size(root)
    if isinstance(size, str):
        return head + f"not judged against the size to refactor ({size})"
    ratio, diff = size
    over = lines > ratio * estimate and lines - estimate >= diff
    return (head + ("over" if over else "within")
            + f" the size to refactor ({repo.BUDGETS}: over {ratio} times and {diff} lines more)")


def fresh(directory, name):
    """`<directory>/<name>-<time>.patch`, with `~N` when there already (two in one second: the record keeps each)."""
    stem, n = f"{name}-{time.strftime('%Y%m%d-%H%M%S')}", 1
    out = directory / f"{stem}.patch"
    while out.exists():
        n += 1
        out = out.with_name(f"{stem}~{n}.patch")
    return out


def place(main, worktree):
    """The worktree `worktree` names: a path that is a directory, else a name under WORKTREES of the main tree."""
    wt = Path(worktree)
    return wt if wt.is_dir() else (repo.main_tree(main) or Path(main)) / WORKTREES / worktree


def base_of(tree):
    """The base of the work of a worktree: `git merge-base DEV HEAD` (`take`, `lines`)."""
    return git(tree, "merge-base", DEV, "HEAD").stdout.decode().strip()


def take(args):
    main = Path(args.main)
    wt = place(main, args.worktree)
    if not wt.is_dir():
        raise Failed(f"no worktree {args.worktree} (a path, or a name under {WORKTREES}/ of the main tree)")
    base = args.base or base_of(wt)
    out = Path(args.out) if args.out else fresh(main / "target" / "work", wt.name)
    out.parent.mkdir(parents=True, exist_ok=True)
    line, code = patch(wt, base, out, main)
    text = out.read_bytes().decode(errors="replace")
    for path in REGISTRIES:
        hunks = hunks_of(text, path)
        if hunks:
            print(f"the hunks of {path}:", *hunks, sep="\n")
    if args.estimate:
        print(estimate_line(code[0], args.estimate, main))
    how, paths, notes = checked(out, main)
    if how.startswith("3way") and PENDING in paths:
        print(f"{PENDING} is in a patch that applies 3-way: rebuild it from dev's version (rules/leader.md 3.4)")
    if how == ALREADY:
        return 0
    why = [w for w, bad in ((f"it applies {how}", how != "plain"),
                            ("the main tree has uncommitted changes in the files of the patch", notes),
                            ("the work check is to run again", line.startswith(AGAIN))) if bad]  # fmt: skip
    if why and not args.go:
        print(f"take: not applied ({'; '.join(why)}); read the above, then apply it with --go")
        return 1
    return apply_patch(out, main, how, paths)[0]


# ---------------------------------------------------------------- the cleaning up (X9-16, U5)

LIVE_LOCK = "claude agent"  # the start of the reason of Claude Code's lock while its agent runs (seen 2026-10-18)
# The fields of a record that name the path of its worktree: its own, or that of the agent that spawned it in its
# worktree (an agent of an agent, `spawnDepth` 2; seen 2026-10-25).
TREE_PATHS = ("worktreePath", "inheritedWorktreePath")
META_TEXT = ("agentType", *TREE_PATHS, "worktreeBranch")  # the fields of a record that are strings when there
TAKEN_TEXT = {"patch": ("patch", "worktree", "branch", "tree"), "apply": ("patch", "to")}  # the rows `take` writes
BUILD = "target/"  # the build output: its fuzzing inputs are copied, the rest of it goes with the worktree


class Unreadable(Exception):
    pass


class Entry(NamedTuple):
    """A worktree to clean up (its path resolved, its branch, the reason of its lock: None when not locked), or a
    branch alone (`path` None)."""

    path: "Path | None"
    branch: "str | None"
    lock: "str | None" = None


class Verdict(NamedTuple):
    """What the cleaning up does with a worktree or a branch: `kind` (live, clean, taken, ignored, changed,
    unknown), `why`, `flag` (`-d`: its branch goes when in dev; `-D`: it goes; None: it stays), `agents`
    [(agent_type, agent_id)] of the records that name it (for the check of the saved reports), `state` (`state`
    when judged: a removal reads it again and stops when it changed)."""

    kind: str
    why: str
    flag: "str | None"
    agents: tuple = ()
    state: tuple = ()


def agents_of(path, branch, session):
    """[(agent_type, agent_id, live)] of Claude Code's records `<RECORDS_ENV or handback.PROJECT>/<session>/
    subagents/agent-<ID>.meta.json` whose path (a field of TREE_PATHS) is `path` or `worktreeBranch` is `branch`;
    live when it has no `finished`. With `session`, that session's alone (another session's agents cannot be
    called again: finished), and none of them is unreadable (a wrong ID would make every agent finished); without,
    all of them.
    The form is not in Claude Code's documents (checked on 2026-10-18): a record that cannot be read, a field of
    META_TEXT not a string, `finished` not a boolean, or one spawned with a worktree that names neither a path nor
    its branch raises Unreadable, and the worktree stays."""
    top = Path(os.environ.get(RECORDS_ENV) or handback.PROJECT)
    if not top.is_dir():
        raise Unreadable(f"no records of Claude Code in {top} (${RECORDS_ENV})")
    metas, out = sorted(top.glob(f"{session or '*'}/subagents/agent-*.meta.json")), []
    if session and not metas:
        raise Unreadable(f"no record of the session {session} in {top}")
    for meta in metas:
        try:
            d = json.loads(meta.read_text(encoding="utf-8"))
        except (OSError, ValueError) as e:
            raise Unreadable(f"the record {meta} cannot be read ({e})") from None
        if not isinstance(d, dict) or not isinstance(d.get("finished", False), bool) or any(
                k in d and not isinstance(d[k], str) for k in META_TEXT):  # fmt: skip
            raise Unreadable(f"the record {meta} is not of the form known")
        paths = [d[k] for k in TREE_PATHS if d.get(k)]
        if d.get("spawnedWithWorktree") and not (paths or d.get("worktreeBranch")):
            raise Unreadable(f"the record {meta} names no worktree, though spawned with one")
        if (path and any(Path(p).resolve() == path for p in paths)) or (branch and d.get("worktreeBranch") == branch):
            out.append((d.get("agentType"), meta.name[len("agent-"): -len(".meta.json")], not d.get("finished")))
    return out


def taken_trees(main):
    """{(worktree, branch, tree): the patch} of the `patch` rows of TAKEN that an `apply` to the main tree follows
    before the next patch to the same file (only an apply to the main tree is taken). A line that is not such a row
    (TAKEN_TEXT not all strings), or a record that cannot be read, takes nothing: the worktree stays."""
    last, out = {}, {}
    try:
        lines = (main / TAKEN).read_text(encoding="utf-8").splitlines()
    except (OSError, ValueError):
        return out
    for line in lines:
        try:
            row = json.loads(line)
        except ValueError:
            continue
        keys = TAKEN_TEXT.get(row.get("kind")) if isinstance(row, dict) else None
        if keys is None or not all(isinstance(row.get(k), str) for k in keys):
            continue
        if row["kind"] == "patch":
            last[row["patch"]] = row
        elif row["to"] == str(main) and row["patch"] in last:
            p = last.pop(row["patch"])
            out[(p["worktree"], p["branch"], p["tree"])] = p["patch"]
    return out


def sha(main, rev):
    return git(main, "rev-parse", "--verify", "--end-of-options", rev).stdout.decode().strip()


def state(main, e):
    """(HEAD, the git tree of what it holds: `repo.tree_hash`, untracked files too, the ignored files and
    directories outside BUILD) of the worktree of `e`; of its branch alone, (its tip, its tree, ())."""
    if e.path:
        listed = git(e.path, "ls-files", "-z", "-o", "-i", "--exclude-standard", "--directory").stdout.decode()
        ignored = tuple(p for p in listed.split("\0") if p and not p.startswith(BUILD))
        return git(e.path, "rev-parse", "HEAD").stdout.decode().strip(), repo.tree_hash(e.path), ignored
    head = sha(main, f"refs/heads/{e.branch}")
    return head, sha(main, f"{head}^{{tree}}"), ()


def from_base(main, head, tree):
    """(the base `git merge-base DEV <head>`, the patch from it to `tree`, untracked files and binaries too)."""
    base = git(main, "merge-base", DEV, head).stdout.decode().strip()
    return base, git(main, "diff", "--binary", base, tree).stdout


def judge(main, e, session):
    """The one verdict of `done`, `close` and `remove` on the worktree of `e` (or its branch alone, the directory
    gone; no branch: detached), the first of: a live agent's (stays: a record not finished, or Claude Code's lock
    LIVE_LOCK); no change: no commit after DEV and what it holds (`state`) is its HEAD's tree (goes, `-d`); taken:
    TAKEN has the patch of what it holds and its apply to the main tree, or its patch from the base applies in
    reverse in the main tree (goes, `-D`); else changed (stays, with the files and the commits). One that would go
    with ignored files outside BUILD stays (`ignored`)."""
    try:
        agents = agents_of(e.path, e.branch, session)
    except Unreadable as x:
        return Verdict("unknown", str(x), None)
    named = tuple((t, i) for t, i, _ in agents if t)
    live = [f"{t or 'agent'} {i}" for t, i, alive in agents if alive]
    if e.lock is not None and e.lock.startswith(LIVE_LOCK):
        live.append(f"locked: {e.lock}")
    if live:
        return Verdict("live", f"the agent is running ({', '.join(live)})", None, named)
    try:
        now = head, tree, ignored = state(main, e)
        ahead = int(git(main, "rev-list", "--count", f"{DEV}..{head}").stdout)
        patch = next((p for (w, b, t), p in taken_trees(main).items()
                      if (w == str(e.path) if e.path else b == e.branch) and t == tree), None)  # fmt: skip
        if ahead == 0 and tree == sha(main, f"{head}^{{tree}}"):
            v = ("clean", f"no change (no commit after {DEV}, the tree is its HEAD's)", "-d")
        elif patch:
            v = ("taken", f"taken (the patch {patch} of this tree and its apply to the main tree are in {TAKEN})", "-D")
        else:
            base, diff = from_base(main, head, tree)
            if diff and applies_in_reverse(main, input=diff):
                v = ("taken", "taken (its patch from the base applies in reverse in the main tree)", "-D")
            else:
                files = len(numstat(main, "diff", base, tree))
                v = ("changed", f"not taken: {files} file(s) changed from the base, {ahead} commit(s) after {DEV}", None)
    except (Failed, repo.RepoError, ValueError) as x:
        return Verdict("unknown", f"cannot tell ({x})", None, named)
    if ignored and v[2]:
        shown = ", ".join(ignored[:3]) + (", …" if len(ignored) > 3 else "")
        v = ("ignored", f"{v[1]}; but {len(ignored)} ignored file(s) outside {BUILD} would go with it: {shown}", None)
    return Verdict(*v, named, now)


def main_of(where):
    main = repo.main_tree(where)
    if main is None:
        raise Failed(f"{where} is not the top of a git tree")
    return main.resolve()


def entries(main, dry):
    """The worktrees directly under WORKTREES of the main tree, and the BRANCH_PREFIX branches no worktree checks
    out. The registrations of a directory gone are pruned first (a lock taken off); with `dry`, nothing is, and
    their branches count as free."""
    def listed():
        out = []
        for block in git(main, "worktree", "list", "--porcelain", "-z").stdout.decode().split("\0\0"):
            d = dict(line.partition(" ")[::2] for line in block.split("\0") if line)
            if "worktree" in d:
                branch = d["branch"].removeprefix("refs/heads/") if "branch" in d else None
                out.append(Entry(Path(d["worktree"]).resolve(), branch, d.get("locked")))
        return out

    if not dry:
        for e in listed():
            if e.lock is not None and not e.path.is_dir() and e.path.parent == main / WORKTREES:
                git(main, "worktree", "unlock", str(e.path))
        git(main, "worktree", "prune")
    trees = [e for e in listed() if e.path.is_dir()]
    held = {e.branch for e in trees}
    heads = git(main, "for-each-ref", "--format=%(refname)", "refs/heads/").stdout.decode().split("\n")
    free = [h.removeprefix("refs/heads/") for h in heads if h.startswith(f"refs/heads/{BRANCH_PREFIX}")]
    return [e for e in trees if e.path.parent == main / WORKTREES] + [Entry(None, b) for b in free if b not in held]


def let_go(main, e, v, force):
    """Remove the worktree of `e` and then its branch when BRANCH_PREFIX (never DEV nor `main`), its tip printed.
    Before anything goes: a branch of `-d` is checked to be in DEV, the fuzzing inputs copied (a failure stops it),
    and `state` read again (changed after the verdict: it stays); then the lock is taken off."""
    branch = e.branch if e.branch and e.branch.startswith(BRANCH_PREFIX) and e.branch not in (DEV, "main") else None
    if branch and v.flag == "-d" and git(main, "merge-base", "--is-ancestor", f"refs/heads/{branch}", DEV,
                                         ok=(0, 1)).returncode:  # fmt: skip
        raise Failed(f"the branch {branch} is not in {DEV} any more; nothing removed")
    if e.path:
        print("  " + copy_fuzz_inputs(e.path, main, strict=True))
    if state(main, e) != v.state:
        raise Failed(f"{e.path or e.branch} changed after the verdict; nothing removed")
    if e.path:
        if e.lock is not None:
            git(main, "worktree", "unlock", str(e.path))
        git(main, "worktree", "remove", *(["--force"] if force else []), str(e.path))
        print(f"  removed {e.path}")
    if branch:
        tip = sha(main, f"refs/heads/{branch}")
        git(main, "branch", "-q", "-D", branch)
        print(f"  removed the branch {branch} ({'in ' + DEV if v.flag == '-d' else '-D'}; its tip was {tip})")
    elif e.branch:
        print(f"  kept the branch {e.branch} (only {BRANCH_PREFIX}… go)")


def settle(main, e, args, discard=False, dry=False, err=False):
    """Judge `e` (`judge`), say it, and remove it when the verdict lets it go (`discard`: when changed or with
    ignored files too, after writing its patch from the base under DISCARDED and listing those files); whether it
    went (with `dry`, would go). The line of a kept one goes to stderr with `err`."""
    v = judge(main, e, args.session)
    go = bool(v.flag) or (discard and v.kind in ("changed", "ignored"))
    name = e.path.name if e.path else e.branch
    line = f"{'would remove' if dry and go else 'remove' if go else 'keep'} {name}" + (
        f" ({e.branch})" if e.path and e.branch else "") + f": {v.why}"  # fmt: skip
    print(line, file=sys.stderr if err and not go else sys.stdout)
    if not go:
        return False
    if args.scratchpad is None:
        print("  reports: not checked (no --scratchpad)")
    for kind, agent in v.agents if args.scratchpad else ():
        found = sorted((Path(args.scratchpad) / handback.REPORTS).glob(handback.report_prefix(kind, agent) + "*.md"))
        if not found:
            print(f"  reports: none saved for {kind} {agent} in {args.scratchpad}/{handback.REPORTS}/")
        for p in filter(handback.no_body, found):  # the hook's "no body": not saved (rules/leader.md 2.9)
            print(f"  reports: no body in {p} for {kind} {agent}: take it out with the command in it")
    if dry:
        return True
    if not v.flag:  # discarded: its last patch first, and the ignored files that go with it
        out = fresh(main / DISCARDED, name)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(from_base(main, *v.state[:2])[1])
        print(f"  the patch from the base: {out}")
        if v.state[2]:
            print(f"  the ignored files that go with it: {', '.join(v.state[2])}")
    let_go(main, e, v, force=v.kind != "clean")
    return True


def one(args, where, discard=False, err=False):
    """`done` and `remove` (`err`): the worktree `where` (a path or a name), or its branch alone when its directory
    is gone. For `remove`, a path with neither a worktree nor its branch has nothing to remove: exit 0."""
    main = main_of(args.main)
    path = place(main, where).resolve()
    if path == main or path.parent != main / WORKTREES:
        raise Failed(f"{path} is not a worktree under {WORKTREES}/ of the main tree {main}")
    found = [e for e in entries(main, False) if e.path == path or (e.path is None and e.branch == branch_of(path.name))]
    if not found and err and not path.exists():
        print(f"nothing to remove: no worktree {path} nor its branch {branch_of(path.name)}", file=sys.stderr)
        return 0
    if not found:
        raise Failed(f"no worktree {path} nor its branch {branch_of(path.name)} without one")
    return 0 if settle(main, found[0], args, discard=discard, err=err) else 1


def done(args):
    return one(args, args.worktree, discard=args.discard)


def remove(args):
    try:
        return one(args, args.path, err=True)
    except Failed as e:  # the hook WorktreeRemove: the reason on stderr
        print(e, file=sys.stderr)
        return 1


def close(args):
    main = main_of(args.main)
    status = git(main, "status", "--porcelain").stdout.decode().splitlines()
    print(f"the main tree {main}: {len(status)} uncommitted change(s)")
    went = kept = failed = 0
    for e in entries(main, args.dry_run):
        try:
            if settle(main, e, args, dry=args.dry_run):
                went += 1
            else:
                kept += 1
        except Failed as x:
            print(f"  failed: {x}")
            failed += 1
    print(f"close: {went} {'to remove' if args.dry_run else 'removed'}, {kept} kept, {failed} failed")
    return 1 if failed else 0


# ---------------------------------------------------------------- an agent's sync, the parent's commit (U6)

SYNC_WIP = "WIP: before sync with dev"  # the default subjects of the WIP commits of `sync`
APPLY_WIP = "WIP: apply {}"
DOCS_AGENT = "onsa-docs"  # named in the value of docs.DOCS_CHECKED, after the work
CO_AUTHOR = "Co-Authored-By"
CO_AUTHOR_FORM = re.compile(r"[^<>\n]*[^<>\s] <[^<>\s]+@[^<>\s]+>")


def count(tree, revs):
    return int(git(tree, "rev-list", "--count", revs).stdout)


def in_merge(tree):
    """Why `sync` and `lines` stop when the tree is in a merge (`add -A` and `reset` would end it), else None."""
    merging = git(tree, "rev-parse", "-q", "--verify", "MERGE_HEAD", ok=(0, 1)).returncode == 0
    return "in a merge (MERGE_HEAD): finish or abort it" if merging else None


def uncommitted(tree):
    """The lines of `git status --porcelain` (untracked files too)."""
    return git(tree, "status", "--porcelain").stdout.decode(errors="replace").splitlines()


def short(tree, rev="HEAD"):
    return git(tree, "rev-parse", "--short", rev).stdout.decode().strip()


def wip(tree, subject, paths=()):
    """Commit what the tree holds (`add -A`), or the paths alone (`--only`), with `subject`."""
    git(tree, "add", "-A", "--", *paths)
    git(tree, "commit", "-q", "-m", subject, *(["--only", "--", *paths] if paths else []))
    print(f"sync: committed {subject!r} ({short(tree)})")


def hand_in(tree, patch_file, subject):
    """`--apply`: the patch the way `check` and `apply` do, then its WIP commit of its files; the exit."""
    how, paths, notes = checked(patch_file, tree)
    if how == ALREADY:
        return 0
    if notes:
        print("sync: not applied: the tree has uncommitted changes in the files of the patch")
        return 1
    code, conflicts = apply_patch(patch_file, tree, how, paths)
    if code or conflicts:
        print("sync: the patch did not apply cleanly; nothing committed"
              + (f"; conflicts: {', '.join(conflicts)}" if conflicts else ""))  # fmt: skip
        return 1
    wip(tree, subject or APPLY_WIP.format(Path(patch_file).name), paths)
    return 0


def merge_dev(tree, subject):
    """Steps 2 to 4 of `sync`; the exit."""
    if count(tree, f"HEAD..{DEV}") == 0:
        print(f"sync: {DEV} is in HEAD already; nothing to take in")
        return 0
    if count(tree, f"{DEV}..HEAD") == 0 and not uncommitted(tree):
        git(tree, "merge", "-q", "--ff-only", DEV)
        print(f"sync: fast-forwarded to {DEV}")
        return 0
    if uncommitted(tree):
        wip(tree, subject or SYNC_WIP)
    r = git(tree, "merge", "-q", "--no-edit", DEV, ok=(0, 1))
    conflicts = listed(tree, "diff", "--name-only", "--diff-filter=U")
    if r.returncode and not conflicts:
        raise Failed(f"git merge {DEV}: {r.stderr.decode(errors='replace').strip()}")
    if conflicts:
        print(f"sync: the merge of {DEV} stopped with conflicts; resolve them and commit (rules/common.md 2.2):")
        for path in conflicts:
            print(f"  {path}")
        return 1
    print(f"sync: merged {DEV}")
    return 0


def sync(args):
    tree = Path(args.tree)
    kind = repo.tree_kind(tree)
    branch = git(tree, "symbolic-ref", "-q", "--short", "HEAD", ok=(0, 1)).stdout.decode().strip() if kind else ""
    why = ("not the top of a git tree" if kind is None else "the main tree; sync is for a worktree" if kind == "main"
           else "HEAD is on no branch" if not branch else in_merge(tree))  # fmt: skip
    if why:
        print(f"sync: {tree}: {why}; nothing done")
        return 1
    behind = count(tree, f"HEAD..{DEV}")
    try:
        code = merge_dev(tree, args.m)
        if code == 0 and args.apply:
            code = hand_in(tree, args.apply, args.m)
    except Failed as e:
        print(e)
        code = 1
    print(f"sync: {branch}, HEAD {short(tree)}, {DEV} {short(tree, DEV)}; {count(tree, f'{DEV}..HEAD')} commit(s) "
          f"after {DEV}, {behind - count(tree, f'HEAD..{DEV}')} commit(s) of {DEV} taken in, "
          f"{len(uncommitted(tree))} uncommitted change(s)")  # fmt: skip
    return code


def lines(args):
    tree = Path(args.tree)
    kind = repo.tree_kind(tree)
    why = "not the top of a git tree" if kind is None else in_merge(tree)
    if why:
        print(f"lines: {tree}: {why}; nothing done")
        return 1
    main = kind == "main"
    base = args.base or (git(tree, "rev-parse", "HEAD").stdout.decode().strip() if main else base_of(tree))
    _, stats, new, inner = staged_diff(tree, base)
    how = "HEAD of the main tree" if main else f"git merge-base {DEV} HEAD"
    print(f"lines: {tree} from {args.base or f'{base[:9]} ({how})'}, uncommitted changes and untracked files too")
    code = summary(stats, new, inner)
    if args.estimate:
        print(estimate_line(code[0], args.estimate, tree))
    return 0


def docs_value(tree, text, work_id):
    """The value of docs.DOCS_CHECKED for `<A>..<B>`, both ends commits of `tree`, written as their short hashes
    (a name such as HEAD or a branch would read as another commit later, X-12)."""
    ends = text.split("..")
    sha = [git(tree, "rev-parse", "-q", "--verify", "--short", f"{e}^{{commit}}", ok=(0, 1)) for e in ends if e]
    if len(ends) != 2 or len(sha) != 2 or any(r.returncode for r in sha):
        raise Failed(f"commit: {text} is not <A>..<B> of two commits of {tree}; nothing done")
    return f"{'..'.join(r.stdout.decode().strip() for r in sha)} ({work_id}, {DOCS_AGENT})"


def mark_done(tree, id_):
    """`docs.py set <id_> status=DONE` in `tree` (the swap files checked); (its file, what it held before)."""
    try:
        docs.Ids(tree).require(id_)
        rel = docs.Ids(tree).where(id_).rel
    except docs.DocsError as e:
        raise Failed(f"commit: --done {id_}: {e}; nothing done") from None
    if rel is None:
        raise Failed(f"commit: --done {id_}: no file of it; nothing done")
    held = (tree / rel).read_bytes()
    if docs.main(["set", id_, "status=DONE", "--root", str(tree)]):
        raise Failed(f"commit: --done {id_}: docs.py set wrote nothing; nothing done")
    return rel, held


def commit(args):
    tree = Path(args.tree)
    if repo.tree_kind(tree) is None:
        raise Failed(f"commit: {tree} is not the top of a git tree")
    try:
        message = "\n\n".join([*args.m, *([Path(args.F).read_text(encoding="utf-8")] if args.F else [])]) + "\n"
    except (OSError, ValueError) as e:
        raise Failed(f"commit: -F {args.F}: {e}") from None
    value = docs_value(tree, *args.docs_checked) if args.docs_checked else None
    trailers = [*([f"{docs.DOCS_CHECKED}: {value}"] if value else []),
                *([f"{CO_AUTHOR}: {args.co_author}"] if args.co_author else [])]  # fmt: skip
    paths, done, added = list(args.paths), None, []
    if not paths and not args.done:
        raise Failed("commit: name the paths to commit (or --done)")
    if args.done:
        done = mark_done(tree, args.done)
        paths.append(done[0].as_posix())
    try:
        idle = [p for p in paths if not listed(tree, "diff", "--name-only", "HEAD", "--", p)
                and not listed(tree, "ls-files", "-o", "--exclude-standard", "--", p)]  # fmt: skip
        if idle:
            print(f"commit: no change in {', '.join(idle)}")
        live = [p for p in paths if p not in idle]
        if not live:
            raise Failed("commit: none of the paths named has a change; nothing committed")
        added = listed(tree, "ls-files", "-o", "--exclude-standard", "--", *live)
        if added:
            git(tree, "add", "--", *added)
        git(tree, "commit", "-q", "--only", "--cleanup=whitespace", "-F", "-",
            *(x for t in trailers for x in ("--trailer", t)), "--", *live, input=message.encode())  # fmt: skip
    except Failed as e:
        if added:
            git(tree, "reset", "-q", "--", *added)
        if done:
            (tree / done[0]).write_bytes(done[1])
        raise Failed(f"{e}\ncommit: the index{' and the file of --done are' if done else ' is'} as before") from None
    head = git(tree, "rev-parse", "HEAD").stdout.decode().strip()
    if value:
        try:
            read = docs.last_docs_check(tree)
        except docs.DocsError as e:
            read = f"nothing ({e})"
        if read != (head, value):
            print(f"commit: docs.py due does not read the {docs.DOCS_CHECKED}: of {head[:9]} (it reads {read})")
    files = listed(tree, "diff-tree", "--root", "--no-commit-id", "--name-only", "-r", "HEAD")
    branch = git(tree, "branch", "--show-current").stdout.decode().strip() or "no branch"
    print(f"commit {short(tree)} on {branch}: {len(files)} file(s); "
          f"{len(uncommitted(tree))} uncommitted change(s) not in it")  # fmt: skip
    try:
        print(after_commit.on_commit(tree.resolve(), sweep=not args.no_sweep))
    except (narrowing.NarrowError, OSError) as e:
        print(f"auto sweep: not asked: {e} (the commit is made; tools/after_commit.py --now)")
        return 1
    return 0


def sync_args(p):
    p.add_argument("--apply", metavar="PATCH", help="then apply this patch (check, apply) and commit it as WIP")
    p.add_argument("-m", metavar="SUBJECT", help=f"the subject of the WIP commits (default {SYNC_WIP!r}, "
                   f"{APPLY_WIP.format('<the patch>')!r})")
    p.add_argument("--tree", default=ROOT, help="the worktree (default the one of this tool)")


def lines_args(p):
    p.add_argument("--base", help="the commit to count from (default: in a worktree git merge-base dev HEAD, after a "
                   "unit taken over its WIP commit; in the main tree HEAD)")
    p.add_argument("--estimate", type=positive, help="the lines of the code estimated before the work")
    p.add_argument("--tree", default=ROOT, help="the worktree or the main tree (default the one of this tool)")


def co_author(text):
    if not CO_AUTHOR_FORM.fullmatch(text):
        raise argparse.ArgumentTypeError(f"not \"<name> <mail>\": {text}")
    return text


def commit_args(p):
    p.add_argument("paths", nargs="*", help="the paths to commit (from the top of the tree), as they are now "
                   "(untracked, removed)")
    p.add_argument("-m", action="append", required=True, metavar="TEXT", help="the subject, then a paragraph each")
    p.add_argument("-F", metavar="FILE", help="paragraphs after those of -m")
    p.add_argument("--done", metavar="ID", help="docs.py set ID status=DONE, and its file in the commit")
    p.add_argument("--docs-checked", nargs=2, metavar=("A..B", "WORK"),
                   help=f"the trailer `{docs.DOCS_CHECKED}: A..B (WORK, {DOCS_AGENT})` (docs.py due reads it): A..B is "
                   "the range checked, the HEAD of then at both ends for an uncommitted diff")
    p.add_argument("--co-author", type=co_author, metavar='"NAME <MAIL>"', help=f"the trailer {CO_AUTHOR}:, last")
    p.add_argument("--no-sweep", action="store_true", help="網羅の検査を外す（いつ外すかは rules/process.md 8.5）")
    p.add_argument("--tree", default=ROOT, help="the tree (default the one of this tool)")


def positive(text):
    n = int(text)
    if n <= 0:
        raise argparse.ArgumentTypeError(f"not a positive number: {text}")
    return n


def new_args(p):
    p.add_argument("name", help="the name of the worktree (a slug: WorktreeCreate's `name`)")
    p.add_argument("--main", default=ROOT, help="a tree of the repository (default this one); its main tree's")


def take_args(p):
    p.add_argument("worktree", help="the worktree: a path, or a name under .claude/worktrees/ of the main tree")
    p.add_argument("--base", help="the commit the patch starts from (default: git merge-base dev <its HEAD>)")
    p.add_argument("--estimate", type=positive, help="the lines of the code estimated before the work")
    p.add_argument("--go", action="store_true", help="apply it also when the check says to read it first")
    p.add_argument("--out", help="the patch file to write (default <main>/target/work/<name>-<time>.patch)")
    p.add_argument("--main", default=ROOT, help="the main tree the patch goes to (default this repository)")


def patch_args(p):
    p.epilog, p.formatter_class = PATCH_EPILOG, argparse.RawDescriptionHelpFormatter
    p.add_argument("worktree", help="the worktree whose work is taken")
    p.add_argument("base", help="the commit the patch starts from (the base of the work)")
    p.add_argument("out", help="the patch file to write")
    p.add_argument("--main", default=ROOT, help="the main tree the patch goes to (default this repository)")


def session_id(text):
    if not NAME.fullmatch(text):
        raise argparse.ArgumentTypeError(f"not the ID of a session: {text}")
    return text


def clean_args(*first):
    def add(p):
        for name, help_ in first:
            p.add_argument(name, help=help_)
        p.add_argument("--session", type=session_id, help="the session of the agents that may be running (the ID in "
                       "its scratchpad's path; the hook's session_id); without it, any record not finished is live")
        p.add_argument("--scratchpad", help="the session's scratchpad: whether the reports of the agents are saved")
        p.add_argument("--main", default=ROOT, help="a tree of the repository (default this one); its main tree's")

    return add


def done_args(p):
    clean_args(("worktree", "the worktree: a path, or a name under .claude/worktrees/ of the main tree"))(p)
    p.add_argument("--discard", action="store_true", help="remove it also when changed and not taken, after writing "
                   f"its last patch under {DISCARDED}/ (never a running agent's)")


def close_args(p):
    clean_args()(p)
    p.add_argument("--dry-run", action="store_true", help="remove nothing (nor prune): the verdicts alone")


def to_args(p):
    p.add_argument("patch")
    p.add_argument("--to", default=ROOT)


def run_new(args):
    path = new(args.name, args.main)
    print(f"made {path} on the branch {branch_of(args.name)} from {DEV}", path, sep="\n")
    return 0


def run_patch(args):
    patch(args.worktree, args.base, args.out, args.main)
    return 0


def run_check(args):
    checked(args.patch, args.to)
    return 0


def run_apply(args):
    how, paths, _ = checked(args.patch, args.to)
    return 0 if how == ALREADY else apply_patch(args.patch, args.to, how, paths)[0]


def failing(fn):
    def go(args):
        try:
            return fn(args)
        except Failed as e:
            print(e)
            return 1

    return go


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "sync": C(sync_args, failing(sync), ("t", "i", "docs"),
              "作業ツリーに dev を取り込む（自分のコミットも変更も無ければ ff-only、あれば WIP を置いて merge、衝突ならファイルを並べて止める）。--apply で引き継ぎのパッチを当てて WIP を置く",
              "作業ツリーで動く担当の始めと、親が dev の取り込みを指示したとき。主のツリーと merge の途中では何もせず終了 1",
              "work.py sync --apply /tmp/x1.patch -m 'WIP: X-9 U6'"),
    "lines": C(lines_args, failing(lines), ("t", "i", "b", "parent"),
               "作業ツリーの基（take と同じ git merge-base dev HEAD）か主のツリーの HEAD からの差の行数を、未コミットと未追跡も含めて take・patch と同じ数え方（テストとデータ、Rust のテストのモジュールを除く）で出す。--estimate で take と同じ比の行",
               "実装の担当が報告に見積もりと実際の行数を書く前。前の単位を引き継いだ作業ツリーの担当は、その WIP のコミットを --base に渡す。git の外と merge の途中では何もせず終了 1",
               "work.py lines --estimate 40"),
    "new": C(new_args, failing(run_new), ("parent",),
             "主のツリーの .claude/worktrees/<名前> に、dev から枝 worktree-<名前> の作業ツリーを作り、経路を最後の行に出す",
             "担当を作業ツリーで起こすとき（WorktreeCreate のフックが呼ぶ）。同じ名前の枝か経路があれば作らずに終了 1",
             "work.py new agent-a1b2c3"),
    "take": C(take_args, failing(take), ("parent",),
              "作業ツリーの仕事を patch → check の順に確かめ、plain で当たり、重なる未コミットが無く、作業の検査を回し直さずに済むときだけ主のツリーに当てる",
              "担当の成果を写すとき。止まったら check の結果を読み、--go で当てる。登録の hunk と --estimate の比も読む",
              "work.py take agent-a1b2c3 --estimate 150"),
    "patch": C(patch_args, failing(run_patch), ("parent",),
               "作業ツリーの基からのパッチを作って行数を出し、作業の検査を回し直すかを言い、ファズの入力を主のツリーに写す",
               "take を使わずに一つずつ写すとき、引き継ぎのパッチを作るとき。読み方は patch --help の末尾",
               "work.py patch .claude/worktrees/x1 2ce980a /tmp/x1.patch"),
    "check": C(to_args, failing(run_check), ("parent", "i"),
               "パッチが plain・3-way・既に入っているのどれで当たるかと、当てる先の重なる未コミットを出す",
               "パッチを当てる前",
               "work.py check /tmp/x1.patch --to .claude/worktrees/x2"),
    "apply": C(to_args, failing(run_apply), ("parent", "i"),
               "パッチを check の見つけた形で当て、3-way の後は索引から外し、当てたことを控える",
               "check を読んだ後。担当の引き継ぎのパッチは、自分の作業ツリーで `work.py sync --apply <パッチ>` が当てて WIP を置く",
               "work.py apply /tmp/x1.patch --to .claude/worktrees/x2"),
    "commit": C(commit_args, failing(commit), ("parent",),
                "名指した経路の今の中身だけをコミットし（未追跡と削除も。他の変更と索引は残す）、--done で作業を DONE に、--docs-checked と --co-author で trailer を書く。主のツリーでコードか事例に触れたら網羅の検査を裏で起こす（--no-sweep で外し、コードに触れたら基のバイナリだけを保存する）",
                "親が主のツリーでコミットするとき。git の commit が失敗したら、索引と --done のファイルを元に戻す",
                "work.py commit -m 'Add sync and commit to the work tool (X-9/U6)' tools/work.py --done X-9 --co-author 'Claude <noreply@anthropic.com>'"),
    "done": C(done_args, failing(done), ("parent",),
              "一つの作業ツリーに片付けの判定（生きている担当 → 変更なし → 写し済み → それ以外）を当て、消せるなら消し、消せなければ理由を出して終了 1",
              "担当の成果を写した後と、担当の仕事を捨てるとき（--discard でパッチを target/work/discarded/ に書いてから消す）",
              "work.py done agent-a1b2c3 --session <ID> --scratchpad <scratchpad>"),
    "close": C(close_args, failing(close), ("parent",),
               "全ての作業ツリー（.claude/worktrees/ の下）と worktree- の枝に同じ判定を当て、消せるものを消し、残すものを理由と並べる",
               "区切りで。--dry-run は消さずに表だけを出す。主のツリーの未コミットの数も出す",
               "work.py close --dry-run --session <ID> --scratchpad <scratchpad>"),
    "remove": C(clean_args(("path", "the worktree's path (WorktreeRemove's worktree_path)")), remove, ("parent",),
                "一つの作業ツリーに同じ判定を当て、消せるなら消して終了 0、残すなら理由を stderr に書いて終了 1",
                "WorktreeRemove のフックが呼ぶ（Claude Code は 0 でない終了で作業ツリーを残す）",
                "work.py remove /Users/centrevillage/projects/onsalang/.claude/worktrees/agent-a1b2c3"),
}  # fmt: skip


def main(argv=None):
    args = repo.parse_command("work.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
