#!/usr/bin/env python3
"""Run chosen cases of a tree alone (rules/checks.md ch. 4, "running cases narrowly").

The case runner `onsa_cases --run <root>` takes a root that holds `tests/`, not a file. This copies
each `tests/<path>` of the tree (a file with its `.fixK` files, or a directory) under a work
directory and runs the runner on it; it prints `ok` or `FAIL` and the problems of each case.
The host sequences of a case (`[[test.host]]`, the calls at the C boundary) run only with `--hosts`, as
`cargo test -p onsa_tests --test cases` runs them (`onsa_cases --run --hosts`): the line of such a case then says how
many passed, and one that fails or does not run is a problem of the case (without a C compiler, a problem of kind
`harness`, as in the test). Without `--hosts` the `ok` says nothing of them: the line says how many did not run.

    tools/run_cases.py [--tree DIR] [--bin ONSA_CASES] [--hosts | --c ITEM] --work DIR <path under tests/>...

--tree  the tree whose cases are run (default: this repository)
--bin   the case runner (default: <tree>/target/debug/onsa_cases)
--hosts run the host sequences too (a C compiler, the C check `c-clang`'s, builds them)
--c     run the C check ITEM (one of `onsa_cases --c-items`: c-clang, c-gcc, …; another name is a usage error, exit 2)
        on the cases copied instead of the cases themselves, as the gate runs it on all (`onsa_cases --c ITEM <work>`);
        its lines (a line a case `<path>[<target>]`) are printed as they are. With --hosts it is a usage error (exit 2).
        An empty tests/pending.toml is written in the work directory: as with the cases, a case listed there fails as
        without the list. Exit 0 when the item passes, 1 when it fails or cannot run (its exit 2: no C compiler, no
        case copied that builds a target; its last line says CANNOT RUN).
--work  a scratch directory of the caller, emptied first: an absolute path outside the tree and this repository
        (and its main tree, run from a work tree), neither in them nor holding them; any other is refused with
        exit 1, nothing removed
The golden files a case declares (`golden`, `golden_graph`, read from the runner's list of the cases copied) are
copied to the same places under the work directory, so they are compared as in the test.
The runner does not read tests/pending.toml, so a case listed there fails here as it fails without the list.
It writes no copy either (the `.fixK` of a case, a golden file): they are made by
`UPDATE_GOLDEN=1 cargo test -p onsa_tests --test cases`, which runs every case (about 5 s).
A problem is printed whole, its lines indented.
Exit 0 when every case passes, 1 otherwise (without the runner too: a line says which path is not there).
A runner older than the code it is built from gets a line first (X-19 2), and the run goes on: it is not built here.
The code is every file below `narrowing.BUILT_FROM` but `tools/` (scripts, not built into the runner), the tests of a
crate (`crates/<crate>/tests/`) and names that start with `.`; the newest by the time of the file is named. Missed:
a file removed, and a runner copied or touched after the change; told without need: a change that cargo does not
rebuild the runner for (a crate it does not use), and a runner of another tree (`--bin`).
"""
import argparse
import glob
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import narrowing  # noqa: E402
import repo  # noqa: E402


def refused(work, trees):
    """Why `--work` is not emptied, or None: not absolute (it would be read from the current directory), or in one
    of `trees` or holding one (X-6 S3 left a copy in the root of its work tree)."""
    if not os.path.isabs(work):
        return "not an absolute path"
    w = Path(work).resolve()
    for t in (Path(t).resolve() for t in trees if t):
        if w == t or t in w.parents or w in t.parents:
            return f"{'holds' if w in t.parents else 'in'} {t}"
    return None


HOST_STEPS = "cargo test -p onsa_tests --test cases"


def host_note(case, ran) -> str:
    """What the line of `case` says of its host sequences: how many passed when they `ran`, else how many did not."""
    names = case.get("host_names", [])
    if not names:
        return ""
    if not ran:
        return f" ({len(names)} host sequence(s) not run: pass --hosts, or `{HOST_STEPS}` runs them)"
    passed = sum(h.get("outcome") == "passed" for h in case.get("hosts", []))
    return f" ({passed} of {len(names)} host sequence(s) passed)"


def declared(case):
    """The golden files under tests/golden/ that `case` (of the runner's list) declares, as `golden::declared` of
    crates/onsa_tests/src/golden.rs names them."""
    n, kinds = case["name"], case.get("golden", [])
    out = [{"core": f"core/{n}.core", "interface": f"interface/{n}.txt"}[k] for k in kinds if k != "c"]
    out += [f"c/{n}.{t}.{e}" for t in case.get("targets", []) if "c" in kinds for e in "ch"]
    return out + [f"graph/{n}.{f}.dot" for f in case.get("golden_graph", [])]


def code_files(tree):
    """The files of `tree` the case runner is built from, as the docstring says."""
    for spec in (x for x in narrowing.BUILT_FROM if x != "tools"):
        glob_ = spec.startswith(":(glob)")
        for top in glob.glob(os.path.join(tree, spec[7:])) if glob_ else [os.path.join(tree, spec)]:
            yield from [top] if os.path.isfile(top) else []
            for d, dirs, files in os.walk(top):
                crate = os.path.dirname(os.path.relpath(d, tree)) == "crates"
                dirs[:] = [x for x in dirs if not x.startswith(".") and not (crate and x == "tests")]
                yield from (os.path.join(d, f) for f in files if not f.startswith("."))


def stale(tree, runner):
    """The line of a runner older than the newest of `code_files(tree)`, or None."""
    newest = max(code_files(tree), key=os.path.getmtime, default=None)
    late = newest and os.path.getmtime(newest) - os.path.getmtime(runner)
    if late and late > 0:
        return (f"note: {runner} is older than {os.path.relpath(newest, tree)} by {late:.0f} s ({late / 3600:.1f} h): "
                "`cargo build -p onsa_tests --bin onsa_cases` builds it; this run goes on")
    return None


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tree", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--bin")
    one = ap.add_mutually_exclusive_group()
    one.add_argument("--hosts", action="store_true")
    one.add_argument("--c", metavar="ITEM")
    ap.add_argument("--work", required=True)
    ap.add_argument("paths", nargs="+")
    a = ap.parse_args(argv)
    why = refused(a.work, [a.tree, repo.ROOT, repo.main_tree(repo.ROOT)])
    if why:
        print(f"--work {a.work}: {why}; give an absolute path outside the tree and the repository (nothing removed)")
        return 1
    tests = os.path.join(a.tree, "tests")
    runner = a.bin or os.path.join(a.tree, "target", "debug", "onsa_cases")
    if shutil.which(runner) is None:
        print(f"no case runner: {runner} (build it, or pass one with --bin)")
        return 1
    items = json.loads(subprocess.run([runner, "--c-items"], capture_output=True, timeout=60).stdout) if a.c else []
    if a.c and a.c not in items:
        ap.error(f"--c {a.c}: not an item of `onsa_cases --c-items` ({', '.join(items)})")
    if note := stale(a.tree, runner):
        print(note)
    shutil.rmtree(a.work, ignore_errors=True)
    for rel in a.paths:
        src = os.path.join(tests, rel)
        if os.path.isdir(src):
            shutil.copytree(src, os.path.join(a.work, "tests", rel))
            continue
        if not os.path.isfile(src):
            print(f"no case: tests/{rel}")
            return 1
        for f in [src] + sorted(glob.glob(src + ".fix*")):
            dst = os.path.join(a.work, "tests", os.path.relpath(f, tests))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy(f, dst)
    listed = subprocess.run([runner, a.work], capture_output=True, text=True, timeout=600)
    try:
        golden = sorted({g for c in json.loads(listed.stdout) for g in declared(c)})
    except json.JSONDecodeError:
        print("the runner did not list the cases:", listed.stdout[:2000], listed.stderr[:2000])
        return 1
    for g in golden:
        if os.path.isfile(src := os.path.join(tests, "golden", g)):  # one missing is the run's problem
            os.makedirs(os.path.dirname(dst := os.path.join(a.work, "tests", "golden", g)), exist_ok=True)
            shutil.copy(src, dst)
    if a.c:  # the item reads the list (its exit 2 when no case copied builds a target)
        Path(a.work, "tests", "pending.toml").write_text("")
        r = subprocess.run([runner, "--c", a.c, a.work], capture_output=True, text=True, timeout=1800)
        print(r.stdout + r.stderr, end="")
        return 0 if r.returncode == 0 else 1
    r = subprocess.run([runner, "--run", *(["--hosts"] if a.hosts else []), a.work],
                       capture_output=True, text=True, timeout=600)  # fmt: skip
    try:
        out = json.loads(r.stdout)
    except json.JSONDecodeError:
        print(r.stdout[:2000], r.stderr[:2000])
        return 1
    cases = out.get("cases", [])
    if not cases:
        print("no case ran")
        return 1
    failed = 0
    for c in cases:
        problems = c.get("problems", [])
        failed += bool(problems)
        print(("FAIL " if problems else "ok   ") + c.get("path", c.get("name", "?")) + host_note(c, a.hosts))
        for p in problems:
            print("      " + str(p).replace("\n", "\n      "))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
