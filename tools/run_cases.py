#!/usr/bin/env python3
"""Run chosen cases of a tree alone (rules/checks.md ch. 4, "running cases narrowly").

The case runner `onsa_cases --run <root>` takes a root that holds `tests/`, not a file. This copies
each `tests/<path>` of the tree (a file with its `.fixK` files, or a directory) under a work
directory and runs the runner on it; it prints `ok` or `FAIL` and the problems of each case.

    tools/run_cases.py [--tree DIR] [--bin ONSA_CASES] --work DIR <path under tests/>...

--tree  the tree whose cases are run (default: this repository)
--bin   the case runner (default: <tree>/target/debug/onsa_cases)
--work  a scratch directory of the caller, emptied first: an absolute path outside the tree and this repository
        (and its main tree, run from a work tree), neither in them nor holding them; any other is refused with
        exit 1, nothing removed
The runner does not read tests/pending.toml, so a case listed there fails here as it fails without the list.
Exit 0 when every case passes, 1 otherwise (without the runner too: a line says which path is not there).
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


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--bin")
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
    r = subprocess.run([runner, "--run", a.work], capture_output=True, text=True, timeout=600)
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
        print(("FAIL " if problems else "ok   ") + c.get("path", c.get("name", "?")))
        for p in problems:
            print("     ", str(p)[:400])
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
