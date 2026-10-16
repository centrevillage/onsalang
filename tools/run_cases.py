#!/usr/bin/env python3
"""Run chosen cases of a tree alone (rules/checks.md ch. 4, "running cases narrowly").

The case runner `onsa_cases --run <root>` takes a root that holds `tests/`, not a file. This copies
each `tests/<path>` of the tree (a file with its `.fixK` files, or a directory) under a work
directory and runs the runner on it; it prints `ok` or `FAIL` and the problems of each case.

    tools/run_cases.py [--tree DIR] [--bin ONSA_CASES] --work DIR <path under tests/>...

--tree  the tree whose cases are run (default: this repository)
--bin   the case runner (default: <tree>/target/debug/onsa_cases)
--work  a scratch directory of the caller; it is emptied first
The runner does not read tests/pending.toml, so a case listed there fails here as it fails without the list.
Exit 0 when every case passes, 1 otherwise.
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--bin")
    ap.add_argument("--work", required=True)
    ap.add_argument("paths", nargs="+")
    a = ap.parse_args()
    tests = os.path.join(a.tree, "tests")
    runner = a.bin or os.path.join(a.tree, "target", "debug", "onsa_cases")
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
