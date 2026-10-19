#!/usr/bin/env python3
"""Compare the time of two or more `onsa` binaries (rules/refactoring.md ch. 8: measure before and after).

Moved to `tools/compare.py speed` (X-9 X9-19), which turns the order of the binaries round every other round.

    tools/speed.py all  [--rounds N] [--long DIR] <binary>...
    tools/speed.py long [--rounds N] --long DIR <binary>...

all   `check` and `fmt --check` over every .onsa of tests/, std/ and examples/ of this repository
      (one process per file), and `check` over the long inputs of --long if given.
long  `check` over each long input; prints the total and the five inputs that slowed the most
      (the last binary against the first).
The binaries run in turn within each round and the minimum over the rounds is kept, so that a load
of the machine during one round does not decide the comparison. The long inputs (files of tens of
thousands of lines) are not kept in the repository; the caller passes their directory.
"""
import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def timed(binary: str, args: list, files: list) -> float:
    t = time.perf_counter()
    for f in files:
        subprocess.run([binary, *args, str(f)], capture_output=True, timeout=120)
    return time.perf_counter() - t


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["all", "long"])
    ap.add_argument("--rounds", type=int)
    ap.add_argument("--long")
    ap.add_argument("binaries", nargs="+")
    a = ap.parse_args()
    long = sorted(Path(a.long).glob("*.onsa")) if a.long else []
    if a.mode == "all":
        rounds = a.rounds or 3
        files = sorted(p for d in ("tests", "std", "examples") for p in (ROOT / d).rglob("*.onsa"))
        best = {b: {"check": 1e9, "fmt": 1e9, "long": 1e9} for b in a.binaries}
        for _ in range(rounds):
            for b in a.binaries:
                best[b]["check"] = min(best[b]["check"], timed(b, ["check"], files))
                best[b]["fmt"] = min(best[b]["fmt"], timed(b, ["fmt", "--check"], files))
                if long:
                    best[b]["long"] = min(best[b]["long"], timed(b, ["check"], long))
        print(f"{len(files)} files, {len(long)} long inputs, {rounds} rounds; minimum seconds")
        for b in a.binaries:
            shown = {k: round(v, 2) for k, v in best[b].items() if k != "long" or long}
            print(os.path.basename(b), shown)
        return 0
    if not long:
        print("long: give --long DIR with the long inputs")
        return 1
    rounds = a.rounds or 10
    best = {b: {f: 1e9 for f in long} for b in a.binaries}
    for _ in range(rounds):
        for b in a.binaries:
            for f in long:
                best[b][f] = min(best[b][f], timed(b, ["check"], [f]))
    print(f"{len(long)} long inputs, {rounds} rounds; minimum seconds")
    print({os.path.basename(b): round(sum(best[b].values()), 3) for b in a.binaries})
    first, last = a.binaries[0], a.binaries[-1]
    for f in sorted(long, key=lambda f: best[last][f] / best[first][f])[-5:]:
        print(f.name, round(best[first][f], 4), round(best[last][f], 4))
    return 0


if __name__ == "__main__":
    sys.exit(main())
