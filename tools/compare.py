#!/usr/bin/env python3
"""Before and after: the diagnostics and the time of `onsa` binaries (rules/refactoring.md 8; X-9 X9-18, X9-19).

Its commands are `diags` and `speed` (COMMANDS, rules/tools.md 9.1); `compare.py help` shows them.
`diags` runs `check --json` of both binaries on every case of tests/: the seed files of the gate's fuzz
(`fuzz.seeds`), a file in a package (a directory below tests/ with an `onsa.toml`, the outermost, as the case
harness `onsa_tests::case::collect`) giving way to its directory. It lists the cases whose diagnostics differ in
the code, the place, the message, the titles or the edits of the fix candidates, or the notes (their messages and
places), and every case where a binary fell (exited other than 0, 1 and 2, ran out of time, or printed no JSON).
It exits 1 when a case differs (a case where both fell the same way is listed, but does not differ) or when no
case gave JSON on both sides.
`speed` measures as the removed `tools/speed.py` did (X9-19), the order of the binaries turned round every other round.
"""
import json
import os
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
import fuzz  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
TIMEOUT = 30  # seconds per run of `diags`
PARTS = ((2, "message"), (3, "fix titles"), (4, "fix edits"), (5, "notes"))  # the parts of `diagnostic` a pair names


def cases(root) -> list:
    """The paths `diags` checks, relative to `root`: the fuzz's seed files, a package's ones as its directory."""
    out = {}
    for rel, _ in fuzz.seeds(root):
        dirs = [d for d in reversed(Path(rel).parents) if len(d.parts) > 1]  # below tests/, the outermost first
        out[next((d.as_posix() for d in dirs if (Path(root) / d / "onsa.toml").exists()), rel)] = None
    return list(out)


def diagnostic(d) -> tuple:
    """What `diags` compares of a diagnostic: (code, place, message, fix titles, fix edits, notes).
    `found` is not compared."""
    s = d.get("span") or {}
    fixes = d.get("fixes") or []
    return (d.get("code"), f"{s.get('file')}:{s.get('line')}:{s.get('col')}-{s.get('end_line')}:{s.get('end_col')}",
            d.get("message"), tuple(f.get("title") for f in fixes),
            json.dumps([f.get("edits") for f in fixes], sort_keys=True, ensure_ascii=False),
            json.dumps([[n.get("message"), n.get("span")] for n in d.get("notes") or []],
                       sort_keys=True, ensure_ascii=False))


def check(binary, case, root):
    """The diagnostics of `binary check --json <case>`, or (a str) how it fell."""
    try:
        r = subprocess.run([binary, "check", "--json", case], cwd=root, capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return f"timeout ({TIMEOUT} s)"
    head = "".join(f": {h[:100]}" for h in (r.stderr or r.stdout).decode("utf-8", "replace").strip().splitlines()[:1])
    if r.returncode not in (0, 1, 2):
        return (f"signal {-r.returncode}" if r.returncode < 0 else f"exit {r.returncode}") + head
    try:
        return [diagnostic(d) for d in json.loads(r.stdout)["diagnostics"]]
    except (ValueError, KeyError, TypeError, AttributeError):
        return f"not JSON (exit {r.returncode}){head}"


def changes(before, after) -> list:
    """The lines of a case listed: how a binary fell, or the diagnostics of one side only (`-` before, `+`
    after), a pair at the same code and place in one line (`~`) naming the parts that differ."""
    if isinstance(before, str) or isinstance(after, str):
        show = lambda x: x if isinstance(x, str) else f"{len(x)} diagnostic(s)"  # noqa: E731
        return [f"  before: {show(before)}", f"  after:  {show(after)}"]
    new = list((Counter(after) - Counter(before)).elements())
    out = []
    for g in (Counter(before) - Counter(after)).elements():
        n = next((n for n in new if n[:2] == g[:2]), None)
        if n is None:
            out.append(f"  - {g[0]} {g[1]} {g[2]}")
            continue
        new.remove(n)
        parts = [f"{name} {g[i]!r} -> {n[i]!r}" if i < 4 else name for i, name in PARTS if g[i] != n[i]]
        out.append(f"  ~ {g[0]} {g[1]}: " + "; ".join(parts))
    return out + [f"  + {n[0]} {n[1]} {n[2]}" for n in new] or ["  the same diagnostics in another order"]


def executable(parser, b) -> str:
    p = Path(b).resolve()
    if not (p.is_file() and os.access(p, os.X_OK)):
        parser.error(f"{b}: not an executable file")
    return str(p)


def diags(args) -> int:
    before, after = (executable(args.parser_, b) for b in (args.before, args.after))
    units = cases(args.root)
    if not units:
        print(f"diags: no case under {args.root / 'tests'}")
        return 1
    with ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda c: (check(before, c, args.root), check(after, c, args.root)), units))
    differ = one = both = 0
    for case, (b, a) in zip(units, results):
        fell = isinstance(b, str) + isinstance(a, str)
        if b != a or fell:
            differ, one, both = differ + (b != a), one + (fell == 1), both + (fell == 2)
            print(case, *changes(b, a), sep="\n")
    print(f"{len(units)} cases, {differ} differ, {one} fell in one binary only, {both} fell in both")
    return 1 if differ or both == len(units) else 0  # none compared is no pass


def timed(binary: str, args: list, files: list) -> float:
    t = time.perf_counter()
    for f in files:
        subprocess.run([binary, *args, str(f)], capture_output=True, timeout=120)
    return time.perf_counter() - t


def turn(binaries, r) -> list:
    """The order of round `r`: as given in the even rounds, the other way round in the odd ones (W3-13)."""
    return binaries if r % 2 == 0 else binaries[::-1]


def speed(a) -> int:
    long = sorted(Path(a.long).glob("*.onsa")) if a.long else []
    if a.mode == "all":
        rounds = a.rounds or 3
        files = sorted(p for d in ("tests", "std", "examples") for p in (ROOT / d).rglob("*.onsa"))
        best = {b: {"check": 1e9, "fmt": 1e9, "long": 1e9} for b in a.binaries}
        for r in range(rounds):
            for b in turn(a.binaries, r):
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
    for r in range(rounds):
        for b in turn(a.binaries, r):
            for f in long:
                best[b][f] = min(best[b][f], timed(b, ["check"], [f]))
    print(f"{len(long)} long inputs, {rounds} rounds; minimum seconds")
    print({os.path.basename(b): round(sum(best[b].values()), 3) for b in a.binaries})
    first, last = a.binaries[0], a.binaries[-1]
    for f in sorted(long, key=lambda f: best[last][f] / best[first][f])[-5:]:
        print(f.name, round(best[first][f], 4), round(best[last][f], 4))
    return 0


def diags_args(p):
    p.add_argument("before")
    p.add_argument("after")
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    p.set_defaults(parser_=p)


def speed_args(p):
    p.add_argument("mode", choices=["all", "long"],
                   help="all: check と fmt --check を tests・std・examples の全ての .onsa に（1 ファイル 1 プロセス）、"
                        "--long があればその長い入力に check も。long: 長い入力ごとの check、合計と最も遅くなった五つ")
    p.add_argument("--rounds", type=int, help="回の数（既定 all 3、long 10）。回ごとの最小を残す")
    p.add_argument("--long", help="長い入力（数万行の .onsa）のディレクトリ。リポジトリには置かない")
    p.add_argument("binaries", nargs="+", metavar="binary")


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "diags": C(diags_args, diags, ("parent", "i", "b"),
               "二つのバイナリの check --json を tests/ の事例（fuzz の種。パッケージはディレクトリで）に回し、診断（コード・位置・メッセージ・候補の題と編集・note）が違う事例と落ちた事例を並べる",
               "リファクタリングや診断の文面の直しの前後で、診断と候補が変わっていないか（変わった所が意図どおりか）を見るとき。前のバイナリは主のツリーの target/base/<基>/ にある（基は作業ツリーの git merge-base dev HEAD の短い SHA）",
               "compare.py diags <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "speed": C(speed_args, speed, ("parent", "i", "b"),
               "バイナリの時間を、回ごとに順を入れ替えて交互に測り、回ごとの最小を並べる",
               "リファクタリングの前後で性能が落ちていないかを測り、報告に並べるとき（rules/refactoring.md 8.2）。前のバイナリは diags と同じ",
               "compare.py speed all <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("compare.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
