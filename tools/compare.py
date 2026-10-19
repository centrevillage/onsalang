#!/usr/bin/env python3
"""Before and after: the diagnostics, the formatting, the Core and the time of `onsa` binaries (rules/refactoring.md 8;
X-9 X9-18, X9-19; X-6 B1).

Its commands are `diags`, `fmt`, `core` and `speed` (COMMANDS, rules/tools.md 9.1); `compare.py help` shows them.
`diags` runs `check --json` of both binaries on every case of tests/: the seed files of the gate's fuzz
(`fuzz.seeds`), a file in a package (a directory below tests/ with an `onsa.toml`, the outermost, as the case
harness `onsa_tests::case::collect`) giving way to its directory. It lists the cases whose diagnostics differ in
the code, the place, the message, the titles or the edits of the fix candidates, or the notes (their messages and
places), and every case where a binary fell (exited other than 0, 1 and 2, ran out of time, or printed no JSON).
It exits 1 when a case differs (a case where both fell the same way is listed, but does not differ) or when no
case gave JSON on both sides.
`fmt` runs `onsa fmt` of both binaries on the fuzz's seed files, a file at a time, each run on its own copy in a
temporary directory of its own, and lists the files whose exit code, written text, stdout or the names of the files
left in the directory differ. `core` runs `dump --core` of both on the cases of tests/ and examples (`core_cases`) and
lists those whose exit code or output differ. Both list the falls and exit 1 as `diags` does, and when no case ran to
exit 0 in both binaries.
`speed` measures as the removed `tools/speed.py` did (X9-19), the order of the binaries turned round every other round;
the long inputs get `check` and `fmt --check`, shown apart.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
import fuzz  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
TIMEOUT = 30  # seconds per run of `diags`, `fmt` and `core`
REVIEW = "tests/review-phase1"  # left by `core`: some of its inputs fall on lowering (rules/common.md 3.2)
PARTS = ((2, "message"), (3, "fix titles"), (4, "fix edits"), (5, "notes"))  # the parts of `diagnostic` a pair names


def packaged(root, rels) -> list:
    """`rels` (files relative to `root`), a package's ones as its directory: the outermost one below the top directory
    with an `onsa.toml`, as the case harness `onsa_tests::case::collect`."""
    out = {}
    for rel in rels:
        dirs = [d for d in reversed(Path(rel).parents) if len(d.parts) > 1]  # below tests/, the outermost first
        out[next((d.as_posix() for d in dirs if (Path(root) / d / "onsa.toml").exists()), rel)] = None
    return list(out)


def cases(root) -> list:
    """The paths `diags` checks, relative to `root`: the fuzz's seed files, a package's ones as its directory."""
    return packaged(root, [rel for rel, _ in fuzz.seeds(root)])


def core_cases(root) -> list:
    """The inputs `core` lowers, relative to `root`: the cases of `diags` but tests/review-phase1 (rules/common.md
    3.2), then the files of examples, a package's ones as its directory. Whether an input lowers is its exit code."""
    tests = [rel for rel, _ in fuzz.seeds(root) if not rel.startswith(f"{REVIEW}/")]
    examples = [p.relative_to(root).as_posix() for p in sorted((Path(root) / "examples").rglob("*.onsa"))]
    return packaged(root, tests + examples)


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


def compared(args, units, run, show, ran=None, where="tests") -> int:
    """`run(binary, case)` of both binaries on every case, `--jobs` at a time. Lists the
    cases that differ or fell (a str is a fall), each with `show(before, after)`, and the count. No pair compared is
    no pass: every case fell in both, or, with `ran`, no pair is `ran(before, after)`. `where` names, below `--root`,
    where the cases come from."""
    before, after = (executable(args.parser_, b) for b in (args.before, args.after))
    if not units:
        print(f"{args.cmd}: no case in {where} of {args.root}")
        return 1
    with ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda c: (run(before, c), run(after, c)), units))
    differ = one = both = 0
    for case, (b, a) in zip(units, results):
        fell = isinstance(b, str) + isinstance(a, str)
        if b != a or fell:
            differ, one, both = differ + (b != a), one + (fell == 1), both + (fell == 2)
            print(case, *show(b, a), sep="\n")
    print(f"{len(units)} cases, {differ} differ, {one} fell in one binary only, {both} fell in both")
    if ran and not any(ran(b, a) for b, a in results):
        print(f"{args.cmd}: no case ran to exit 0 in both binaries")
        return 1
    return 1 if differ or both == len(units) else 0  # none compared is no pass


def diags(args) -> int:
    return compared(args, cases(args.root), lambda b, c: check(b, c, args.root), changes)


def outcome(argv, cwd):
    """(the exit code, the bytes of stdout) of `argv` run in `cwd`, or (a str) how it fell."""
    try:
        r = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return f"timeout ({TIMEOUT} s)"
    if r.returncode not in (0, 1, 2):
        head = "".join(f": {h[:100]}" for h in (r.stderr or r.stdout).decode("utf-8", "replace").splitlines()[:1])
        return (f"signal {-r.returncode}" if r.returncode < 0 else f"exit {r.returncode}") + head
    return r.returncode, r.stdout


def formatted(binary, rel, root, tmp):
    """`binary fmt <rel>` on a copy of `rel` in a new directory below `tmp`: (the exit code, the bytes of the file
    written, of stdout, the names of the files left in the directory), or (a str) how it fell, the file gone or
    unreadable too."""
    d = Path(tempfile.mkdtemp(dir=tmp))
    (d / rel).parent.mkdir(parents=True)
    shutil.copyfile(Path(root) / rel, d / rel)
    r = outcome([binary, "fmt", rel], d)
    if isinstance(r, str):
        return r
    try:
        text = (d / rel).read_bytes()
    except OSError as e:
        return f"exit {r[0]}, the file not readable: {e.strerror}"
    return r[0], text, r[1], tuple(sorted(p.relative_to(d).as_posix() for p in d.rglob("*") if not p.is_dir()))


def ok(before, after) -> bool:
    """A pair of `fmt` or `core` run to exit 0 in both binaries (`compared`'s `ran`)."""
    return not isinstance(before, str) and not isinstance(after, str) and before[0] == after[0] == 0


def first_line(before: bytes, after: bytes) -> str:
    """The first line that differs, `(end)` past the last."""
    b, a = (x.decode("utf-8", "replace").split("\n") for x in (before, after))
    k = next((i for i, (x, y) in enumerate(zip(b, a)) if x != y), min(len(b), len(a)))
    line = lambda xs: repr(xs[k][:100]) if k < len(xs) else "(end)"  # noqa: E731
    return f"{k + 1}: {line(b)} -> {line(a)}"


def texts(before, after) -> list:
    """The lines of a case of `fmt` or `core`: how a binary fell, or the exit codes, the numbers of lines of the
    output (the file written by `fmt`), and the first line that differs of the output and of the stdout of `fmt`,
    and the names of the files left by `fmt` on one side only."""
    if isinstance(before, str) or isinstance(after, str):
        show = lambda x: x if isinstance(x, str) else f"exit {x[0]}"  # noqa: E731
        return [f"  before: {show(before)}", f"  after:  {show(after)}"]
    lines = lambda x: x[1].count(b"\n") + 1  # noqa: E731  as `first_line` splits
    out = [f"  before: exit {before[0]}, {lines(before)} lines", f"  after:  exit {after[0]}, {lines(after)} lines"]
    for i, label in ((1, "line"), (2, "stdout line")):
        if i < len(before) and before[i] != after[i]:
            out.append(f"  {label} {first_line(before[i], after[i])}")
    if len(before) > 3 and before[3] != after[3]:
        gone, new = (sorted(set(x[3]) - set(y[3])) for x, y in ((before, after), (after, before)))
        out.append("  files: " + " ".join([f"-{n}" for n in gone] + [f"+{n}" for n in new]))
    return out


def fmt(args) -> int:
    rels = [rel for rel, _ in fuzz.seeds(args.root)]
    with tempfile.TemporaryDirectory() as tmp:  # a directory for each run
        return compared(args, rels, lambda b, rel: formatted(b, rel, args.root, tmp), texts, ok)


def core(args) -> int:
    units = core_cases(args.root)
    run = lambda b, c: outcome([b, "dump", "--core", c], args.root)  # noqa: E731
    return compared(args, units, run, texts, ok, f"tests (but {REVIEW}) and examples")


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
        runs = {"check": (["check"], files), "fmt": (["fmt", "--check"], files)}
        if long:
            runs.update({"long": (["check"], long), "long fmt": (["fmt", "--check"], long)})
        best = {b: dict.fromkeys(runs, 1e9) for b in a.binaries}
        for r in range(rounds):
            for b in turn(a.binaries, r):
                for k, (argv, fs) in runs.items():
                    best[b][k] = min(best[b][k], timed(b, argv, fs))
        print(f"{len(files)} files, {len(long)} long inputs, {rounds} rounds; minimum seconds")
        for b in a.binaries:
            print(os.path.basename(b), {k: round(v, 2) for k, v in best[b].items()})
        return 0
    if not long:
        print("long: give --long DIR with the long inputs")
        return 1
    rounds = a.rounds or 10
    kinds = {"check": ["check"], "fmt": ["fmt", "--check"]}  # shown apart (RF-13 may move check, RF-14 fmt)
    best = {b: {(k, f): 1e9 for k in kinds for f in long} for b in a.binaries}
    for r in range(rounds):
        for b in turn(a.binaries, r):
            for f in long:
                for k, argv in kinds.items():
                    best[b][k, f] = min(best[b][k, f], timed(b, argv, [f]))
    print(f"{len(long)} long inputs, {rounds} rounds; minimum seconds")
    for b in a.binaries:
        print(os.path.basename(b), {k: round(sum(best[b][k, f] for f in long), 3) for k in kinds})
    first, last = a.binaries[0], a.binaries[-1]
    for k, f in sorted(best[first], key=lambda kf: best[last][kf] / best[first][kf])[-5:]:
        print(f.name, k, round(best[first][k, f], 4), round(best[last][k, f], 4))
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
                        "--long があればその長い入力に check と fmt --check も（別の欄に）。"
                        "long: 長い入力ごとの check と fmt --check、それぞれの合計と、最も遅くなった五つ（入力と命令）")
    p.add_argument("--rounds", type=int, help="回の数（既定 all 3、long 10）。回ごとの最小を残す")
    p.add_argument("--long", help="長い入力（数万行の .onsa）のディレクトリ。リポジトリには置かない")
    p.add_argument("binaries", nargs="+", metavar="binary")


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "diags": C(diags_args, diags, ("parent", "i", "b"),
               "二つのバイナリの check --json を tests/ の事例（fuzz の種。パッケージはディレクトリで）に回し、診断（コード・位置・メッセージ・候補の題と編集・note）が違う事例と落ちた事例を並べる",
               "リファクタリングや診断の文面の直しの前後で、診断と候補が変わっていないか（変わった所が意図どおりか）を見るとき。前のバイナリは主のツリーの target/base/<基>/ にある（基は作業ツリーの git merge-base dev HEAD の短い SHA）",
               "compare.py diags <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "fmt": C(diags_args, fmt, ("parent", "i", "b"),
             "二つのバイナリの fmt を、fuzz の種の .onsa を 1 回ごとに一時のディレクトリに写して回し、終了コード・書いた後のファイル・stdout・ディレクトリに残ったファイルの名前のどれかが違う事例と落ちた事例を並べる",
             "字句・行の配置・fmt のリファクタリングの前後で、整形の結果が変わっていないかを見るとき（マージの前の確かめ）。前のバイナリは diags と同じ",
             "compare.py fmt <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "core": C(diags_args, core, ("parent", "i", "b"),
              "二つのバイナリの dump --core を、tests/ の事例（diags と同じ。tests/review-phase1 を除く）と examples（パッケージはディレクトリで）に回し、終了コードか出力が違う入力と落ちた入力を並べる。両方で終了コード 0 の入力が無ければ失敗",
              "意味解析・降下のリファクタリングの前後で、Core IR が変わっていないかを見るとき（check を回す diags では降下を確かめられない）。前のバイナリは diags と同じ",
              "compare.py core <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
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
