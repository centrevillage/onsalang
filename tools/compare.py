#!/usr/bin/env python3
"""Before and after: the diagnostics, the formatting, the Core and the time of `onsa` binaries (rules/refactoring.md 8;
X-9 X9-18, X9-19; X-6 B1).

Its commands are `diags`, `fmt`, `core`, `speed` and `probe` (COMMANDS, rules/tools.md 9.1); `compare.py help` shows
them.
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
the long inputs get `check` and `fmt --check`, shown apart, and in `all` the inputs of `core` the first binary lowers
(exit 0) get `dump --core`. Each binary is named by its place in the arguments and the path past the directories they
share; each run shows the wall seconds and the cpu seconds (user + sys of the children). The cpu seconds swing under
load too (about 55% in an A/A of one binary, 2026-10-20): judge on a quiet machine.
`probe` writes the cases of a file (`probe_cases`) as packages below `--out` and runs every binary on each, `check
--json` or `--cmd`, named as in `speed` (W4-03, 70th session: the scripts the agents copied per worktree).
"""
import json
import os
import re
import resource
import shlex
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
CASE_NAME = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.-]*")  # a case of `probe`: a directory below --out
DIAG_LINE = re.compile(r"^(.+?):(\d+):(\d+): \w+\[(\w+)\]", re.M)  # the text form: `file:line:col: error[E…]`


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


def timed(binary: str, args: list, files: list) -> tuple:
    """(wall seconds, CPU seconds: user + sys of the children) of `binary <args> <file>` on each of `files`."""
    t, r = time.perf_counter(), resource.getrusage(resource.RUSAGE_CHILDREN)
    for f in files:
        subprocess.run([binary, *args, str(f)], capture_output=True, timeout=120)
    u = resource.getrusage(resource.RUSAGE_CHILDREN)
    return time.perf_counter() - t, u.ru_utime - r.ru_utime + u.ru_stime - r.ru_stime


def turn(binaries, r) -> list:
    """The order of round `r`: as given in the even rounds, the other way round in the odd ones (W3-13)."""
    return binaries if r % 2 == 0 else binaries[::-1]


def labels(binaries) -> list:
    """The names of the binaries in the lines of `speed`: the place in the arguments and the path past the leading
    directories they share, as `target/base/<base>/onsa` and `target/debug/onsa` (X-6 T2)."""
    paths = [os.path.abspath(b) for b in binaries]
    n = len(Path(os.path.commonpath(paths)).parts)
    return [f"{i}:" + "/".join(p[min(n, len(p) - 1):]) for i, p in enumerate((Path(x).parts for x in paths), 1)]


def least(best, times) -> tuple:
    """The (wall, cpu) minima of the rounds so far, each kept apart."""
    return tuple(map(min, best, times))


def shown(times: dict, digits: int) -> dict:
    """The wall seconds of a run under its name, the cpu seconds under `<name> cpu`."""
    return {f"{k}{s}": round(t[i], digits) for k, t in times.items() for i, s in ((0, ""), (1, " cpu"))}


def speed(a) -> int:
    long = sorted(Path(a.long).glob("*.onsa")) if a.long else []
    order, names = list(enumerate(a.binaries)), labels(a.binaries)  # a binary given twice is measured twice, apart
    unit = "minimum seconds, wall and cpu (user + sys of the children)"
    if a.mode == "all":
        rounds = a.rounds or 3
        files = sorted(p for d in ("tests", "std", "examples") for p in (ROOT / d).rglob("*.onsa"))
        # The inputs of `compare.py core` the first binary lowers (exit 0), chosen once: the column times lowering,
        # not inputs that stop at `check`.
        first = a.binaries[0]
        lowered = [ROOT / c for c in core_cases(ROOT) if outcome([first, "dump", "--core", c], ROOT)[0] == 0]
        runs = {"check": (["check"], files), "fmt": (["fmt", "--check"], files), "core": (["dump", "--core"], lowered)}
        if long:
            runs.update({"long": (["check"], long), "long fmt": (["fmt", "--check"], long)})
        best = [dict.fromkeys(runs, (1e9, 1e9)) for _ in order]
        for r in range(rounds):
            for i, b in turn(order, r):
                for k, (argv, fs) in runs.items():
                    best[i][k] = least(best[i][k], timed(b, argv, fs))
        print(f"{len(files)} files ({len(lowered)} for core), {len(long)} long inputs, {rounds} rounds; {unit}")
        for name, times in zip(names, best):
            print(name, shown(times, 2))
        return 0
    if not long:
        print("long: give --long DIR with the long inputs")
        return 1
    rounds = a.rounds or 10
    kinds = {"check": ["check"], "fmt": ["fmt", "--check"]}  # shown apart (RF-13 may move check, RF-14 fmt)
    best = [{(k, f): (1e9, 1e9) for k in kinds for f in long} for _ in order]
    for r in range(rounds):
        for i, b in turn(order, r):
            for f in long:
                for k, argv in kinds.items():
                    best[i][k, f] = least(best[i][k, f], timed(b, argv, [f]))
    print(f"{len(long)} long inputs, {rounds} rounds; {unit}")
    for name, times in zip(names, best):
        print(name, shown({k: [sum(times[k, f][i] for f in long) for i in (0, 1)] for k in kinds}, 3))
    first, last = best[0], best[-1]
    print(f"the five grown most in cpu, {names[0]} -> {names[-1]}: input, command, cpu, wall")
    for k, f in sorted(first, key=lambda kf: last[kf][1] / max(first[kf][1], 1e-6))[-5:]:
        print(f.name, k, *(f"{first[k, f][i]:.4f} -> {last[k, f][i]:.4f}" for i in (1, 0)))
    return 0


def probe_cases(text) -> list:
    """[(name, {path: text})] of a file of cases: `=== <name>` starts a case (a package), `--- <path>` a file of it,
    the lines before its first `---` are `main.onsa` (blank ones dropped), `onsa.toml` is added when not given.
    Raises ValueError (the line) on a line before the first case, and on a name or a path that is not new or would
    leave the directory of the case."""
    cases, files, path = {}, None, None
    for n, line in enumerate(text.split("\n"), 1):
        if line.startswith("=== "):
            name, files, path = line[4:].strip(), {}, None
            if not CASE_NAME.fullmatch(name) or name in cases:
                raise ValueError(f"line {n}: {name!r} is not a new name of a case (letters, digits, _ . -)")
            cases[name] = files
        elif files is None and line.strip():
            raise ValueError(f"line {n}: before the first `=== <name>`")
        elif line.startswith("--- ") or (files is not None and path is None and line.strip()):
            path = line[4:].strip() if line.startswith("--- ") else "main.onsa"
            if path in files or not path or Path(path).is_absolute() or ".." in Path(path).parts:
                raise ValueError(f"line {n}: {path!r} is not a new path inside the case")
            files[path] = [] if line.startswith("--- ") else [line]
        elif path is not None:
            files[path].append(line)
    toml = '[package]\nname = "{}"\nedition = "2026"\n'
    return [(name, {"onsa.toml": toml.format(name), **{p: "\n".join(ls).rstrip() + "\n" for p, ls in files.items()}})
            for name, files in cases.items()]  # fmt: skip


def probed(binary, argv, d):
    """(`x<exit>`, or how it fell; stdout; stderr) of `binary <argv> <d>`, the directory `d/` taken out."""
    try:
        r = subprocess.run([binary, *argv, str(d)], capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return f"timeout ({TIMEOUT} s)", "", ""
    out, err = (x.decode("utf-8", "replace").rstrip().replace(f"{d}/", "") for x in (r.stdout, r.stderr))
    return (f"x{r.returncode}" if r.returncode >= 0 else f"signal {-r.returncode}"), out, err


def probe_line(argv, result) -> str:
    """The exit and the diagnostics `code@file:line:col` of a run: from the JSON with `--json`, else from the lines
    of the text form (when none, the number of lines of the output)."""
    code, out, err = result
    if "--json" in argv:
        try:
            spans = [(d.get("code"), d.get("span") or {}) for d in json.loads(out)["diagnostics"]]
            marks = [f"{c}@{s.get('file')}:{s.get('line')}:{s.get('col')}" if s else str(c) for c, s in spans]
        except (ValueError, KeyError, TypeError, AttributeError):
            marks = ["(not JSON)"] if out else []
    else:
        text = "\n".join(x for x in (out, err) if x)
        marks = [f"{m[4]}@{m[1]}:{m[2]}:{m[3]}" for m in DIAG_LINE.finditer(text)]
        marks = marks or ([f"({text.count(chr(10)) + 1} lines)"] if text else [])
    return " ".join([code, *marks])


def probe(a) -> int:
    bins = [executable(a.parser_, b) for b in a.binaries]
    try:
        cases = probe_cases(Path(a.cases).read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        print(f"probe: {a.cases}: {e}")
        return 1
    cases = [c for c in cases if a.only in (None, c[0])]
    if not cases:
        print(f"probe: no case{f' {a.only}' if a.only else ''} in {a.cases}")
        return 1
    argv, names = shlex.split(a.cmd), labels(a.binaries)
    width = max(map(len, names))
    for name, files in cases:
        d = Path(a.out).resolve() / name
        shutil.rmtree(d, ignore_errors=True)
        for rel, text in files.items():
            (d / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / rel).write_text(text, encoding="utf-8")
        results = [probed(b, argv, d) for b in bins]
        same = all(r == results[0] for r in results)
        if a.full:
            print(f"##### {name}")
            for label, (code, out, err) in [("all", results[0])] if same else zip(names, results):
                print(f"[{label}] {code}", *[x for x in (out, err) if x], sep="\n")
            continue
        lines = [probe_line(argv, r) for r in results]
        if same:
            print(f"{name}: {lines[0]}")
            continue
        print(f"{name}:" + ("  (the same lines; the outputs differ: --full)" if len(set(lines)) == 1 else ""))
        for label, line in zip(names, lines):
            print(f"   {label:{width}} {line}")
    return 0


def diags_args(p):
    p.add_argument("before")
    p.add_argument("after")
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    p.set_defaults(parser_=p)


def speed_args(p):
    p.add_argument("mode", choices=["all", "long"],
                   help="all: check と fmt --check を tests・std・examples の全ての .onsa に、"
                        "dump --core を core の入力のうち最初のバイナリで終了コード 0 になるものに（1 ファイル 1 プロセス）、"
                        "--long があればその長い入力に check と fmt --check も（別の欄に）。"
                        "long: 長い入力ごとの check と fmt --check、それぞれの合計と、cpu の時間で最も遅くなった五つ（入力と命令）。"
                        "各欄は壁時計と cpu（子プロセスの user + sys）。cpu も負荷の下では揺れる"
                        "（同じバイナリの A/A で約 55%%、2026-10-20）ので、判定は静かな機械で測る")
    p.add_argument("--rounds", type=int, help="回の数（既定 all 3、long 10）。回ごとの最小を残す")
    p.add_argument("--long", help="長い入力（数万行の .onsa）のディレクトリ。リポジトリには置かない")
    p.add_argument("binaries", nargs="+", metavar="binary")


def probe_args(p):
    p.add_argument("cases", help="the file of the cases: `=== <name>` starts a case (a package), `--- <path>` a file "
                   "of it (none: main.onsa); onsa.toml is added when not given")
    p.add_argument("--out", required=True, help="the directory the packages are written below (<out>/<name>/, emptied first)")
    p.add_argument("--full", action="store_true", help="every output, not a line of the codes per binary")
    p.add_argument("--only", metavar="NAME", help="that case alone")
    p.add_argument("--cmd", default="check --json", help="the command of onsa before the directory (default "
                   "%(default)s; the text form gives the codes of its lines `file:line:col: error[E…]`)")
    p.add_argument("binaries", nargs="+", metavar="binary")
    p.set_defaults(parser_=p)


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
               "バイナリの時間を、回ごとに順を入れ替えて交互に測り、回ごとの最小（壁時計と cpu）を、引数の順の番号と経路の違う部分の名前で並べる",
               "リファクタリングの前後で性能が落ちていないかを測り、報告に並べるとき（rules/refactoring.md 8.2）。前のバイナリは diags と同じ",
               "compare.py speed all <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "probe": C(probe_args, probe, ("i", "b"),
               "一つのファイルに書いた事例（=== でパッケージ、--- でファイル）を --out の下に書き、バイナリごとの終了コードと診断（コードと位置）を事例ごとに一行で並べる（全てのバイナリで同じなら一行）",
               "前からある挙動かを、dev のバイナリと作業のバイナリで比べるとき（壊す側、実装の担当）。dev のバイナリは diags と同じ。--full で全ての出力、--only で一つの事例、--cmd で check --json 以外の命令",
               "compare.py probe cases.txt --out <scratchpad>/probe <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("compare.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
