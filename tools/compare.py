#!/usr/bin/env python3
"""Before and after: the diagnostics, the formatting, the Core and the time of `onsa` binaries (rules/refactoring.md 8;
X-9 X9-18, X9-19; X-6 B1).

Its commands are `diags`, `fmt`, `cst`, `core`, `graph`, `c`, `fixes`, `loops`, `speed`, `run-c` and `probe` (COMMANDS,
rules/tools.md 9.1); `compare.py help` shows them.
`diags` runs `check --json` of both binaries on every case of tests/: the seed files of the gate's fuzz
(`fuzz.seeds`), a file in a package (a directory below tests/ with an `onsa.toml`, the outermost, as the case
harness `onsa_tests::case::collect`) giving way to its directory. It lists the cases whose diagnostics differ in
the code, the place, the message, the titles or the edits of the fix candidates, or the notes (their messages and
places; the notes of one side only are listed below the pair, a line each), and every case where a binary fell
(exited other than 0, 1 and 2, ran out of time, or printed no JSON).
It exits 1 when a case differs (a case where both fell the same way is listed, but does not differ) or when no
case gave JSON on both sides.
`fmt` runs `onsa fmt` of both binaries on the fuzz's seed files, a file at a time, each run on its own copy in a
temporary directory of its own, and lists the files whose exit code, written text, stdout or the names of the files
left in the directory differ. `cst` runs `dump --cst --tree` of both on the fuzz's seed files, a file at a time (the
syntax only: tests/review-phase1 too), and lists those whose exit code or output differ. `core` runs `dump --core` of both on the cases of tests/ and examples (`core_cases`) and
lists those whose exit code or output differ. `graph` runs `graph <flow> <file>` of both on each flow declared at
the head of a line (FLOW_DECL) of each `.onsa` of those inputs, a package's files each (W7-15 U1, X-6 step 8), and
lists the `<file>::<flow>` whose exit code or output differ. `c` builds every target (`build --target … --out`) of
the inputs of `core` as they are in the HEAD of `--root` (a copy of its tests/ but REVIEW and the fuzz's inputs, and examples, `c_builds`),
a file with a manifest in its `// onsa.toml` fragment as a package of its own whose onsa.toml is the fragment without
its `[test]` table (the `manifest` of the list of `onsa_cases`: every file it builds is a case), and lists the builds whose exit code, output (the diagnostics) or files written (the C, the
headers, `onsa_build.json`; of an object or an archive, the name) differ, the out directory named `<out>` and the
package `<pkg>`. All five list the falls and exit 1 as `diags` does, and when no case ran to exit 0 in both binaries.
`fixes` runs `--fix-contract` of two `onsa_cases` on each input given, a process an input (W6-04 U17: the
inputs of a unit that changes the candidates), and sorts the inputs by the candidates before and after and by
whether each kept the contract of §18.1; it lists those broken after, those with fewer candidates after whose
candidates before all kept it, and the falls. Only a fall, or no candidate at all, makes it exit 1.
`loops` runs `--fix-loop --json --branches` of two `onsa_cases` on each input given, with `--pick first` and with
`--pick last`, a process a run (W7-04 U1b: the scripts of W5-24 and W7-04 U1a), and sorts the inputs by the stops of
their walks before and after; it lists those whose walks all ended `clean` or `no-candidate` before and not after,
with the walks after, and the falls. Only a fall, or no input, makes it exit 1.
`speed` measures as the removed `tools/speed.py` did (X9-19), the order of the binaries turned round every other round;
the long inputs get `check` and `fmt --check`, shown apart, and in `all` the inputs of `core` that every binary checks
to exit 0 and the first then lowers (exit 0) get `dump --core`: a binary before a fix may fall lowering an input that
it checks to 0 and the fixed one finds an error in (X-21 P-4); the choosing runs a file a process, out of the timed
rounds. Each binary is named by its place in the arguments and the path past the directories they share; each run
shows the wall seconds and the cpu seconds (user + sys of the children). The cpu seconds swing under load too (about
55% in an A/A of one binary, 2026-10-20): judge on a quiet machine.
`run-c` builds each bench of RUN_C (a package and a main.c, tools/run_c/bench.h) with both binaries, compiles the
C with the same flags (CFLAGS, `-fstack-usage` too) and links it with the bench's main, then runs the two a process
at a time, the order turned round every other round as `speed`, and lists per bench the least time of a run of
`process` before and after and their ratio, the values of the output that differ, and the stack frames of the
functions of the C that differ (S-1264 P4, W8-03 U2: the time of the generated C, which counts of `c` do not show).
`probe` writes the cases of a file (`probe_cases`) as packages below `--out` and runs every binary on each, `check
--json` or `--cmd`, named as in `speed` (W4-03, 70th session: the scripts the agents copied per worktree).
`core` and `c` take `--sub` (the same rewriting of the texts of both binaries before they are compared) and `--lines`
(the texts compared as multisets of lines, the lines of one side only shown): X-27 TU3, the scripts of W7-08 U2 and
W7-07 U1 for the units that change set marks only, or move lines.
"""
import argparse
import io
import json
import os
import re
import resource
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import NamedTuple

sys.dont_write_bytecode = True
import fuzz  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
TIMEOUT = 30  # seconds per run of `diags`, `fmt` and `core`
REVIEW = "tests/review-phase1"  # left by `core`: unknown inputs, not lowered all at once (rules/common.md 3.2)
FLOW_REF_CORPUS = "tests/flow_ref/corpus"  # left by `c`: inputs of the reference evaluator, not cases
PARTS = ((2, "message"), (3, "fix titles"), (4, "fix edits"), (5, "notes"))  # the parts of `diagnostic` a pair names
CASE_NAME = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.-]*")  # a case of `probe`: a directory below --out
DIAG_LINE = re.compile(r"^(.+?):(\d+):(\d+): \w+\[(\w+)\]", re.M)  # the text form: `file:line:col: error[E…]`
BINARY = (".o", ".a")  # files of `build` compared by the name alone
CASES = repo.CASES_CMD  # the list of the cases of `c` (the self-test gives its own)
FIX_COUNTS = re.compile(r"fix-contract: \d+ file\(s\), (\d+) candidate\(s\), \d+ problem\(s\)")  # its last line
PICKS = ("first", "last")  # the `--pick` of `loops`
GOOD = {"clean", "no-candidate"}  # the stops of `--fix-loop` that `loops` takes as ending well
# A flow `graph` compares: declared at the head of a line. One missed (an attribute before it on its line, indented)
# is not compared; one taken by mistake (`flow` at the head of a line in a string) is the same usage error (exit 2)
# in both binaries.
FLOW_DECL = re.compile(r"^(?:pub(?:\(\w+\))? |priv )?flow (\w+)", re.M)
RUN_C = ROOT / "tools/run_c"  # the benches of `run-c`: not below tests, std or examples, so no case nor seed
CC = "clang"
CFLAGS = ("-std=c11", "-O2", "-ffp-contract=off", "-fno-fast-math")  # `run-c`'s, the same for both binaries
REPS = "5"  # the runs a process of a bench of `run-c` times, its least kept (tools/run_c/bench.h)


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
    """The inputs `core` lowers, relative to `root`: the cases of `diags` (tests/fuzz is not among them) but REVIEW
    and the slow cases of `repo.HEAVY`,
    then the files of examples, a package's ones as its directory. Whether an input lowers is its exit code."""
    tests = [rel for rel, _ in fuzz.seeds(root) if not rel.startswith((f"{REVIEW}/", f"{repo.HEAVY}/"))]
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


def note_lines(before: str, after: str) -> list:
    """The notes of a pair (`diagnostic`'s, its message and span) on one side only, counted as a multiset, a line
    each with its place `file:line:col`: `-` before, `+` after (W6-04 U17)."""
    b, a = (Counter(json.dumps(n, sort_keys=True) for n in json.loads(x)) for x in (before, after))
    place = lambda s: f"{s.get('file')}:{s.get('line')}:{s.get('col')}" if s else "(no place)"  # noqa: E731
    return [f"    {sign} {m} {place(s)}" for sign, d in (("-", b - a), ("+", a - b))
            for m, s in map(json.loads, d.elements())]  # fmt: skip


def changes(before, after) -> list:
    """The lines of a case listed: how a binary fell, or the diagnostics of one side only (`-` before, `+`
    after), a pair at the same code and place in one line (`~`) naming the parts that differ, the notes on one side
    only below it (`note_lines`)."""
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
        out += [f"  ~ {g[0]} {g[1]}: " + "; ".join(parts), *note_lines(g[5], n[5])]
    return out + [f"  + {n[0]} {n[1]} {n[2]}" for n in new] or ["  the same diagnostics in another order"]


def executable(parser, b) -> str:
    p = Path(b).resolve()
    if not (p.is_file() and os.access(p, os.X_OK)):
        parser.error(f"{b}: not an executable file")
    return str(p)


def compared(args, units, run, show, ran=None, where="tests", key=lambda r: r) -> int:
    """`run(binary, case)` of both binaries on every case, `--jobs` at a time. Lists the
    cases that differ (by `key` of the results) or fell (a str is a fall), each with `show(before, after)`, and the
    count. No pair compared is no pass: every case fell in both, or, with `ran`, no pair is `ran(before, after)`.
    `where` names, below `--root`, where the cases come from."""
    before, after = (executable(args.parser_, b) for b in (args.before, args.after))
    if not units:
        print(f"{args.cmd}: no case in {where} of {args.root}")
        return 1
    with ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda c: (run(before, c), run(after, c)), units))
    differ = one = both = 0
    for case, (b, a) in zip(units, results):
        fell, other = isinstance(b, str) + isinstance(a, str), key(b) != key(a)
        if other or fell:
            differ, one, both = differ + other, one + (fell == 1), both + (fell == 2)
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
    return out + (files_line(before[3], after[3]) if len(before) > 3 else [])


def files_line(before, after) -> list:
    """`  files: -<name> +<name>`: the names of the files on one side only (none: no line)."""
    gone, new = sorted(set(before) - set(after)), sorted(set(after) - set(before))
    return ["  files: " + " ".join([f"-{n}" for n in gone] + [f"+{n}" for n in new])] if gone or new else []


def substitution(text) -> tuple:
    """(the pattern, the replacement) of `--sub <pattern>=<replacement>`, as bytes: split at the first `=` with no
    backslash before it. A pattern or a replacement that does not read is a usage error."""
    parts = re.split(r"(?<!\\)=", text, maxsplit=1)
    if len(parts) < 2:
        raise argparse.ArgumentTypeError(f"{text!r}: no `=` between the pattern and the replacement")
    try:
        pattern = re.compile(parts[0].encode())
        pattern.sub(parts[1].encode(), b"")  # reads the replacement: a group the pattern has not is an error
    except (re.error, IndexError) as e:
        raise argparse.ArgumentTypeError(f"{text!r}: {e}") from None
    return pattern, parts[1].encode()


def each_text(r, f):
    """`r`, a result of `outcome` or `built`, with `f` applied to each of its texts (the output, the contents of the
    files written); a fall, an exit code, a name and the None of a BINARY file are kept."""
    return f(r) if isinstance(r, bytes) else tuple(each_text(x, f) for x in r) if isinstance(r, tuple) else r


def lines_of(text: bytes) -> list:
    """The lines `--lines` compares: their leading and trailing blanks taken off."""
    return [x.strip() for x in text.split(b"\n")]


def rewritten(args, run, show) -> dict:
    """The `run`, `show` and `key` of `compared` for `core` and `c`: the texts of each run rewritten by every `--sub`
    in order; with `--lines`, compared as multisets of `lines_of` and shown by `line_changes`."""
    def sub(text):
        for pattern, replacement in args.sub:
            text = pattern.sub(replacement, text)
        return text

    out = {"run": lambda b, u: each_text(run(b, u), sub), "show": show}
    multiset = {"show": line_changes, "key": lambda r: each_text(r, lambda t: sorted(lines_of(t)))}
    return out | (multiset if args.lines else {})


def line_changes(before, after) -> list:
    """The lines of a case of `--lines`: how a binary fell, or the exit codes, the files written on one side only
    (`c`), and the lines of each text on one side only, counted as a multiset (`-` before, `+` after), named `output`
    and by the file in `c`."""
    if isinstance(before, str) or isinstance(after, str):
        return texts(before, after)
    nb, na = ({"": r[1]} if len(r) == 2 else {"output ": r[1], **{f"{n} ": t for n, t in r[2] if t is not None}}
              for r in (before, after))  # fmt: skip
    out = [f"  before: exit {before[0]}", f"  after:  exit {after[0]}"]
    out += files_line([n for n, _ in before[2]], [n for n, _ in after[2]]) if len(before) > 2 else []
    for name in [n for n in nb if n in na]:
        b, a = (Counter(lines_of(x[name])) for x in (nb, na))
        out += [f"  {name}{sign} {x.decode('utf-8', 'replace')}" for sign, d in (("-", b - a), ("+", a - b))
                for x in d.elements()]  # fmt: skip
    return out


def fmt(args) -> int:
    rels = [rel for rel, _ in fuzz.seeds(args.root)]
    with tempfile.TemporaryDirectory() as tmp:  # a directory for each run
        return compared(args, rels, lambda b, rel: formatted(b, rel, args.root, tmp), texts, ok)


def cst(args) -> int:
    run = lambda b, rel: outcome([b, "dump", "--cst", "--tree", rel], args.root)  # noqa: E731
    return compared(args, [rel for rel, _ in fuzz.seeds(args.root)], run, texts, ok)


def core(args) -> int:
    units = core_cases(args.root)
    run = lambda b, c: outcome([b, "dump", "--core", c], args.root)  # noqa: E731
    return compared(args, units, ran=ok, where=f"tests (but {REVIEW}) and examples", **rewritten(args, run, texts))


class Flow(NamedTuple):
    file: str  # an `.onsa` of the inputs of `core`, from --root
    name: str

    def __str__(self):
        return f"{self.file}::{self.name}"


def graph_units(root) -> list:
    """[Flow] of `graph`: each `.onsa` of `core_cases` (a package's files each, as `graph` takes a file and looks the
    name up in its module, spec §18.2), each flow its FLOW_DECL names once."""
    out = []
    for case in core_cases(root):
        p = Path(root) / case
        for f in sorted(p.rglob("*.onsa")) if p.is_dir() else [p]:
            names = FLOW_DECL.findall(f.read_bytes().decode("utf-8", "replace"))
            out += [Flow(f.relative_to(root).as_posix(), n) for n in dict.fromkeys(names)]
    return out


def graph(args) -> int:
    run = lambda b, u: outcome([b, "graph", u.name, u.file], args.root)  # noqa: E731
    return compared(args, graph_units(args.root), run, texts, ok, f"the flows of tests (but {REVIEW}) and examples")


class Build(NamedTuple):
    case: str  # the input of `core`, from --root
    package: Path
    target: str

    def __str__(self):
        return f"{self.case} [{self.target}]"


def c_builds(root, tmp) -> list:
    """[Build] of every target of the inputs of `core_cases` in a copy of the HEAD of `root` below `tmp`; the manifest of
    a file is the `manifest` of the list of `onsa_cases` (CASES) of the copy. Raises OSError for a file it does not
    list."""
    tree, packages = Path(tmp) / "head", Path(tmp) / "packages"
    # The corpus of the reference evaluator is no case: its files have no manifest to build with.
    paths = ["tests", f":!{REVIEW}", f":!{repo.HEAVY}", f":!{fuzz.FUZZ_DIR}", f":!{FLOW_REF_CORPUS}", "examples"]
    git = subprocess.run(["git", "-C", str(root), "archive", "HEAD", "--", *paths], capture_output=True)
    if git.returncode:
        raise OSError(f"git archive HEAD in {root}: {git.stderr.decode('utf-8', 'replace').strip()}")
    with tarfile.open(fileobj=io.BytesIO(git.stdout)) as tar:
        tar.extractall(tree, filter="data")
    builds, listed = [], {c["path"]: c["manifest"] for c in repo.cases_json(repo.ROOT, CASES, str(tree))}
    for i, case in enumerate(core_cases(tree)):
        package = tree / case
        manifest = (package / "onsa.toml") if package.is_dir() else None
        if not manifest and case not in listed:
            raise OSError(f"{case}: not a case that `onsa_cases` lists (a file is built with the manifest of its fragment)")
        text = manifest.read_text(encoding="utf-8") if manifest else listed[case]
        if text is not None and not manifest:
            package = packages / str(i)
            package.mkdir(parents=True)
            (package / "onsa.toml").write_text(text, encoding="utf-8")
            shutil.copyfile(tree / case, package / Path(case).name)
        try:
            targets = tomllib.loads(text or "").get("targets")
        except tomllib.TOMLDecodeError:
            targets = None  # no target to build: `check` and `diags` see the error
        builds += [Build(case, package, t) for t in targets] if isinstance(targets, dict) else []
    return builds


def built(binary, b, tmp):
    """(the exit code, stdout and stderr, ((name, bytes, None for BINARY), …) of the files written) of `binary build`
    of the Build `b` into a new directory below `tmp`, removed after; or (a str) how it fell."""
    out = Path(tempfile.mkdtemp(dir=tmp)) / "out"
    try:
        r = subprocess.run([binary, "build", "--target", b.target, "--out", str(out), str(b.package)],
                           cwd=tmp, capture_output=True, timeout=TIMEOUT)  # fmt: skip
        named = lambda x: x.replace(bytes(out), b"<out>").replace(bytes(b.package), b"<pkg>")  # noqa: E731
        files = tuple((p.relative_to(out).as_posix(), None if p.suffix in BINARY else named(p.read_bytes()))
                      for p in sorted(out.rglob("*")) if p.is_file())  # fmt: skip
    except subprocess.TimeoutExpired:
        return f"timeout ({TIMEOUT} s)"
    finally:
        shutil.rmtree(out.parent, ignore_errors=True)
    if r.returncode not in (0, 1, 2):
        head = "".join(f": {h[:100]}" for h in (r.stderr or r.stdout).decode("utf-8", "replace").splitlines()[:1])
        return (f"signal {-r.returncode}" if r.returncode < 0 else f"exit {r.returncode}") + head
    return r.returncode, named(r.stdout + r.stderr), files


def build_lines(before, after) -> list:
    """The lines of a build of `c`: how a binary fell, or the exit codes and the numbers of files, the first line that
    differs of the output and its codes, the files written on one side only, and the first line that differs of each
    file written by both."""
    if isinstance(before, str) or isinstance(after, str):
        return texts(before, after)
    out = [f"  before: exit {before[0]}, {len(before[2])} files", f"  after:  exit {after[0]}, {len(after[2])} files"]
    if before[1] != after[1]:
        codes = [[m[4] for m in DIAG_LINE.finditer(x[1].decode("utf-8", "replace"))] for x in (before, after)]
        out.append(f"  output line {first_line(before[1], after[1])}")
        if codes[0] != codes[1]:
            out.append(f"  codes: {' '.join(codes[0]) or 'none'} -> {' '.join(codes[1]) or 'none'}")
    fb, fa = dict(before[2]), dict(after[2])
    return out + files_line(fb, fa) + [f"  {n} line {first_line(fb[n], fa[n])}" for n in sorted(fb.keys() & fa.keys())
                                       if fb[n] != fa[n]]  # fmt: skip


def c(args) -> int:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = os.path.realpath(tmp)  # as the binaries print it
        try:
            builds = c_builds(args.root, tmp)
        except (OSError, tarfile.TarError, repo.RepoError) as e:
            print(f"c: {e}")
            return 1
        inputs = len({b.case for b in builds})
        print(f"c: {len(builds)} builds of {inputs} inputs with targets in the HEAD of {args.root}")
        run = lambda binary, b: built(binary, b, tmp)  # noqa: E731
        where = f"the HEAD of tests (but {REVIEW}) and examples"
        return compared(args, builds, ran=ok, where=where, **rewritten(args, run, build_lines))


def contract(binary, path):
    """(the candidates, the problem lines) of `binary --fix-contract <path>` (an `onsa_cases`), or (a str) how it
    fell: an exit other than 0 and 1, out of time, no line of the counts last, or a line of the file with no place
    (the file cannot be read, or its check ends in an internal error)."""
    r = outcome([binary, "--fix-contract", path], None)
    if isinstance(r, str):
        return r
    *lines, last = r[1].decode("utf-8", "replace").rstrip("\n").split("\n")
    counts, whole = FIX_COUNTS.match(last), next((x for x in lines if x.startswith(f"{path}: ")), None)
    if r[0] == 2 or not counts or whole:
        return f"exit {r[0]}: {(whole or last)[:100]}"
    return int(counts[1]), lines


def onsa_inputs(args) -> list:
    """The inputs of `fixes` and `loops`: each file given, every .onsa below a directory given (none: says so)."""
    for x in args.inputs:
        if not os.path.exists(x):
            args.parser_.error(f"{x}: no such file or directory")
    units = [str(f) for x in map(Path, args.inputs) for f in (sorted(x.rglob("*.onsa")) if x.is_dir() else [x])]
    if not units:
        print(f"{args.cmd}: no .onsa in {' '.join(args.inputs)}")
    return units


def fixes(args) -> int:
    before, after = (executable(args.parser_, b) for b in (args.before, args.after))
    units = onsa_inputs(args)
    if not units:
        return 1
    with ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda u: (contract(before, u), contract(after, u)), units))
    groups, broke, lost, fell = {}, [], [], []
    held = lambda r: "broke" if r[1] else "held"  # noqa: E731
    for u, (b, a) in zip(units, results):
        if isinstance(b, str) or isinstance(a, str):
            fell += [(u, b, a)]
            continue
        groups.setdefault((b[0], a[0], held(b), held(a)), []).append(u)
        broke += [(f"{u} (before {held(b)}, {b[0]} -> {a[0]})", a[1])] if a[1] else []
        lost += [f"{u} {b[0]} -> {a[0]}"] if a[0] < b[0] and not b[1] else []
    ran = [r for r in results if not any(isinstance(x, str) for x in r)]
    sums = [sum(f(r[i]) for r in ran) for f in (lambda x: x[0], lambda x: len(x[1])) for i in (0, 1)]
    print(f"{len(units)} inputs, {len(fell)} fell; candidates {sums[0]} -> {sums[1]}, problems {sums[2]} -> {sums[3]}")
    print("candidates before -> after, before, after: inputs, the first")
    for (cb, ca, hb, ha), us in sorted(groups.items()):
        print(f"  {cb} -> {ca}, {hb}, {ha}: {len(us)}  {us[0]}")
    print(f"broke after: {len(broke)}", *[x for u, lines in broke for x in (u, *(f"  {n}" for n in lines))], sep="\n")
    print(f"fewer candidates after, before held (a candidate that held lost?): {len(lost)}", *lost, sep="\n")
    show = lambda r: r if isinstance(r, str) else f"{r[0]} candidate(s), {len(r[1])} problem(s)"  # noqa: E731
    print(f"fell: {len(fell)}", *[x for u, b, a in fell for x in (u, f"  before: {show(b)}", f"  after:  {show(a)}")],
          sep="\n")  # fmt: skip
    if not sums[0] + sums[1]:
        print(f"fixes: no candidate in {' '.join(args.inputs)}")
    return 1 if fell or not sums[0] + sums[1] else 0  # a difference is no failure; none judged is no pass


def walked(binary, path, pick):
    """The report of `binary --fix-loop --json --branches --pick <pick> <path>` (an `onsa_cases`), or (a str) how it
    fell: an exit other than 0 and 1, out of time, no report of one file in the JSON, or the check of the file itself
    ended in an internal error or could not read it."""
    r = outcome([binary, "--fix-loop", "--json", "--branches", "--pick", pick, path], None)
    if isinstance(r, str) or r[0] == 2:
        return r if isinstance(r, str) else f"exit 2: {r[1].decode('utf-8', 'replace')[:100]}"
    try:
        (report,) = json.loads(r[1])
        if not (isinstance(report["stops"], dict) and isinstance(report["walks"], list)):
            raise TypeError("stops or walks")
    except (ValueError, TypeError, KeyError) as e:
        return f"exit {r[0]}: no report in the JSON ({type(e).__name__}: {e})"[:150]
    bad = next((f"{k}: {report[k]}" for k in ("internal", "unreadable") if report.get(k)), None)
    return bad[:150] if bad else report


def ends(report) -> str:
    """The stops of the walks of a report, as `clean+no-candidate`."""
    return "+".join(sorted(report["stops"])) or "none"


def walk_lines(w) -> list:
    """A walk of a report, as the text form of `--fix-loop` prints it."""
    how = f" ({w['how']} {w['back_to']})" if w.get("how") else ""
    head = f"  {w['stop']}{how} after {len(w['steps'])} steps{': ' + w['message'][:100] if w.get('message') else ''}"
    return [head, *(f"    {i}. {s['code']} {s['line']}:{s['col']} candidate {s['candidate']}/{s['of']} `{s['title']}`"
                    f" -> {'?' if s['errors'] is None else s['errors']} errors" for i, s in enumerate(w["steps"], 1))]


def loops(args) -> int:
    before, after = (executable(args.parser_, b) for b in (args.before, args.after))
    units = onsa_inputs(args)
    if not units:
        return 1
    runs = [(u, p) for u in units for p in PICKS]
    with ThreadPoolExecutor(args.jobs) as ex:
        results = dict(zip(runs, ex.map(lambda r: (walked(before, *r), walked(after, *r)), runs)))
    fell = [u for u in units if any(isinstance(x, str) for p in PICKS for x in results[u, p])]
    ran = [(u, p, b, a) for (u, p), (b, a) in results.items() if u not in fell]
    names = sorted({s for *_, b, a in ran for s in (*b["stops"], *a["stops"])})
    sums = ", ".join(f"{s} {sum(b['stops'].get(s, 0) for *_, b, _ in ran)} -> "
                     f"{sum(a['stops'].get(s, 0) for *_, a in ran)}" for s in names)  # fmt: skip
    print(f"{len(units)} inputs, {len(fell)} fell; walks by stop, before -> after: {sums or 'none'}")
    groups = {}
    for u, p, b, a in ran:
        groups.setdefault((p, ends(b), ends(a)), []).append(u)
    print("--pick, stops before -> after: inputs, the first", *[f"  {p}, {eb} -> {ea}: {len(us)}  {us[0]}"
          for (p, eb, ea), us in sorted(groups.items())], sep="\n")  # fmt: skip
    worse = [(u, p, b, a) for u, p, b, a in ran if set(b["stops"]) <= GOOD and not set(a["stops"]) <= GOOD]
    print(f"worse after (before all {' or '.join(sorted(GOOD))}): {len(worse)}", *[x for u, p, b, a in worse for x in (
        f"{u} (--pick {p}, {ends(b)} -> {ends(a)})", *(y for w in a["walks"] if w["stop"] not in GOOD
                                                       for y in walk_lines(w)))], sep="\n")  # fmt: skip
    show = lambda r: r if isinstance(r, str) else ends(r)  # noqa: E731
    print(f"fell: {len(fell)}", *[x for u in fell for x in (u, *(f"  --pick {p} {side} {show(r)}" for p in PICKS
          for side, r in zip(("before:", "after: "), results[u, p])))], sep="\n")  # fmt: skip
    return 1 if fell else 0  # a difference is no failure


def ok_run(argv) -> bool:
    """`argv` run in ROOT exits 0."""
    r = outcome(argv, ROOT)
    return not isinstance(r, str) and r[0] == 0


def core_inputs(binaries) -> tuple:
    """(the inputs of `compare.py core`, those every binary checks to exit 0, the paths of those the first of them
    then lowers to exit 0) in ROOT, a file a process: the column `core` of `speed all` times lowering, not inputs that
    stop at `check`, and no binary lowers an input another finds an error in."""
    units, bins = core_cases(ROOT), list(dict.fromkeys(map(os.path.realpath, binaries)))
    checked = [c for c in units if all(ok_run([b, "check", c]) for b in bins)]
    return units, checked, [ROOT / c for c in checked if ok_run([binaries[0], "dump", "--core", c])]


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
        units, checked, lowered = core_inputs(a.binaries)
        runs = {"check": (["check"], files), "fmt": (["fmt", "--check"], files), "core": (["dump", "--core"], lowered)}
        if long:
            runs.update({"long": (["check"], long), "long fmt": (["fmt", "--check"], long)})
        best = [dict.fromkeys(runs, (1e9, 1e9)) for _ in order]
        for r in range(rounds):
            for i, b in turn(order, r):
                for k, (argv, fs) in runs.items():
                    best[i][k] = least(best[i][k], timed(b, argv, fs))
        core_of = f"{len(lowered)} for core: {len(checked)} of {len(units)} checked to 0 by every binary"
        print(f"{len(files)} files ({core_of}), {len(long)} long inputs, {rounds} rounds; {unit}")
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


def benches(where) -> list:
    """The names of the benches of `run-c` in `where`: its directories with an onsa.toml (none if it is none)."""
    return sorted(p.name for p in Path(where).iterdir() if (p / "onsa.toml").is_file()) if Path(where).is_dir() else []


def ran(argv, cwd):
    """The stdout (bytes) of `argv` run in `cwd` to exit 0, or (a str) how it ended: the program, the exit or the
    signal, the first line of its output."""
    try:
        r = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=TIMEOUT)
    except (subprocess.TimeoutExpired, OSError) as e:
        return f"{Path(argv[0]).name}: {type(e).__name__}"
    if r.returncode == 0:
        return r.stdout
    head = "".join(f": {h[:100]}" for h in (r.stderr or r.stdout).decode("utf-8", "replace").splitlines()[:1])
    how = f"signal {-r.returncode}" if r.returncode < 0 else f"exit {r.returncode}"
    return f"{Path(argv[0]).name}: {how}{head}"


def stack_frames(su: str) -> dict:
    """{function: bytes} of the lines `<file>:<line>:<col>:<function>\\t<bytes>\\t<kind>` of `clang -fstack-usage`."""
    fields = (line.split("\t") for line in su.splitlines())
    return {f[0].rsplit(":", 1)[-1]: int(f[1]) for f in fields if len(f) == 3 and f[1].isdigit()}


def measured(stdout: bytes):
    """(the least nanoseconds, the value of the output) of the line of a bench's main (bench.h), or (a str) what
    is wrong with it."""
    parts = stdout.decode("utf-8", "replace").split()
    if len(parts) != 2 or not parts[0].isdigit():
        return f"no line `<ns> <value>`: {stdout[:80]!r}"
    return int(parts[0]), parts[1]


def bench_exe(binary, bench: Path, tmp):
    """(the executable of `bench` built by `binary` and linked with its main.c, {function: the bytes of its stack
    frame} of the C built) in a new directory below `tmp`, or (a str) the step that failed and how."""
    d = Path(tempfile.mkdtemp(dir=tmp))
    out = d / "out"
    if isinstance(r := ran([binary, "build", "--target", "host", "--out", str(out), str(bench)], d), str):
        return r
    sources = sorted(out.glob("*.c"))
    objects = [f"{d / c.stem}.o" for c in sources]  # an object a C file, its .su beside it
    steps = [[CC, *CFLAGS, "-fstack-usage", "-c", str(c), "-o", o] for c, o in zip(sources, objects)]
    for argv in [*steps, [CC, *CFLAGS, f"-I{out}", str(bench / "main.c"), *objects, "-o", "bench", "-lm"]]:
        if isinstance(r := ran(argv, d), str):
            return r
    return str(d / "bench"), {k: v for c in sources for k, v in stack_frames((d / f"{c.stem}.su").read_text()).items()}


def bench_lines(name, sides) -> tuple:
    """(it fell or its values differ, its lines) of a bench of `run-c`: of [(the least ns of the rounds, {values},
    {function: frame}) or (a str) how it fell] of before and after, the line of the table (ms, ms, after / before),
    then the values or the falls, and the stack frames that differ (a function on one side only as `-`)."""
    if any(isinstance(s, str) for s in sides):
        falls = [f"  {w}: {s}" for w, s in zip(("before", "after"), sides) if isinstance(s, str)]
        return True, [f"{name:10} fell", *falls]
    (nb, vb, fb), (na, va, fa) = sides
    out = [f"{name:10} {nb / 1e6:9.3f} {na / 1e6:9.3f} {na / nb:7.3f}"]
    if differ := len(vb | va) > 1:  # between the sides, or between the rounds of one
        out.append(f"  value differs: before {' '.join(sorted(vb))}, after {' '.join(sorted(va))}")
    return differ, out + [f"  stack {f}: {fb.get(f, '-')} -> {fa.get(f, '-')}" for f in sorted(fb.keys() | fa.keys())
                          if fb.get(f) != fa.get(f)]  # fmt: skip


def run_c(a) -> int:
    names = benches(a.benches)
    if not 1 <= a.rounds <= 100:
        a.parser_.error(f"--rounds {a.rounds}: give 1 to 100")
    if a.only and a.only not in names:
        a.parser_.error(f"--only {a.only}: no bench of that name in {a.benches} ({', '.join(names)})")
    names = [a.only] if a.only else names
    if not names:
        print(f"run-c: no bench in {a.benches}")
        return 1
    binaries = [executable(a.parser_, b) for b in (a.before, a.after)]
    with tempfile.TemporaryDirectory() as tmp:
        sides = {n: [bench_exe(b, Path(a.benches) / n, tmp) for b in binaries] for n in names}
        times = {n: [(1 << 62, set()) for _ in binaries] for n in names}
        for r in range(a.rounds):  # a process at a time: run side by side, the times swing
            for n in names:
                for i in turn([0, 1], r):
                    if isinstance(sides[n][i], str):
                        continue
                    got = ran([sides[n][i][0], REPS], tmp)
                    got = got if isinstance(got, str) else measured(got)
                    if isinstance(got, str):
                        sides[n][i] = got
                    else:
                        times[n][i] = (min(times[n][i][0], got[0]), times[n][i][1] | {got[1]})
    rows = {n: [s if isinstance(s, str) else (*times[n][i], s[1]) for i, s in enumerate(sides[n])] for n in names}
    print(f"run-c: {len(names)} benches, {a.rounds} rounds of {REPS} runs; "
          "the least ms of a run: before, after, after / before")
    shown = [bench_lines(n, rows[n]) for n in names]
    print(*(x for _, lines in shown for x in lines), sep="\n")
    return 1 if any(bad for bad, _ in shown) else 0  # a time is no failure


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


def rewrite_args(p):
    diags_args(p)
    p.add_argument("--sub", action="append", default=[], type=substitution, metavar="PATTERN=REPLACEMENT",
                   help=r"両方のバイナリの出力（core は dump の出力、c は診断の出力と書いたファイルの中身）に当ててから比べる置き換え。"
                        r"最初の、\ の後でない = で、型（Python の正規表現、バイト列に当てる）と置き換え（\1 などの群の参照が使える）に分ける。"
                        r"型の中の = は \= と書く。繰り返すと書いた順に当てる。型か置き換えが読めなければ使い方の誤り（終了コード 2）")
    p.add_argument("--lines", action="store_true",
                   help="出力を行の多重集合として比べ（行の前後の空白は外すので、字下げだけの違いは数えない。見るときは付けずに回す）、"
                        "違う入力ごとに終了コードと、前だけの行（-）・後だけの行（+）を出す。並べ替えだけの違いは違いにならない。"
                        "c は診断の出力を output、書いたファイルをその名前で行の前に付け、片方だけのファイルは files の行。"
                        "--sub と一緒なら置き換えた後の行で比べる。終了コードの決まりは付けないときと同じ")


def fixes_args(p):
    p.add_argument("before", help="前の onsa_cases")
    p.add_argument("after", help="後の onsa_cases")
    p.add_argument("inputs", nargs="+", metavar="input", help="入力のファイルかディレクトリ（その下の全ての .onsa）")
    p.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2), help="同時に回す入力の数（既定: コアの数の半分）")
    p.epilog = ("出力: 一行目に入力・落ちた数と、候補と問題の数の合計（前 -> 後）。次に（候補の数 前 -> 後、前、後）の組ごとの入力の数と最初の入力"
                "（held は問題の行が無い、broke はある）。その後に、後で破った入力（前の状態と後の問題の行）、"
                "候補が減り前は守っていた入力（守った候補が消えたかを見る）、落ちた入力（0・1 の外の終了、時間切れ、数の行が無い、"
                "ファイルの位置の無い行: 読めないか内部エラー）。落ちた入力があるか、候補が前後とも 0 なら終了コード 1。違いは失敗にしない")
    p.set_defaults(parser_=p)


def loops_args(p):
    fixes_args(p)
    p.epilog = ("出力: 一行目に入力・落ちた数と、止まり方ごとの道筋の数の合計（--pick の両方、前 -> 後）。次に（--pick、前の止まり方 -> 後の止まり方）の組"
                "ごとの入力の数と最初の入力（止まり方は報告の stops の名前を + でつないだもの）。その後に、後で悪くなった入力（前は全ての道筋が clean か "
                "no-candidate で、後はそれ以外がある）と後のその道筋（段ごとに診断・位置・候補・後の誤りの数）、落ちた入力（どれかの回が 0・1 の外の終了、"
                "時間切れ、一つのファイルの報告の JSON が無い、ファイルそのものの検査の内部エラーか読めない）。落ちた入力があるか、入力が無ければ終了コード 1。"
                "違いは失敗にしない")  # fmt: skip


def speed_args(p):
    p.add_argument("mode", choices=["all", "long"],
                   help="all: check と fmt --check を tests・std・examples の全ての .onsa に、"
                        "dump --core を core の入力のうち、与えた全てのバイナリの check が終了コード 0 で、"
                        "その後に最初のバイナリの dump --core が 0 になるものに（選ぶ回も 1 ファイル 1 プロセスで、測る回の外）、"
                        "--long があればその長い入力に check と fmt --check も（別の欄に）。"
                        "long: 長い入力ごとの check と fmt --check、それぞれの合計と、cpu の時間で最も遅くなった五つ（入力と命令）。"
                        "各欄は壁時計と cpu（子プロセスの user + sys）。cpu も負荷の下では揺れる"
                        "（同じバイナリの A/A で約 55%%、2026-10-20）ので、判定は静かな機械で測る")
    p.add_argument("--rounds", type=int, help="回の数（既定 all 3、long 10）。回ごとの最小を残す")
    p.add_argument("--long", help="長い入力（数万行の .onsa）のディレクトリ。リポジトリには置かない")
    p.add_argument("binaries", nargs="+", metavar="binary")


def run_c_args(p):
    p.add_argument("before")
    p.add_argument("after")
    p.add_argument("--rounds", type=int, default=3,
                   help="本ごとに、前と後の実行を交互に（回ごとに順を入れ替えて）回す数（1〜100、既定 %(default)s）。回の間の最小を残す")
    p.add_argument("--only", metavar="NAME", help="その本だけ（知らない名前は使い方の誤り）")
    p.add_argument("--benches", default=str(RUN_C), help="本のディレクトリ（既定 tools/run_c。自己テストが替える）")
    p.epilog = ("出力: 本ごとに一行（一回の実行の最小の ms の前と後、後 / 前）。その下に、出力の値（最後の回の全てのサンプルのビットの"
                "ハッシュと和）が前後か回の間で違えば value differs、ビルド・リンク・実行が 0 以外で終われば fell とその段、"
                "生成した C の関数ごとのスタックの枠（clang -fstack-usage）が違う関数（片方だけは -）。値の違いか落ちた本があれば"
                "終了コード 1、速さの違いは失敗にしない。揺れ: 同じバイナリを前と後に渡した比は 0.997〜1.003 の内（2026-11-28、"
                "静かな機械の 5 回。--rounds 1 でも同じ）。1.01 を超える本が二度続けて回しても出たら遅くなったと読み、一つずつ説明する。"
                "他のビルドや検査と重なると揺れが大きくなるので、一本ずつ静かな時に回す")
    p.set_defaults(parser_=p)


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
               "二つのバイナリの check --json を tests/ の事例（fuzz の種。パッケージはディレクトリで）に回し、診断（コード・位置・メッセージ・候補の題と編集・note）が違う事例と落ちた事例を並べる。note が違う組は ~ の行の下に、前だけの note（-）と後だけの note（+）を文と位置で一行ずつ（同じ note の数の違いも）",
               "リファクタリングや診断の文面の直しの前後で、診断と候補が変わっていないか（変わった所が意図どおりか）を見るとき。前のバイナリは主のツリーの target/base/<基>/ にある（基は作業ツリーの git merge-base dev HEAD の短い SHA）",
               "compare.py diags <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "fmt": C(diags_args, fmt, ("parent", "i", "b"),
             "二つのバイナリの fmt を、fuzz の種の .onsa を 1 回ごとに一時のディレクトリに写して回し、終了コード・書いた後のファイル・stdout・ディレクトリに残ったファイルの名前のどれかが違う事例と落ちた事例を並べる",
             "字句・行の配置・fmt のリファクタリングの前後で、整形の結果が変わっていないかを見るとき（マージの前の確かめ）。前のバイナリは diags と同じ",
             "compare.py fmt <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "cst": C(diags_args, cst, ("parent", "i", "b"),
             "二つのバイナリの dump --cst --tree を fuzz の種の .onsa に 1 ファイルずつ回し（構文だけなので tests/review-phase1 も）、終了コードか出力（CST の木）が違うファイルと落ちたファイルを並べる。両方で終了コード 0 のファイルが無ければ失敗",
             "字句・構文解析のリファクタリングの前後で、CST が変わっていないかを見るとき（diags と fmt より直接。AST への降下は見ない）。前のバイナリは diags と同じ",
             "compare.py cst <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "core": C(rewrite_args, core, ("parent", "i", "b"),
              "二つのバイナリの dump --core を、tests/ の事例（diags と同じ。未知の入力を持つ tests/review-phase1 は、"
              "降下に進む命令に一括でかけないので除く。rules/common.md 3.2）と examples（パッケージはディレクトリで）に回し、終了コードか出力が違う入力と落ちた入力を並べる。両方で終了コード 0 の入力が無ければ失敗",
              "意味解析・降下のリファクタリングの前後で、Core IR が変わっていないかを見るとき（check を回す diags では降下を確かめられない）。前のバイナリは diags と同じ。"
              "決めた印だけが変わる単位は --sub で両方を置き換えて、行の並べ替えだけの単位は --lines で比べる",
              "compare.py core <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "graph": C(diags_args, graph, ("parent", "i", "b"),
               "二つのバイナリの graph <flow> <ファイル> を、core の入力の各 .onsa（パッケージは中のファイルごと）の行頭で宣言した flow ごとに回し、"
               "終了コードか出力（DOT）が違う <ファイル>::<flow> と落ちたものを並べる。行頭でない宣言（同じ行の前に属性がある、字下げした）は比べない。両方で終了コード 0 の flow が無ければ失敗",
               "graph の作り（計画の辺・描き方）を変える単位の前後で、出力が変わっていないか（変わった所が意図どおりか）を見るとき。前のバイナリは diags と同じ",
               "compare.py graph <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "c": C(rewrite_args, c, ("parent", "i", "b"),
           "二つのバイナリの build を、HEAD の tests/（tests/review-phase1 と fuzz の入力を除く）と examples の写しで、core と同じ入力の全てのターゲットに回し"
           "（マニフェストを断片に持つファイルは、断片から [test] を除いた onsa.toml の一つのパッケージにして）、終了コード・出力（診断）・書いたファイル"
           "（C、ヘッダ、onsa_build.json。.o と .a は名前だけ）が違うビルドと落ちたビルドを並べる",
           "後端・降下の変更の前後で、生成する C とビルドの診断が変わっていないか（変わった所が意図どおりか）を見るとき。前のバイナリは diags と同じ。"
           "入力は HEAD のものなので、作業ツリーで書き換えた事例は前のまま比べる。--sub と --lines は core と同じ",
           "compare.py c <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "fixes": C(fixes_args, fixes, ("parent", "i", "b"),
               "二つの onsa_cases の --fix-contract を入力ごとに一つずつ回し、候補の数（前 -> 後）と約束を守ったか破ったかの組に分け、後で破った入力と、候補が減り前は守っていた入力と、落ちた入力を並べる",
               "修正候補を変える単位で、生成した入力の格子の前後の違いを、前の候補が約束（§18.1）を守っていたかで仕分けるとき（正しい候補が消えていないか）。前のバイナリは主のツリーの target/base/<基>/onsa_cases",
               "compare.py fixes <主のツリー>/target/base/<基>/onsa_cases target/debug/onsa_cases <scratchpad>/grid"),
    "loops": C(loops_args, loops, ("parent", "i", "b"),
               "二つの onsa_cases の --fix-loop --json --branches を入力ごとに --pick first と last で一つずつ回し、--pick と止まり方（前 -> 後）の組に分け、後で悪くなった入力（前は clean か no-candidate だけ、後は cycle・limit・diverge など）と後の道筋と、落ちた入力を並べる",
               "修正候補を変える単位で、生成した入力の格子の前後の止まり方を比べるとき（候補を当て続けて収束するか止まるか、§18.1、rules/criteria.md の fix-loop の行）。前のバイナリは fixes と同じ",
               "compare.py loops <主のツリー>/target/base/<基>/onsa_cases target/debug/onsa_cases <scratchpad>/grid"),
    "speed": C(speed_args, speed, ("parent", "i", "b"),
               "バイナリの時間を、回ごとに順を入れ替えて交互に測り、回ごとの最小（壁時計と cpu）を、引数の順の番号と経路の違う部分の名前で並べる",
               "リファクタリングの前後で性能が落ちていないかを測り、報告に並べるとき（rules/refactoring.md 8.2）。前のバイナリは diags と同じ",
               "compare.py speed all <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
    "run-c": C(run_c_args, run_c, ("parent", "i", "b"),
               "tools/run_c の本（Onsa のパッケージと手書きの C の main）を二つのバイナリで build し、同じ clang -O2 の旗で main と繋いで"
               "一本ずつ順に回し、本ごとの process の輪の最小の時間と比、出力の値の食い違い、関数ごとのスタックの枠の違いを並べる",
               "生成する C の形を変える単位（W8-03・W8-05・W8-07 の出力を変える単位）の受け入れで、生成コードの実行の時間が落ちていないかを"
               "測るとき（S-1264 の P4。gate には入れない）。前のバイナリは diags と同じ。遅くなった本は一つずつ説明する",
               "compare.py run-c <主のツリー>/target/base/<基>/onsa target/debug/onsa"),
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
