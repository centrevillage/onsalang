#!/usr/bin/env python3
"""The short fuzzing of `onsa check` and `onsa fmt` (Q-06, plan D-16 6, W1-04).

The properties: whatever the input, the compiler does not fail inside
(S-67), and a fix candidate does not leave an error at its own place (the
near "same place" of the contract of §18.1, S-236, W3-17; 3. below). A run
is a crash when the command exits with a code other than 0, 1 and 2 (101 is
the internal error; a signal is a crash too, a stack overflow included,
S-183), prints a raw Rust panic, or runs longer than `TIMEOUT`.

The gate item `fuzz` (this script without options) does three things:

1. **Replay.** Every saved input `tests/fuzz/*.onsa` runs through both
   commands and the fix stage (3.). An input listed in `tests/pending.toml`
   (kind `fuzz-input`) must still crash or break the contract of a fix
   candidate: when it does neither, the work fixed it, and the entry goes
   (the file stays, as a regression input). An input not listed must do
   neither.
2. **Fuzz.** Every `.onsa` file under `tests/` (but `tests/fuzz`) is a seed.
   Each seed gives `--per-seed` mutants from a random generator seeded with
   the seed's path and bytes. A mutant also inserts tokens of the whole
   corpus and splices lines of other seeds, so the mutants depend on every
   seed: the run is the same for the same tree on every machine, and adding
   or changing a seed may change the mutants of the others. A crash of a
   class (`signature`) that a listed input also shows is known.
   A crash of a new class fails the gate: its first input is minimized and
   written to `target/fuzz/new/`, with the entry to add (the gate writes
   nothing under `tests/`; `--save` copies the inputs into `tests/fuzz/`).
3. **Fix candidates** (S-236, W3-17). One mutant in `FIX_EVERY` (a fixed
   rule: the mutants whose index in the run is a multiple of it), and every
   saved input, go through the near "same place" of the contract of the fix
   candidates (spec §18.1): `onsa_cases --fix-same-place` applies the first
   candidate of each diagnostic alone, checks the file again, and reports a
   diagnostic of the original's stage or an earlier one whose start lies in
   the original's range or a replacement, moved to the text after it (an
   error the input held there before is not one, but one of the original's
   code inside its range is: a part of the same form, S-248). Its
   class is `fix|<code>|<title>|<code left>` (the quoted text of the title
   `…`, the numbers `#`). A saved input listed in `tests/pending.toml` must
   still crash or break the contract; one not listed must do neither; a
   class a listed input shows is known, a new one is minimized and written
   as above. The units are not used: this is a net for new kinds of broken
   candidates, not the contract (the test runner checks the contract on the
   cases, `onsa_tests::fix_contract`).

Inputs are bytes: the seeds and the saved inputs are read and written as
they are (a `\r` stays, invalid UTF-8 too).

    tools/fuzz.py [--per-seed N] [--version V] [--jobs N] [--binary PATH]
                  [--cases-binary PATH] [--time-budget S] [--deep] [--save]

`--deep` adds mutants that nest brackets or blocks thousands deep: the
nesting limit (spec §2.5, S-183, W3-14) must stop them with E0006 before
the stack runs out. The gate runs them only at a stage end (the item
`fuzz-deep`, W3-03): they are heavy on the machine. (W3-14 ran them once: no
signal; `fmt --check` timed out on the 20002 lexer diagnostics of a string
nesting `{ ` 20000 deep, one per unit since W3-03, S-214;
`tests/fuzz/8858ce8c.onsa`.) A signal is not saved under `tests/` (with `--save`
it goes to `target/fuzz/new/`): a stack overflow aborts the process, and
the system writes a crash report for each one.

The compiler is `<target directory>/debug/onsa`, the target directory of
`cargo metadata` (which follows `CARGO_TARGET_DIR` and the cargo
configuration), unless `--binary` names it; the fix stage runs
`<target directory>/debug/onsa_cases` (`--cases-binary`). `--time-budget` bounds the
whole run: when it is spent, the remaining mutants do not run and the item
fails (it never passes on fewer inputs than it says).

Exit 0 when nothing new crashes and the replay agrees with the list, 1
otherwise, 2 on a usage error (or when the compiler cannot be built).
"""
import argparse
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
FUZZ_DIR = repo.FUZZ_DIR
# The commands of Q-06; `fmt --check` reads and does not write.
COMMANDS = (("check",), ("fmt", "--check"))
TIMEOUT = 20  # seconds per run
PER_SEED = 10
# Changing the version changes every mutant (a new set of inputs).
VERSION = "2"
MINIMIZE_RUNS = 400
MINIMIZE_SECONDS = 60  # per crash class
# One mutant in FIX_EVERY goes through the fix stage (W3-17); the saved inputs all do.
FIX_EVERY = 4
# The paths given to one run of `onsa_cases --fix-same-place`.
FIX_BATCH = 400
FIX_COMMAND = "fix-same-place"
TIME_BUDGET = 600  # seconds for the whole run
# Nesting depths of the deep mutants (S-183): far above the nesting limit
# (256, spec §2.5) and above what the stack of a command would hold without it.
DEPTHS = (2000, 5000, 20000)
DEEP = (("(", ")"), ("{ ", " }"), ("[", "]"), ("-", ""), ("!", ""))

# Inserted as they are: unbalanced brackets, quotes, escapes, characters of
# more than one byte, invisible and control characters, extreme literals.
SPECIAL = (
    "{", "}", "(", ")", "[", "]", '"', "'", "\\", "~", "^", "@", "|", "\n", "\t", "\r",
    "音", "é", "。", "​", "\x00",
    "0x", "1e999", "99999999999999999999999999999999999999", "0.", "-",
)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|\d+(?:\.\d+)?|[^\sA-Za-z0-9_]{1,2}")


@dataclass(frozen=True)
class Crash:
    signature: str  # the class: the same bug gives the same signature
    command: str
    detail: str  # what the command printed, shortened


def message_head(message):
    """The part of a message that names the bug: the numbers become `#`, a
    quoted character `'?'`, and from the first quoted text with a space or a
    character outside ASCII (source text, which may hold backquotes itself)
    to the end `…`; a quoted name before it (`Option::unwrap()`) stays. The
    first 80 characters."""
    m = message
    for q in re.finditer(r"`[^`]*`?", message):
        if re.search(r"[\s\x80-\U0010ffff]", q.group(0)):
            m = message[: q.start()] + "`…`"
            break
    m = re.sub(r"'.'", "'?'", m)
    m = re.sub(r"\d+", "#", m)
    m = re.sub(r"\s+", " ", m).strip()
    return m[:80]


def classify(command, returncode, stderr, timed_out=False):
    """The crash of one run, or None."""
    name = " ".join(command)
    if timed_out:
        return Crash("timeout", name, f"more than {TIMEOUT} s")
    lines = stderr.splitlines()
    raw = next((l for l in lines if "panicked at" in l or "has overflowed its stack" in l), None)
    if returncode in (0, 1, 2) and raw is None:
        return None
    if returncode == 101 and raw is None:
        # The message runs from `onsa: internal error:` to the position lines.
        start = next((i for i, l in enumerate(lines) if l.startswith("onsa: internal error:")), None)
        body = []
        if start is not None:
            body.append(lines[start].removeprefix("onsa: internal error:"))
            for l in lines[start + 1:]:
                if l.startswith("  --> ") or l.startswith("  = "):
                    break
                body.append(l)
        message = "\n".join(body).strip() or (lines[0] if lines else "")
        where = next((l.strip()[len("= at "):] for l in lines if l.strip().startswith("= at ")), "")
        where = re.sub(r":\d+:\d+$", "", where)
        return Crash(f"internal|{where or '-'}|{message_head(message)}", name, "\n".join(lines[:4]))
    if returncode < 0:
        # A stack overflow names no place in the compiler: the command does.
        last = message_head(raw or (lines[-1] if lines else ""))
        return Crash(f"signal {-returncode}|{name}|{last}", name, "\n".join(lines[-3:]))
    return Crash(f"exit {returncode}|{message_head(raw or '')}", name, "\n".join(lines[:4]))


class Runner:
    """Runs the compiler on inputs, each in a directory of its own."""

    def __init__(self, argv, work):
        self.argv = list(argv)
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)

    def crashes(self, text, commands=COMMANDS):
        """The crashes of the commands on `text` (a str whose bytes are
        `encode(text)`)."""
        d = Path(tempfile.mkdtemp(dir=self.work))
        try:
            path = d / "m.onsa"
            path.write_bytes(encode(text))
            out = []
            for cmd in commands:
                try:
                    r = subprocess.run(
                        [*self.argv, *cmd, str(path)], capture_output=True, timeout=TIMEOUT
                    )
                    c = classify(cmd, r.returncode, r.stderr.decode("utf-8", "replace"))
                except subprocess.TimeoutExpired:
                    c = classify(cmd, None, "", timed_out=True)
                if c:
                    out.append(c)
            return out
        finally:
            shutil.rmtree(d, ignore_errors=True)


def fix_signature(v):
    """The class of a violation of the near "same place" (S-236): the code,
    the title of the candidate (its quoted text `…`, its numbers `#`) and
    the code left after it."""
    title = re.sub(r"`[^`]*`", "`…`", v["title"])
    title = re.sub(r"\d+", "#", re.sub(r"\s+", " ", title)).strip()[:80]
    return f"fix|{v['code']}|{title}|{v['left']}"


class FixRunner:
    """Runs `onsa_cases --fix-same-place` on inputs, written to a directory
    of their own (W3-17)."""

    def __init__(self, argv, work):
        self.argv = list(argv)
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)
        # Inputs `onsa check` cannot read either (not UTF-8): no candidate to check, counted.
        self.unreadable = 0

    def violations(self, texts, timeout=TIME_BUDGET):
        """For each text, its violations as `Crash`es (the command is
        `FIX_COMMAND`). Raises RuntimeError when the tool fails (never a
        silent pass)."""
        d = Path(tempfile.mkdtemp(dir=self.work))
        try:
            paths = []
            for i, text in enumerate(texts):
                path = d / f"m{i}.onsa"
                path.write_bytes(encode(text))
                paths.append(str(path))
            out = []
            deadline = time.monotonic() + timeout
            for start in range(0, len(paths), FIX_BATCH):
                batch = paths[start:start + FIX_BATCH]
                left = deadline - time.monotonic()
                if left <= 0:
                    raise RuntimeError(f"the time ran out after {start} of {len(paths)} inputs")
                try:
                    r = subprocess.run([*self.argv, "--" + FIX_COMMAND, *batch], capture_output=True, timeout=left)
                except subprocess.TimeoutExpired:
                    raise RuntimeError(f"timed out after {start} of {len(paths)} inputs") from None
                try:
                    items = json.loads(r.stdout) if r.returncode == 0 else None
                except ValueError:
                    items = None
                if not isinstance(items, list) or len(items) != len(batch):
                    err = r.stderr.decode("utf-8", "replace").strip().splitlines()
                    raise RuntimeError(f"exit {r.returncode}: {err[-1] if err else 'no list of results'}")
                for item in items:
                    if item.get("unreadable"):
                        self.unreadable += 1
                    out.append([violation_crash(v) for v in item.get("violations", [])])
            return out
        finally:
            shutil.rmtree(d, ignore_errors=True)


def violation_crash(v):
    """A violation of the fix stage as a `Crash` of its class."""
    at = f" at {v['left_line']}:{v['left_col']}" if v.get("left_line") else ""
    head = (v.get("message") or "").splitlines()
    detail = (f"{v['code']} at {v['line']}:{v['col']}, candidate `{v['title']}`, leaves {v['left']}{at}: "
              f"{head[0] if head else ''}")
    return Crash(fix_signature(v), FIX_COMMAND, detail)


def decode(data):
    """Bytes as a str that gives them back (`encode`): no newline is
    translated, and invalid UTF-8 stays as surrogates."""
    return data.decode("utf-8", "surrogateescape")


def encode(text):
    return text.encode("utf-8", "surrogateescape")


def read_input(path):
    return decode(Path(path).read_bytes())


def seeds(root):
    """The seed files: every `.onsa` under `tests/` except the saved inputs."""
    tests = Path(root) / "tests"
    fuzz = Path(root) / FUZZ_DIR
    out = []
    for p in sorted(tests.rglob("*.onsa")):
        if fuzz in p.parents:
            continue
        try:
            out.append((p.relative_to(root).as_posix(), read_input(p)))
        except OSError:
            continue
    return out


def mutate(rng, text, corpus, tokens, deep=False):
    """One mutant: 1 to 3 edits of `text`. With `deep`, an edit may nest
    thousands deep (S-183); without it, no edit nests deeper than 8."""
    s = text
    for _ in range(rng.randint(1, 3)):
        if not s:
            s = rng.choice(tokens)
        op = rng.random()
        p = rng.randrange(len(s) + 1)
        if op < 0.25:  # a token of the corpus
            s = s[:p] + rng.choice(tokens) + s[p:]
        elif op < 0.4:  # a special character or literal
            s = s[:p] + rng.choice(SPECIAL) + s[p:]
        elif op < 0.6:  # delete a range
            s = s[:p] + s[min(len(s), p + rng.randint(1, 20)):]
        elif op < 0.8:  # lines: duplicate, delete, or splice from another seed
            lines = s.split("\n")
            i = rng.randrange(len(lines))
            r = rng.random()
            if r < 0.4:
                lines.insert(i, lines[i])
            elif r < 0.7:
                del lines[i]
            else:
                other = rng.choice(corpus).split("\n")
                j = rng.randrange(len(other))
                lines[i:i + 1] = other[j:j + rng.randint(1, 5)]
            s = "\n".join(lines)
        elif op < 0.86 and deep:  # nest thousands deep (S-183)
            depth = rng.choice(DEPTHS)
            opening, closing = rng.choice(DEEP)
            q = min(len(s), p + rng.randint(0, 10))
            s = s[:p] + opening * depth + s[p:q] + closing * depth + s[q:]
        elif op < 0.9:  # a number literal made extreme
            nums = [m.span() for m in re.finditer(r"\d+(?:\.\d+)?", s)]
            if nums:
                a, b = rng.choice(nums)
                s = s[:a] + rng.choice(("0", "4294967296", "340282366920938463463374607431768211456", "1e999")) + s[b:]
        else:  # nest a range in brackets
            q = min(len(s), p + rng.randint(1, 30))
            n = rng.randint(1, 8)
            s = s[:p] + "(" * n + s[p:q] + ")" * n + s[q:]
    return s


def seeded_random(*parts):
    """A generator seeded with `parts` (str): the same parts give the same
    numbers on every machine (the mutants here, the perturbations of
    `tools/fmt_props.py`)."""
    digest = hashlib.sha256(encode("|".join(parts))).digest()
    return random.Random(int.from_bytes(digest[:8], "big"))


def mutants(seed_files, per_seed, version=VERSION, deep=False):
    """[(seed path, index, text)], the same for the same seeds."""
    corpus = [t for _, t in seed_files]
    tokens = sorted({t for text in corpus for t in TOKEN.findall(text)}) or ["x"]
    out = []
    for path, text in seed_files:
        rng = seeded_random(version, path, text)
        for k in range(per_seed):
            out.append((path, k, mutate(rng, text, corpus, tokens, deep)))
    return out


def minimize(runner, text, signature, commands=COMMANDS, budget=MINIMIZE_RUNS, seconds=MINIMIZE_SECONDS):
    """A smaller input with the same crash class: lines, then characters
    (ddmin), within `budget` runs and `seconds` (a hang takes `TIMEOUT` a run).
    `runner` is a `Runner`, or a `FixRunner` for a class of the fix stage."""
    if isinstance(runner, FixRunner):
        def same(candidate):
            try:
                return any(c.signature == signature for c in runner.violations([candidate], TIMEOUT)[0])
            except RuntimeError:
                return False
    else:
        def same(candidate):
            return any(c.signature == signature for c in runner.crashes(candidate, commands))
    return ddmin(text, same, budget, seconds)


def ddmin(text, still_fails, budget=MINIMIZE_RUNS, seconds=MINIMIZE_SECONDS):
    """A smaller input for which `still_fails(candidate)` holds: lines, then
    characters, within `budget` calls and `seconds` (also `tools/fmt_props.py`)."""
    runs = [0]
    deadline = time.monotonic() + seconds

    def same(candidate):
        if runs[0] >= budget or time.monotonic() > deadline:
            return False
        runs[0] += 1
        return still_fails(candidate)

    def reduce(parts, join):
        n = 2
        while len(parts) >= 2 and runs[0] < budget and time.monotonic() <= deadline:
            chunk = max(1, len(parts) // n)
            for i in range(0, len(parts), chunk):
                rest = parts[:i] + parts[i + chunk:]
                if rest and same(join(rest)):
                    parts = rest
                    n = max(n - 1, 2)
                    break
            else:
                if chunk == 1:
                    break
                n = min(len(parts), n * 2)
        return parts

    lines = reduce(text.split("\n"), "\n".join)
    chars = reduce(list("\n".join(lines)), "".join)
    return "".join(chars)


def short_name(text):
    return hashlib.sha256(encode(text)).hexdigest()[:8]


def entry_stub(target, crash):
    note = crash.signature.replace('"', "'")
    return (
        "[[pending]]\n"
        'kind = "fuzz-input"\n'
        f'target = "{target}"\n'
        'reasons = ["R-?"]  # the parent registers it\n'
        'until = "W?-?"\n'
        f'note = "{crash.command}: {note}"\n'
    )


def run(root, argv, fix_argv, per_seed, version, jobs, save, out=print, target_dir=None, time_budget=TIME_BUDGET,
        deep=False):
    """The gate item. `argv` runs the compiler, `fix_argv` the fix stage
    (`onsa_cases`). Returns the exit code."""
    root = Path(root)
    work = Path(target_dir or root / "target") / "fuzz"
    runner = Runner(argv, work / f"work-{os.getpid()}")  # one per process: two runs do not share it
    fixer = FixRunner(fix_argv, runner.work / "fix")
    failures = []
    start = time.time()
    deadline = time.monotonic() + time_budget

    # 1. Replay the saved inputs against the list.
    entries, errors = pending.load(root / repo.PENDING)
    failures += errors
    listed = {e.target for e in pending.of_kind(entries, "fuzz-input")}
    saved = sorted((root / FUZZ_DIR).glob("*.onsa")) if (root / FUZZ_DIR).is_dir() else []
    known = {}
    with ThreadPoolExecutor(jobs) as ex:
        replayed = list(ex.map(lambda p: runner.crashes(read_input(p)), saved))
    # The saved inputs go through the fix stage too (W3-17).
    try:
        broken = fixer.violations([read_input(p) for p in saved], max(1.0, deadline - time.monotonic()))
    except RuntimeError as e:
        failures.append(f"the fix stage cannot run on the saved inputs: {e}")
        broken = [[] for _ in saved]
    replayed = [crashes + fixes for crashes, fixes in zip(replayed, broken)]
    for p, crashes in zip(saved, replayed):
        rel = p.relative_to(root).as_posix()
        if rel in listed:
            if crashes:
                for c in crashes:
                    known.setdefault(c.signature, rel)
            else:
                failures.append(
                    f"{rel}: no longer crashes nor breaks the contract of a fix candidate; remove its entry from "
                    "tests/pending.toml (the file stays as a regression input)"
                )
        elif crashes:
            what = "breaks the contract of a fix candidate" if crashes[0].command == FIX_COMMAND else "crashes"
            failures.append(f"{rel}: {what} but is not listed in tests/pending.toml: {crashes[0].command}: "
                            f"{crashes[0].signature}")

    # 2. Fuzz.
    seed_files = seeds(root)
    inputs = mutants(seed_files, per_seed, version, deep)

    def one(m):
        # Past the budget, the mutant does not run (and the item fails).
        return None if time.monotonic() > deadline else runner.crashes(m[2])

    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(one, inputs))
    skipped = sum(1 for r in results if r is None)
    if skipped:
        failures.append(f"the time budget ({time_budget} s) ran out: {skipped} of {len(inputs)} mutants did not run")
    # 3. The fix stage, on one mutant in FIX_EVERY (W3-17).
    chosen = [i for i in range(len(inputs)) if i % FIX_EVERY == 0]
    fixes = {}
    fixer.unreadable = 0  # of the mutants only
    if time.monotonic() > deadline:
        failures.append(f"the time budget ({time_budget} s) ran out before the fix stage ({len(chosen)} mutants)")
    else:
        try:
            fixes = dict(zip(chosen, fixer.violations([inputs[i][2] for i in chosen], deadline - time.monotonic())))
        except RuntimeError as e:
            failures.append(f"the fix stage cannot run on the mutants: {e}")
    new = {}
    crashing = 0
    breaking = 0
    for i, ((seed, k, text), crashes) in enumerate(zip(inputs, results)):
        crashes = crashes or []
        if crashes:
            crashing += 1
        if fixes.get(i):
            breaking += 1
        for c in crashes + fixes.get(i, []):
            if c.signature not in known and c.signature not in new:
                new[c.signature] = (seed, k, text, c)
    written = []
    for signature, (seed, k, text, c) in new.items():
        commands = tuple(cmd for cmd in COMMANDS if " ".join(cmd) == c.command)
        seconds = max(0.0, min(MINIMIZE_SECONDS, deadline - time.monotonic()))
        who = fixer if c.command == FIX_COMMAND else runner
        small = minimize(who, text, signature, commands, seconds=seconds) if seconds > 0 else text
        name = f"{short_name(small)}.onsa"
        target = (FUZZ_DIR / name).as_posix()
        # A signal (a stack overflow) is never saved under tests/: replaying it would abort again.
        dest_dir = root / FUZZ_DIR if save and not signature.startswith("signal ") else work / "new"
        dest_dir.mkdir(parents=True, exist_ok=True)
        (dest_dir / name).write_bytes(encode(small))
        written.append((dest_dir / name, target, c, seed, k))
        if dest_dir != root / FUZZ_DIR:
            what = "a new class of a broken fix candidate" if c.command == FIX_COMMAND else "a new crash class"
            failures.append(f"{what}: {c.command}: {signature} (seed {seed}, mutant {k})")
    shutil.rmtree(runner.work, ignore_errors=True)

    out(
        f"fuzz: {len(inputs)} inputs from {len(seed_files)} seeds ({per_seed} each), {crashing} crashing, "
        f"{len(new)} new classes; {len(chosen)} mutants through the fix stage ({fixer.unreadable} not UTF-8), "
        f"{breaking} breaking a candidate's contract; {len(saved)} saved inputs replayed ({len(listed)} listed); "
        f"{time.time() - start:.1f} s"
    )
    for path, target, c, seed, k in written:
        shown = path.relative_to(root).as_posix() if root in path.parents else str(path)
        out(f"\n{shown}  ({c.command}; seed {seed}, mutant {k})\n{c.detail}\nentry to add:\n"
            f"{entry_stub(target, c)}")
    for f in failures:
        out(f"FAIL {f}")
    return 1 if failures else 0


def build(root, cases=False):
    """Build the compiler (or, with `cases`, the fix stage's `onsa_cases`)."""
    what = ["-p", "onsa_tests", "--bin", "onsa_cases"] if cases else ["-p", "onsa_cli"]
    r = subprocess.run(["cargo", "build", "-q", *what], cwd=root)
    return r.returncode == 0


def target_directory(root):
    """Cargo's target directory (`CARGO_TARGET_DIR`, the configuration), or None."""
    r = subprocess.run(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"], cwd=root, capture_output=True, text=True
    )
    if r.returncode != 0:
        return None
    try:
        return Path(json.loads(r.stdout)["target_directory"])
    except (ValueError, KeyError):
        return None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--per-seed", type=int, default=PER_SEED)
    ap.add_argument("--version", default=VERSION)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--binary", type=Path, help="the compiler (default: build <target directory>/debug/onsa)")
    ap.add_argument("--cases-binary", type=Path,
                    help="the fix stage's onsa_cases (default: build <target directory>/debug/onsa_cases)")
    ap.add_argument("--time-budget", type=float, default=TIME_BUDGET, help="seconds for the whole run")
    ap.add_argument("--deep", action="store_true", help="also nest thousands deep (S-183, W3-14; not in the gate)")
    ap.add_argument("--save", action="store_true", help="write the new minimized inputs into tests/fuzz/")
    args = ap.parse_args(argv)
    if args.per_seed < 0 or args.jobs < 1 or args.time_budget <= 0:
        ap.error("--per-seed must be 0 or more, --jobs 1 or more and --time-budget more than 0")
    target = target_directory(args.root)
    if target is None:
        print("fuzz: cannot read cargo's target directory (cargo metadata)", file=sys.stderr)
        return 2
    binary = args.binary
    if binary is None:
        if not build(args.root):
            print("fuzz: cannot build the compiler (cargo build -p onsa_cli)", file=sys.stderr)
            return 2
        binary = target / "debug" / "onsa"
    cases = args.cases_binary
    if cases is None:
        if not build(args.root, cases=True):
            print("fuzz: cannot build onsa_cases (cargo build -p onsa_tests --bin onsa_cases)", file=sys.stderr)
            return 2
        cases = target / "debug" / "onsa_cases"
    return run(
        args.root, [str(binary)], [str(cases)], args.per_seed, args.version, args.jobs, args.save,
        target_dir=target, time_budget=args.time_budget, deep=args.deep,
    )


if __name__ == "__main__":
    sys.exit(main())
