#!/usr/bin/env python3
"""The short fuzzing of `onsa check` and `onsa fmt` (Q-06, D-16 6, W1-04).

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
   or changing a seed may change the mutants of the others. Each seed also
   gives `--truncations` inputs cut short at the end of the file (FZ-1):
   the seed up to the end of a token outside a line comment, most often
   right after a symbol (`CUT_AFTER`: the opening brackets, the operators,
   the marks `@ ~ ' ^ # ? !`, the backslash of an escape; the rarer the
   symbol in the corpus, the more often), without the blanks and the
   newline before the cut, from a generator of their own (they change no
   mutant). A truncation is looked at for a crash only: it does not go
   through the fix stage (3.), since a file cut short often holds two
   errors or more, which the spec puts outside the contract (S-384, S-413).
   A crash of a class (`signature`) that a listed input also shows is known.
   A crash of a new class fails the gate: its first input is minimized and
   written to `target/fuzz/new/`, with the entry to add (the gate writes
   nothing under `tests/`; `--save` copies the inputs into `tests/fuzz/`).
   Those of a worktree, `tools/work.py patch` copies into the main tree's;
   the summary of the main tree's gate lists those `tests/fuzz/` has no file
   of the same name for (`fuzz new: …`): the ones not sorted yet, which
   `fuzz.py sort` sorts (below).
3. **Fix candidates** (S-236, W3-17). One mutant in `FIX_EVERY` (a fixed
   rule: the mutants whose index in the whole run is a multiple of it; never
   a truncation), and every
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

**The classes the spec puts outside the contract** (R-207): `tests/fuzz/allowed.toml`
lists, as `[[allowed]]` entries, classes of the fix stage that the spec
decided are no broken candidate, with an input that shows each: a fix that
the spec makes in two steps (S-386: the `,`, then the `|` before the first
alternative, S-383), and an input with two errors (S-384, S-413), which the
mutants cut short at the end of a file often are. Every field is required:
`class` (`fix|<code>|<title>|<code left>`; a crash or a signal is never
listed), `input` (a saved input `tests/fuzz/<name>.onsa`, not listed in
`tests/pending.toml`; one entry each), `left` (the message of the
diagnostic left after the candidate, as the class writes the title: quoted
text `…`, numbers `#`), `reasons` (S numbers of `decisions/S/`, or R numbers of
`issues/R/` for a low harm recorded there) and `note`. A mutant is known
when it shows the class with that message (the class alone is too coarse a
net); the input must show them on every run (when it no longer does, the
entry goes), and nothing else. The net gets
coarser for such a class: the contract on the cases (`onsa_tests::fix_contract`)
is what holds it.

**Narrowed runs** (X-1): the options of `tools/narrowing.py` (`--changed-since`,
`--sample`, `--salt`, `--code-cap`, `--shard`) pick the seeds to mutate, truncate and
sweep. The corpus, the tokens and the weights of the cuts still come from every seed,
and the fix stage takes a mutant by its index in the whole run (`plan`): a narrowed
run feeds the compiler a part of the whole run's inputs. The replay is always whole.
In a narrowed run (`--changed-since`, `--sample`), a new class of the fix stage that
the base binaries (`--base`, default `auto`: `narrowing.resolve_base`) show on the
same minimized input, with the same message left, does not fail: it is listed on a
line `pre-existing (the base <commit> shows it): ...`. A whole run and a shard fail
on it and mark it. A crash, an internal error and a timeout fail even when they are
from before (the base does not run them); so does every new class when the base is
unknown. A whole run or a shard of the tree at the merge base with no change of the code
(a sweep, a whole run of the main tree) compares with the code before HEAD (X-1 U6), shown
as `<commit> (the code before HEAD)`: what the base shows was there before HEAD's code. A
narrowed run there compares with the merge base's own (X-1 U6b): with no code in the work,
every class of the fix stage is from before it.

Inputs are bytes: the seeds and the saved inputs are read and written as
they are (a `\r` stays, invalid UTF-8 too).

    tools/fuzz.py [run] [--per-seed N] [--truncations N] [--version V] [--jobs N]
                  [--binary PATH] [--cases-binary PATH] [--time-budget S]
                  [--deep] [--save] [--changed-since REV|auto] [--code-cap N]
                  [--sample F --salt ID] [--shard I/K] [--base auto|none|DIR]
    tools/fuzz.py sort [--go] [--jobs N] [--binary PATH] [--cases-binary PATH]
    tools/fuzz.py help [--role R] [COMMAND]

The commands are `run` and `sort` (COMMANDS, rules/tools.md 9.1); `fuzz.py help`
shows their purposes, times, roles and examples (`--help` lists them). A call
with no command (no argument, or a first argument `-…` but `-h` and `--help`:
the gate's `fuzz` and `fuzz-deep`) is `run`, the gate item described above.

**`sort`** (X9-23) runs each input of `target/fuzz/new/` through both commands
and the fix stage with the binaries of the tree, and sorts it with the
replay's known classes (`Replay.knows`, as the run does): an input `tests/fuzz/`
has a file of the same name for, and one whose classes are all known, goes; one
that shows nothing goes into `tests/fuzz/` as a regression input (not listed);
one with an unknown crash, internal error or signal stays (it is fixed; never
allowed, rules/leader.md 4.5), and one with unknown classes of the fix stage
only stays, for the parent to decide. The entries to add go with what stays
(`entry_stub`, and `allowed_stub` for a class of the fix stage, as the run
prints them). It prints the table and moves nothing unless `--go`; its last
line counts each kind.

`--deep` adds mutants that nest brackets or blocks thousands deep: the
nesting limit (spec §2.5, S-183, W3-14) must stop them with E0006 before
the stack runs out. The gate runs them only at a stage end (the item
`fuzz-deep`, W3-03): they are heavy on the machine. (W3-14 ran them once: no
signal; `fmt --check` timed out on the 20002 lexer diagnostics of a string
nesting `{ ` 20000 deep, one per unit since W3-03, S-214;
`tests/fuzz/8858ce8c.onsa`.) A signal is not saved under `tests/` (with `--save`
it goes to `target/fuzz/new/`): a stack overflow aborts the process, and
the system writes a crash report for each one. A deep run also sweeps
(FZ-1): it cuts each seed right after every place of each rare symbol
(`RARE`), outside a line comment and not at its end, as the truncations do,
and looks at each cut for a crash only (the fix stage is not run). The
weighted truncations repeat the gate's: a deep run leaves them out unless
`--truncations` asks.

The compiler is `<target directory>/debug/onsa`, the target directory of
`cargo metadata` (which follows `CARGO_TARGET_DIR` and the cargo
configuration), unless `--binary` names it; the fix stage runs
`<target directory>/debug/onsa_cases` (`--cases-binary`). `--time-budget` bounds the
whole run: when it is spent, the remaining mutants and truncations do not
run and the item fails (it never passes on fewer inputs than it says).

Exit 0 when nothing new crashes and the replay agrees with the list, 1
otherwise, 2 on a usage error (or when the compiler cannot be built).
"""
import argparse
import collections
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
import tomllib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import narrowing  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
FUZZ_DIR = repo.FUZZ_DIR
# The work directory under cargo's target directory, and its directory of the inputs of the new classes.
WORK, NEW = "fuzz", "new"
# The commands of Q-06; `fmt --check` reads and does not write.
ONSA_COMMANDS = (("check",), ("fmt", "--check"))
TIMEOUT = 20  # seconds per run
# The start of the class of a run ended by a signal: never saved under tests/ (a stack overflow aborts again).
SIGNAL = "signal "
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
# The classes of the fix stage that the spec puts outside the contract (R-207).
ALLOWED = FUZZ_DIR / "allowed.toml"
ALLOWED_FIELDS = ("class", "left", "input", "reasons", "note")
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
# The truncations (FZ-1): per seed, and the symbols most cuts come right after
# (`_` only as a token of its own, not inside a name), in CUT_AFTER_SHARE of the cuts.
TRUNCATIONS = 2
CUT_AFTER = re.compile(r"""[@~:,'{(\[<>.?!#^\-+*/%&|=;"\\]|(?<![A-Za-z0-9_])_(?![A-Za-z0-9_])""")
CUT_AFTER_SHARE = 0.75
# The rare symbols of CUT_AFTER (FZ-1): 1,200 places or fewer each in the corpus (counted 2026-10-13).
# A deep run cuts right after every place of each (`sweep`). A fixed set, not counted on each run: what
# the sweep covers shows here and does not move with the corpus.
RARE = "~!?'^@#/\\%"
TRAILING_BLANKS = " \t\r\n"
# A string literal (its `//` starts no comment) or a line comment (spec §2.1), whose words are no token.
COMMENT = re.compile(r'"(?:[^"\\\n]|\\.)*"?|//[^\n]*')


@dataclass(frozen=True)
class Crash:
    signature: str  # the class: the same bug gives the same signature
    command: str
    detail: str  # what the command printed, shortened
    # For a class of the fix stage, the message of the diagnostic left after
    # the candidate, as the title is in the class (`normalized`): what an entry
    # of `tests/fuzz/allowed.toml` names besides the class (R-207).
    left: str = ""


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
        return Crash(f"{SIGNAL}{-returncode}|{name}|{last}", name, "\n".join(lines[-3:]))
    return Crash(f"exit {returncode}|{message_head(raw or '')}", name, "\n".join(lines[:4]))


class Runner:
    """Runs the compiler on inputs, each in a directory of its own."""

    def __init__(self, argv, work):
        self.argv = list(argv)
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)

    def crashes(self, text, commands=ONSA_COMMANDS):
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


def normalized(text):
    """A title or a message as a class names it: its quoted text `…`, its
    numbers `#`, its blanks one space, the first 80 characters."""
    text = re.sub(r"`[^`]*`", "`…`", text)
    return re.sub(r"\d+", "#", re.sub(r"\s+", " ", text)).strip()[:80]


def fix_signature(v):
    """The class of a violation of the near "same place" (S-236): the code,
    the title of the candidate (`normalized`) and the code left after it."""
    return f"fix|{v['code']}|{normalized(v['title'])}|{v['left']}"


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
    return Crash(fix_signature(v), FIX_COMMAND, detail, normalized(head[0]) if head else "")


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


def cut_sites(text):
    """The places to cut `text` (FZ-1), outside a line comment and not at its
    end: ({symbol: the places right after it (`CUT_AFTER`)}, the ends of the
    tokens (`TOKEN`))."""
    inside = bytearray(len(text) + 1)
    for m in COMMENT.finditer(text):
        if m.group().startswith("//"):
            inside[m.start() + 1:m.end() + 1] = b"\x01" * (m.end() - m.start())
    after = {}
    for m in CUT_AFTER.finditer(text):
        if not inside[m.end()]:
            after.setdefault(m.group(), []).append(m.end())
    return after, [m.end() for m in TOKEN.finditer(text) if not inside[m.end()]]


def truncate(rng, text, sites, counts):
    """One truncation of `text` at one of its `sites` (`cut_sites`), the blanks
    and newlines before the cut dropped: the file ends there. In
    `CUT_AFTER_SHARE` of the cuts it is right after a symbol, each symbol of
    the seed weighted by its rarity in the corpus (`counts`): a form the
    corpus seldom shows (a new one, `x@`) is cut as often as `(` (FZ-1)."""
    after, ends = sites
    if after and (not ends or rng.random() < CUT_AFTER_SHARE):
        symbols = sorted(after)
        pool = after[rng.choices(symbols, [1 / counts[c] for c in symbols])[0]]
    else:
        pool = ends
    return cut_at(text, rng.choice(pool) if pool else len(text))


def cut_at(text, place):
    """`text` cut at `place`, the blanks and newlines before the cut dropped: the file ends there."""
    return text[:place].rstrip(TRAILING_BLANKS)


def sweep(seed_files, only=None):
    """[(seed path, label, text)]: each seed cut right after every place of each symbol of `RARE`
    (`cut_sites`, `cut_at`), one input for each text, in the order of the seeds and the places. No
    generator: the same seeds give the same inputs whatever the version (FZ-1, `--deep`). `only`:
    the seeds to cut (all when None)."""
    out = {}
    for path, text in seed_files:
        if only is not None and path not in only:
            continue
        after, _ = cut_sites(text)
        for place, symbol in sorted((p, c) for c in RARE for p in after.get(c, ())):
            at = place - 1  # the symbol
            line, col = text.count("\n", 0, at) + 1, at - text.rfind("\n", 0, at)
            cut = cut_at(text, place)
            out.setdefault(cut, (path, f"sweep `{symbol}` at {line}:{col}", cut))
    return list(out.values())


def truncations(seed_files, per_seed, version=VERSION, only=None):
    """[(seed path, index, text)]: `per_seed` truncations of each seed (of
    `only`, when not None), the same for the same seeds. Their generator is
    not the mutants' (the truncations change no mutant); the weights of the
    symbols come from the whole corpus, as the tokens of the mutants do."""
    sites = [cut_sites(text) for _, text in seed_files]
    counts = collections.Counter()
    for after, _ in sites:
        counts.update({c: len(places) for c, places in after.items()})
    out = []
    for (path, text), site in zip(seed_files, sites):
        if only is not None and path not in only:
            continue
        rng = seeded_random(version, "truncation", path, text)
        out += [(path, k, truncate(rng, text, site, counts)) for k in range(per_seed)]
    return out


def seeded_random(*parts):
    """A generator seeded with `parts` (str): the same parts give the same
    numbers on every machine (the mutants here, the perturbations of
    `tools/fmt_props.py`)."""
    digest = hashlib.sha256(encode("|".join(parts))).digest()
    return random.Random(int.from_bytes(digest[:8], "big"))


def mutants(seed_files, per_seed, version=VERSION, deep=False, only=None):
    """[(seed path, index, text)], the same for the same seeds. With `only`,
    the mutants of those seeds alone: the corpus and its tokens still come
    from every seed, so they are the whole run's mutants of those seeds (X-1)."""
    corpus = [t for _, t in seed_files]
    tokens = sorted({t for text in corpus for t in TOKEN.findall(text)}) or ["x"]
    out = []
    for path, text in seed_files:
        if only is not None and path not in only:
            continue
        rng = seeded_random(version, path, text)
        for k in range(per_seed):
            out.append((path, k, mutate(rng, text, corpus, tokens, deep)))
    return out


def plan(seed_files, per_seed, version=VERSION, deep=False, truncated=TRUNCATIONS, swept=False, only=None):
    """What a run feeds the compiler: (mutants, truncations, swept cuts, the indices in the
    mutants of the ones that go through the fix stage). With `only`, the part of the whole run's
    that comes from those seeds: the fix stage takes a mutant by its index in the whole run, the
    seed's place times `per_seed` plus the mutant's own index (X-1)."""
    inputs = mutants(seed_files, per_seed, version, deep, only)
    cuts = truncations(seed_files, truncated, version, only)
    swept_cuts = sweep(seed_files, only) if swept else []
    place = {path: i for i, (path, _) in enumerate(seed_files)}
    chosen = [i for i, (path, k, _) in enumerate(inputs) if (place[path] * per_seed + k) % FIX_EVERY == 0]
    return inputs, cuts, swept_cuts, chosen


def base_shows(base, crash, text, seconds, work):
    """(whether the base's fix stage shows the class of `crash` on `text`, with the same message
    left; why it cannot tell, or None). A class of the fix stage only (X-1, M-3)."""
    if seconds <= 0:
        return False, "no time left"
    try:
        found = FixRunner(base.onsa_cases, work).violations([text], min(TIMEOUT, seconds))[0]
    except RuntimeError as e:
        return False, str(e)
    return any(v.signature == crash.signature and v.left == crash.left for v in found), None


def minimize(runner, text, signature, commands=ONSA_COMMANDS, budget=MINIMIZE_RUNS, seconds=MINIMIZE_SECONDS, left=None):
    """A smaller input with the same crash class: lines, then characters
    (ddmin), within `budget` runs and `seconds` (a hang takes `TIMEOUT` a run).
    `runner` is a `Runner`, or a `FixRunner` for a class of the fix stage,
    whose message left (`left`, R-207) stays too."""
    if isinstance(runner, FixRunner):
        def same(candidate):
            try:
                return any(c.signature == signature and (left is None or c.left == left)
                           for c in runner.violations([candidate], TIMEOUT)[0])
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


def load_allowed(root, listed):
    """The entries of `tests/fuzz/allowed.toml` ({(class, left): input}) and
    the errors of the file (R-207). `listed`: the inputs of `tests/pending.toml`."""
    root = Path(root)
    path = root / ALLOWED
    if not path.exists():
        return {}, []
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        return {}, [f"{ALLOWED.as_posix()}: {e}"]
    errors = [f"{ALLOWED.as_posix()}: unknown top-level key `{k}` (only [[allowed]])" for k in data if k != "allowed"]
    raw = data.get("allowed", [])
    if not isinstance(raw, list):
        return {}, errors + [f"{ALLOWED.as_posix()}: `allowed` must be an array of tables ([[allowed]])"]
    try:
        docs = pending.load_docs(root)
        numbers, numbers_at = docs.reasons, docs.reasons_at
    except pending.DocsError as e:
        numbers, numbers_at = None, None
        errors.append(f"{ALLOWED.as_posix()}: the S / R numbers cannot be read: {e}")
    out = {}
    inputs = set()
    for i, item in enumerate(raw):
        where = f"{ALLOWED.as_posix()}: allowed[{i}]"
        if not isinstance(item, dict):
            errors.append(f"{where}: not a table")
            continue
        problems = [f"unknown field `{k}`" for k in item if k not in ALLOWED_FIELDS]
        problems += [f"missing field `{k}`" for k in ALLOWED_FIELDS if k not in item]
        if not problems:
            cls, left, inp, reasons, note = (item[k] for k in ALLOWED_FIELDS)
            if not isinstance(cls, str) or not cls.startswith("fix|"):
                problems.append("`class` must be a class of the fix stage (`fix|<code>|<title>|<code left>`); "
                                "a crash is never allowed")
            if not isinstance(left, str) or not left.strip() or normalized(left) != left:
                problems.append("`left` must be the message of the diagnostic left, as the fuzzing writes it "
                                "(quoted text `…`, numbers `#`)")
            elif isinstance(cls, str) and (cls, left) in out:
                problems.append(f"the class `{cls}` with `{left}` is listed twice")
            fuzz_dir = FUZZ_DIR.as_posix() + "/"
            if (not isinstance(inp, str) or pending.path_problem(inp) or not inp.startswith(fuzz_dir)
                    or "/" in inp[len(fuzz_dir):] or not inp.endswith(".onsa")):
                problems.append("`input` must be a saved input `tests/fuzz/<name>.onsa`")
            elif not (root / inp).is_file():
                problems.append(f"the input `{inp}` does not exist")
            elif inp in listed:
                problems.append(f"the input `{inp}` is listed in tests/pending.toml too")
            elif inp in inputs:
                problems.append(f"the input `{inp}` is the input of another entry")
            if (not isinstance(reasons, list) or not reasons
                    or not all(isinstance(r, str) and pending.REASON.fullmatch(r) for r in reasons)):
                problems.append("`reasons` must be an array of one or more S / R numbers (`S-386`, `R-219`)")
            elif len(set(reasons)) != len(reasons):
                problems.append("a reason is listed twice")
            elif numbers is not None:
                problems += [f"the reason `{r}` is not in {numbers_at}" for r in reasons if r not in numbers]
            if not isinstance(note, str) or not note.strip():
                problems.append("`note` must be a non-empty string")
        if problems:
            errors += [f"{where}: {p}" for p in problems]
            continue
        out[(cls, left)] = inp
        inputs.add(inp)
    return out, errors


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


def allowed_stub(target, crash):
    """The entry of `tests/fuzz/allowed.toml` for a class of the fix stage (X9-24): the class and the message
    left as `load_allowed` reads them; the parent writes the reasons and the note (rules/leader.md 4.5)."""
    q = spec_blocks.toml_string
    return (f"[[allowed]]\nclass = {q(crash.signature)}\nleft = {q(crash.left)}\ninput = {q(target)}\n"
            'reasons = ["S-?"]  # the parent writes the S / R numbers\n'
            'note = "?"  # the parent writes it\n')


def stubs(target, crash):
    """The entries to add for a new class: `entry_stub`, and `allowed_stub` too for a class of the fix stage."""
    text = f"entry to add:\n{entry_stub(target, crash)}"
    if crash.command == FIX_COMMAND:
        text += (f"or, when the spec puts the class outside the contract, the entry of {ALLOWED.as_posix()}:\n"
                 f"{allowed_stub(target, crash)}")
    return text


@dataclass
class Replay:
    """The saved inputs replayed against the lists (the run's 1.): what makes a class known."""

    saved: list  # the paths of tests/fuzz/*.onsa
    listed: set  # the inputs of tests/pending.toml (kind fuzz-input)
    allowed: dict  # {(class, left): input} of tests/fuzz/allowed.toml
    known: dict  # {class: a listed input that shows it}
    errors: list  # the lists cannot be read, or the fix stage cannot run: the classes known are not all
    failures: list  # a saved input disagrees with the lists

    def knows(self, c):
        """Whether the class of `c` is known: a listed input shows it, or the allowed list has it with its
        message left (R-207)."""
        return (c.signature, c.left) in self.allowed or c.signature in self.known


def examine(runner, fixer, texts, jobs, seconds):
    """(for each text, the crashes of both commands and the violations of the fix stage; why the fix stage
    cannot run, or None: then the crashes alone)."""
    with ThreadPoolExecutor(jobs) as ex:
        crashes = list(ex.map(runner.crashes, texts))
    try:
        return [c + f for c, f in zip(crashes, fixer.violations(texts, seconds))], None
    except RuntimeError as e:
        return crashes, str(e)


def replay_saved(root, runner, fixer, jobs, deadline):
    """The `Replay` of the saved inputs (the fix stage too, W3-17), within the `deadline` (monotonic)."""
    entries, errors = pending.load(root / repo.PENDING)
    listed = {e.target for e in pending.of_kind(entries, "fuzz-input")}
    allowed, more = load_allowed(root, listed)
    errors += more
    allowed_inputs = {inp: key for key, inp in allowed.items()}
    saved = sorted((root / FUZZ_DIR).glob("*.onsa")) if (root / FUZZ_DIR).is_dir() else []
    replayed, why = examine(runner, fixer, [read_input(p) for p in saved], jobs, max(1.0, deadline - time.monotonic()))
    if why:
        errors.append(f"the fix stage cannot run on the saved inputs: {why}")
    known, failures = {}, []
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
        elif rel in allowed_inputs:
            # A class the spec puts outside the contract (R-207): its input shows it with the
            # message left, and nothing else.
            key = allowed_inputs[rel]
            shown = {(c.signature, c.left) for c in crashes}
            if key not in shown:
                failures.append(f"{rel}: the class `{key[0]}` with `{key[1]}` no longer shows; remove its entry "
                                f"from {ALLOWED.as_posix()} (the file stays as a regression input)")
            for other, left in sorted(shown - {key}):
                failures.append(f"{rel}: shows `{other}` with `{left}`, which is not the entry's in "
                                f"{ALLOWED.as_posix()}")
        elif crashes:
            what = "breaks the contract of a fix candidate" if crashes[0].command == FIX_COMMAND else "crashes"
            failures.append(f"{rel}: {what} but is not listed in tests/pending.toml: {crashes[0].command}: "
                            f"{crashes[0].signature}")
    return Replay(saved, listed, allowed, known, errors, failures)


def run(root, argv, fix_argv, per_seed, version, jobs, save, out=print, target_dir=None, time_budget=TIME_BUDGET,
        deep=False, truncated=TRUNCATIONS, swept=False, selection=None, base=None):
    """The gate item. `argv` runs the compiler, `fix_argv` the fix stage
    (`onsa_cases`); `truncated` truncations of each seed, and with `swept`
    the cuts after every rare symbol (`sweep`). `selection`
    (`narrowing.Selection`, None for the whole run) picks the seeds to
    mutate; `base` (`narrowing.Base`, the reason it is unknown, or None)
    tells a new class of the fix stage from one before. Returns the exit code."""
    root = Path(root)
    work = Path(target_dir or root / "target") / WORK
    runner = Runner(argv, work / f"work-{os.getpid()}")  # one per process: two runs do not share it
    fixer = FixRunner(fix_argv, runner.work / "fix")
    failures = []
    start = time.time()
    deadline = time.monotonic() + time_budget

    # 1. Replay the saved inputs against the list.
    replay = replay_saved(root, runner, fixer, jobs, deadline)
    failures += replay.errors + replay.failures
    saved, listed, allowed = replay.saved, replay.listed, replay.allowed

    # 2. Fuzz: the seeds, the corpus and the weights are the whole run's; only the seeds to mutate narrow.
    seed_files = seeds(root)
    try:
        picked = narrowing.pick(seed_files, selection, root) if selection else None
    except narrowing.NarrowError as e:
        out(f"fuzz: cannot narrow the seeds: {e}")
        return 2
    inputs, cuts, swept_cuts, chosen = plan(seed_files, per_seed, version, deep, truncated, swept,
                                            picked.paths if picked else None)
    if swept and not swept_cuts:
        failures.append(f"the sweep found no place after a rare symbol ({RARE}) in {len(seed_files)} seeds")
    # The mutants first: their indices are the fix stage's (3.). The cuts are looked at for a crash only.
    runs = ([(seed, f"mutant {k}", text) for seed, k, text in inputs]
            + [(seed, f"truncation {k}", text) for seed, k, text in cuts] + swept_cuts)

    def one(m):
        # Past the budget, the input does not run (and the item fails).
        return None if time.monotonic() > deadline else runner.crashes(m[2])

    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(one, runs))
    skipped = sum(1 for r in results if r is None)
    if skipped:
        failures.append(f"the time budget ({time_budget} s) ran out: {skipped} of {len(runs)} inputs "
                        f"({len(inputs)} mutants, {len(cuts)} truncations, {len(swept_cuts)} swept) did not run")
    # 3. The fix stage, on one mutant in FIX_EVERY of the whole run (W3-17, `plan`).
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
    cut_crashing = 0
    swept_crashing = 0
    for i, ((seed, which, text), crashes) in enumerate(zip(runs, results)):
        crashes = crashes or []
        if crashes:
            crashing += 1
            cut_crashing += len(inputs) <= i < len(inputs) + len(cuts)
            swept_crashing += i >= len(inputs) + len(cuts)
        if fixes.get(i):
            breaking += 1
        for c in crashes + fixes.get(i, []):
            if not replay.knows(c) and c.signature not in new:
                new[c.signature] = (seed, which, text, c)
    written = []
    before = []  # the lines of the classes the base shows too, in a narrowed run
    narrowed = bool(selection and selection.narrowed)
    for signature, (seed, which, text, c) in new.items():
        commands = tuple(cmd for cmd in ONSA_COMMANDS if " ".join(cmd) == c.command)
        seconds = max(0.0, min(MINIMIZE_SECONDS, deadline - time.monotonic()))
        who = fixer if c.command == FIX_COMMAND else runner
        small = minimize(who, text, signature, commands, seconds=seconds, left=c.left or None) if seconds > 0 else text
        name = f"{short_name(small)}.onsa"
        target = (FUZZ_DIR / name).as_posix()
        # A signal (a stack overflow) is never saved under tests/: replaying it would abort again.
        dest_dir = root / FUZZ_DIR if save and not signature.startswith(SIGNAL) else work / NEW
        dest_dir.mkdir(parents=True, exist_ok=True)
        (dest_dir / name).write_bytes(encode(small))
        written.append((dest_dir / name, target, c, seed, which))
        if dest_dir != root / FUZZ_DIR:
            what = "a new class of a broken fix candidate" if c.command == FIX_COMMAND else "a new crash class"
            line = f"{what}: {c.command}: {signature} (seed {seed}, {which})"
            # A crash fails even when it is from before (GF-3): the base does not run it.
            shown, why = False, None
            if isinstance(base, narrowing.Base) and c.command == FIX_COMMAND:
                shown, why = base_shows(base, c, small, deadline - time.monotonic(), runner.work / "base")
            if shown and narrowed:
                before.append(f"pre-existing (the base {base.shown} shows it): {c.command}: {signature} "
                              f"(seed {seed}, {which})")
            elif shown:
                failures.append(f"{line} (pre-existing: the base {base.shown} shows it)")
            else:
                failures.append(line + (f" (the base cannot tell: {why})" if why else ""))
    shutil.rmtree(runner.work, ignore_errors=True)

    if isinstance(base, narrowing.Base):
        base_part = f"; base {base.shown}: {len(before)} pre-existing"
    else:
        base_part = f"; base unknown ({base})" if base else ""
    out(
        f"fuzz: {len(inputs)} mutants from "
        f"{picked.describe(len(seed_files)) if picked else f'{len(seed_files)} seeds'} ({per_seed} each) "
        f"and {len(cuts)} truncations "
        f"({truncated} each, {cut_crashing} crashing), "
        + (f"{len(swept_cuts)} cuts swept after `{RARE}` ({swept_crashing} crashing), " if swept else "")
        + f"{crashing} crashing in all, "
        f"{len(new)} new classes; {len(chosen)} mutants through the fix stage ({fixer.unreadable} not UTF-8), "
        f"{breaking} breaking a candidate's contract; {len(saved)} saved inputs replayed ({len(listed)} listed, {len(allowed)} allowed)"
        f"{base_part}; {time.time() - start:.1f} s"
    )
    for path, target, c, seed, which in written:
        shown = path.relative_to(root).as_posix() if root in path.parents else str(path)
        out(f"\n{shown}  ({c.command}; seed {seed}, {which})\n{c.detail}\n{stubs(target, c)}")
    for line in before:
        out(line)
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


def new_inputs(root):
    """The directory a run in `root` keeps the inputs of the new classes in (`run`), as `main` finds it."""
    return Path(target_directory(root) or Path(root) / "target") / WORK / NEW


def unsorted_line(root):
    """The line of the main tree's gate summary (X-1 U9): the inputs in `new_inputs` that `tests/fuzz/`
    has no file of the same name for (`--save` keeps the name), for the parent to sort."""
    new = new_inputs(root)
    try:
        names = sorted(n for n in os.listdir(new) if n.endswith(".onsa") and not (Path(root) / FUZZ_DIR / n).exists())
    except FileNotFoundError:
        names = []
    except OSError as e:
        return f"fuzz new: cannot read {new}/ ({e})"
    if not names:
        return f"fuzz new: none outside {FUZZ_DIR}/"
    return f"fuzz new: {len(names)} not under {FUZZ_DIR}/ (sort them: tools/fuzz.py sort, rules/leader.md 4.5): " + ", ".join(names)


# The kinds of `sort` in the order of its table, and what it does with each (X9-23).
SORTED = {
    "same name": "remove: tests/fuzz/ has a file of the same name",
    "fixed": "place in tests/fuzz/: a regression input (not listed)",
    "known": "remove: a listed input or an allowed entry shows its classes",
    "crash": "keep: an internal error or a crash is fixed, never allowed (rules/leader.md 4.5)",
    "new": "keep: a new class of the fix stage, for the parent to decide (rules/leader.md 4.5)",
}
GONE = ("same name", "fixed", "known")


def sort_inputs(root, runner, fixer, jobs, new_dir, go, out=print):
    """`sort` (X9-23): each input of `new_dir` (`new_inputs`) by `SORTED`, with the known classes of the run
    (`replay_saved`, `Replay.knows`); with `go`, places and removes them. Moves nothing when the lists cannot be
    read or the fix stage cannot run (exit 1)."""
    root, new_dir = Path(root), Path(new_dir)
    names = sorted(p.name for p in new_dir.glob("*.onsa")) if new_dir.is_dir() else []
    rows = [(n, "same name", []) for n in names if (root / FUZZ_DIR / n).exists()]
    rest = [n for n in names if not (root / FUZZ_DIR / n).exists()]
    errors = []
    if rest:  # the inputs to run: the replay gives the known classes
        replay = replay_saved(root, runner, fixer, jobs, time.monotonic() + TIME_BUDGET)
        found, why = examine(runner, fixer, [read_input(new_dir / n) for n in rest], jobs, TIME_BUDGET)
        errors = replay.errors + ([f"the fix stage cannot run on the new inputs: {why}"] if why else [])
        for f in replay.failures:
            out(f"replay: {f}")
        for n, classes in zip(rest, found):
            unknown = [c for c in classes if not replay.knows(c)]
            kind = ("fixed" if not classes else "known" if not unknown
                    else "crash" if any(c.command != FIX_COMMAND for c in unknown) else "new")
            rows.append((n, kind, classes if kind == "known" else unknown))
    rows.sort(key=lambda r: (list(SORTED).index(r[1]), r[0]))
    for n, kind, classes in rows:
        out(f"{kind:<9}  {n}  {SORTED[kind]}" + "".join(f"\n           {c.command}: {c.signature}" for c in classes))
    for n, kind, classes in rows:
        if kind in GONE:
            continue
        c = next((c for c in classes if c.command != FIX_COMMAND), classes[0])
        stub = ("a signal is never saved under tests/: the input stays until it is fixed\n"
                if c.signature.startswith(SIGNAL) else stubs((FUZZ_DIR / n).as_posix(), c))
        out(f"\n{n}  ({c.command})\n{c.detail}\n{stub}")
    for e in errors:
        out(f"FAIL {e}")
    moved = go and not errors
    if moved:
        for n, kind, _ in rows:
            if kind == "fixed":
                (root / FUZZ_DIR).mkdir(parents=True, exist_ok=True)
                shutil.copyfile(new_dir / n, root / FUZZ_DIR / n)
            if kind in GONE:
                (new_dir / n).unlink()
    counts = collections.Counter(kind for _, kind, _ in rows)
    out(f"sort: {len(rows)} inputs in {new_dir}: " + ", ".join(f"{counts[k]} {k}" for k in SORTED) + "; "
        + ("placed and removed" if moved else "nothing moved" + ("" if errors else " (--go places and removes them)")))
    return 1 if errors else 0


def run_args(p):
    p.add_argument("--per-seed", type=int, default=PER_SEED)
    p.add_argument("--truncations", type=int,
                   help=f"truncations of each seed (default {TRUNCATIONS}; 0 with --deep, which would repeat them)")
    p.add_argument("--version", default=VERSION)
    p.add_argument("--time-budget", type=float, default=TIME_BUDGET, help="seconds for the whole run")
    p.add_argument("--deep", action="store_true",
                   help="also nest thousands deep (S-183, W3-14) and sweep the rare symbols (FZ-1); "
                        "the gate item fuzz-deep, at a stage end only")
    p.add_argument("--save", action="store_true", help="write the new minimized inputs into tests/fuzz/")
    narrowing.add_arguments(p, base=True)


def run_command(args):
    ap = args.parser_
    try:
        selection = narrowing.selection(ap, args, args.root)
    except narrowing.NarrowError as e:
        ap.exit(2, f"{ap.prog}: cannot narrow the seeds: {e}\n")
    truncated = args.truncations if args.truncations is not None else 0 if args.deep else TRUNCATIONS
    if args.per_seed < 0 or truncated < 0 or args.jobs < 1 or args.time_budget <= 0:
        ap.error("--per-seed and --truncations must be 0 or more, --jobs 1 or more and --time-budget more than 0")
    tools = binaries(args)
    if tools is None:
        return 2
    target, binary, cases = tools
    return run(
        args.root, [str(binary)], [str(cases)], args.per_seed, args.version, args.jobs, args.save,
        target_dir=target, time_budget=args.time_budget, deep=args.deep, truncated=truncated, swept=args.deep,
        selection=selection,
        base=narrowing.resolve_base(args.root, args.base, narrowed=bool(selection and selection.narrowed)),
    )


def sort_args(p):
    p.add_argument("--go", action="store_true", help="place and remove them (without it, the table alone)")
    p.epilog = ("手で保存するときは、入力を target/fuzz/new/ から tests/fuzz/ へ写し、並んだ雛形の項目を足す"
                "（run の --save は、新しい類の入力を直に tests/fuzz/ に書く。signal は書かない）。"
                "作業ツリーの入力は work.py patch が主のツリーの target/fuzz/new/ に写す。名は中身の hash なので、"
                "消した入力も、同じ作業ツリーで patch をもう一度回すとまた写る（sort がまた消す）。")


def sort_command(args):
    if args.jobs < 1:
        args.parser_.error("--jobs must be 1 or more")
    tools = binaries(args)
    if tools is None:
        return 2
    target, binary, cases = tools
    with tempfile.TemporaryDirectory(prefix="onsa-fuzz-sort-") as work:
        runner = Runner([str(binary)], work)
        return sort_inputs(args.root, runner, FixRunner([str(cases)], runner.work / "fix"), args.jobs,
                           target / WORK / NEW, args.go)


def binaries(args):
    """(cargo's target directory, the compiler, `onsa_cases`), built unless named; None (said) when it cannot."""
    target = target_directory(args.root)
    if target is None:
        print("fuzz: cannot read cargo's target directory (cargo metadata)", file=sys.stderr)
        return None
    binary = args.binary
    if binary is None:
        if not build(args.root):
            print("fuzz: cannot build the compiler (cargo build -p onsa_cli)", file=sys.stderr)
            return None
        binary = target / "debug" / "onsa"
    cases = args.cases_binary
    if cases is None:
        if not build(args.root, cases=True):
            print("fuzz: cannot build onsa_cases (cargo build -p onsa_tests --bin onsa_cases)", file=sys.stderr)
            return None
        cases = target / "debug" / "onsa_cases"
    return target, binary, cases


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "run": C(run_args, run_command, ("parent", "t", "i", "b"),
             "保存済みの入力を一覧と照らし、変異と切り詰めを両方の命令と候補の段に通す（gate の `fuzz`。`--deep` は `fuzz-deep`）",
             "gate が命令の名を付けずに呼ぶ。手で回すのは、作業がファズかその道具を扱うときだけ（rules/checks.md 4 章）",
             "fuzz.py run --changed-since auto --sample 0.1 --salt X-9/U11"),
    "sort": C(sort_args, sort_command, ("parent",),
              "target/fuzz/new/ の入力を今のバイナリで回し、同名・直った・既知・異常終了・新しい類に分ける（`--go` で置く・消す）",
              "区切りで、主のツリーの gate の要約の `fuzz new:` に入力が並んだとき。表を読んでから `--go`",
              "fuzz.py sort --go"),
}  # fmt: skip


def COMMON(p):
    """What every subcommand but `help` takes (`repo.parse_command`; `docs.py check`'s `tools` reads it too)."""
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    p.add_argument("--binary", type=Path, help="the compiler (default: build <target directory>/debug/onsa)")
    p.add_argument("--cases-binary", type=Path,
                   help="the fix stage's onsa_cases (default: build <target directory>/debug/onsa_cases)")
    p.set_defaults(parser_=p)


def main(argv=None):
    """`fuzz.py <command> …`; with no command (no argument, or `-…` first but `-h` and `--help`: the gate's
    `fuzz` and `fuzz-deep`), `run`."""
    argv = sys.argv[1:] if argv is None else list(argv)
    named = argv[:1] and (not argv[0].startswith("-") or argv[0] in ("-h", "--help"))
    args = repo.parse_command("fuzz.py", __doc__.split("\n")[0], COMMANDS, argv if named else ["run", *argv], COMMON)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
