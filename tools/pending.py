#!/usr/bin/env python3
"""The list of things that are expected not to pass yet (plan D-16 7, Q-08, §8.6).

The list is `tests/pending.toml`, one `[[pending]]` table per entry. The
meaning is the same for every kind: a listed target is expected to fail; when
it passes, the gate fails and asks for the entry to be removed. The kinds and
the form of `target`:

    spec-example  "§<section> <hash>: <first line>" of a ```onsa block of the
                  spec (`spec_blocks.ID_FORM`)
    diag-code     a diagnostic code with fewer negative examples than the
                  gate requires, "E0812"        (matched by tools/diag_codes.py, W1-02)
    gate          a pendable gate item of `tools/gate_steps.py` ("c-header"),
                  or a case that the item itself reports, "<item>/<case>": the
                  item applies those entries (a listed case that fails is
                  pending; one that passes, and an entry that names no case of
                  the item, fail). An item is listed as a whole or by case,
                  not both. The C checks name a case `<path>[<target>]`
                  (`c-gcc/tests/conformance/voice.onsa[host]`), and the header
                  checks `<path>[<target>]/<compiler>`  (onsa_tests::ccheck, W1-06).
                  The test vectors name a case `<operation>` (`vectors-interp/u64.mul`)
                  and `<operation>[<toolchain>]` (`vectors-c/u32.mul[c-gcc]`), and
                  are listed only by case (`by_case_only`; onsa_tests::vectors, W2-02)
    test-case     a test case: a path from the repository root (a file or a
                  package directory), optionally "<path>::<test name>"   (W1-03)
    fuzz-input    a saved fuzz input: a path from the repository root  (W1-04)

Paths are in their canonical form: relative, `/`-separated, no `.` or `..`
component, no empty component, no trailing `/`.

Every entry has all of: kind, target, reasons (S / R numbers, one or more),
until (the work that removes it: a W ID of `docs/rework-phase1.md` §3 or a T
ID of `docs/implementation-tasks.md` §4, not marked done), note.

A case entry `<item>/<case>` of a gate item with `counts_rows` (the test
vectors) also has `rows = N`, how many rows fail, and `digest = "<16 hex>"`,
which (the item prints both): the item fails when either differs, so a new
failure does not hide behind the entry, nor one row failing instead of
another (W2-02/b). No other entry has `rows` or `digest`.

One field is optional: `expect = "internal"`, only on a `test-case` entry of a
whole case (no `::<test name>`), or on a case entry `<item>/<case>` of a gate
item with `expect_internal` (`vectors-interp`, W2-02). An internal error of the
compiler (S-67) is never silenced by the list (W1-04); with this field, the
case is expected to end in an internal error: another failure is an error of
the entry, and a pass asks for the entry to be removed (the runner or the item
checks it).

`until = "P2"` names the second phase instead of a work (K-13 rule 3): a code
of the second phase waits for no work of the first. Only the kinds of
`PHASE2_KINDS` may use it. Its reasons may also name a section of the spec
("§20", a numbered heading of `onsa-lang-spec-0.3.md`): the spec itself sets
the scope of the first phase; other entries name S / R numbers only. The summary counts it as the stage `P2`, after the
W and M stages. `--stage-end P2` is a usage error (the first phase never ends
the second); `--stage-end M9`, the end of the first phase, fails on every
entry left whose until is not P2 (K-13: what is left after M9 is only P2).

This module is the only place that validates the list (the Rust reader in
`onsa_tests::pending` only reads it). It runs on its own:

    tools/pending.py [--pending FILE] [--root DIR] [--gate-steps a,b,...] [--stage-end W3]

Exit 0 if the list is valid (and, with --stage-end, nothing of that stage is
left), 1 otherwise, 2 on a usage error.
"""
import argparse
import posixpath
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_steps  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
PENDING = repo.PENDING

KINDS = ("spec-example", "diag-code", "gate", "test-case", "fuzz-input")
FIELDS = ("kind", "target", "reasons", "until", "note")
# Optional fields: `expect` (only "internal": a whole test case, a case of an item with
# `expect_internal`), `rows` and `digest` (both required on, and only on, a case of an item with
# `counts_rows`).
OPTIONAL_FIELDS = ("expect", "rows", "digest")
DIGEST = re.compile(r"[0-9a-f]{16}")
EXPECTS = ("internal",)

# The form of `target` per kind. Paths are checked further in `_check_target`.
TARGET_FORMS = {
    "spec-example": spec_blocks.ID_FORM,
    "diag-code": re.compile(r"E\d{4}"),
    "gate": re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*(?:/\S+)?"),
    "test-case": re.compile(r"[^\s:][^:]*(?:::\S.*)?"),
    "fuzz-input": re.compile(r"[^\s:][^:]*"),
}
REASON = re.compile(r"[SR]-\d+")
# A spec section as a reason, only of `until = "P2"` (the spec §20 sets what the first phase is).
SECTION = re.compile(r"§\d+(?:\.\d+)*")
WORK = re.compile(r"(W\d+)-\d+|T(\d+)-\d+")

# The second phase as an `until` (K-13 rule 3), the kinds that may use it, and
# the stage that ends the first phase (plan §4 M9).
PHASE2 = "P2"
PHASE2_KINDS = ("diag-code",)
PHASE1_END = "M9"

# The documents keep the IDs in table rows `| ID |`, `| ID ✅ |` (done).
DocsError = repo.RepoError


@dataclass(frozen=True)
class Entry:
    index: int  # position in the file, for messages
    kind: str
    target: str
    reasons: tuple
    until: str
    note: str
    expect: str = None
    rows: int = None
    digest: str = None

    def label(self):
        return f'pending[{self.index}] {self.kind} "{self.target}"'


@dataclass
class Docs:
    works: set  # W and T IDs
    done: set  # the works marked done (✅)
    reasons: set  # S and R IDs
    sections: set = frozenset()  # the numbered headings of the spec ("20", "11.4")


def stage_of(work):
    """`W3-07` -> `W3`, `T5-8` -> `M5` (the milestone of a T ID), `P2` -> `P2`."""
    if work == PHASE2:
        return PHASE2
    m = WORK.fullmatch(work)
    if not m:
        return None
    return m.group(1) if m.group(1) else f"M{m.group(2)}"


def _table(doc, text, start, end, id_pattern, what):
    rows = repo.rows(repo.section(text, start, end, doc) if start else text, id_pattern)
    if not rows:
        raise DocsError(f"{doc}: no table rows of {what} found" + (f" in `{start}`" if start else ""))
    return rows


def load_docs(root=ROOT):
    """The IDs of the tables. Raises DocsError when a table is not found."""

    rework, plan, review = (repo.read(root, d) for d in (repo.DOC_REWORK, repo.DOC_PLAN, repo.DOC_REVIEW))
    w = _table(repo.DOC_REWORK, rework, "## 3.", "## 4.", r"W\d+-\d+", "W works")
    t = _table(repo.DOC_PLAN, plan, "## 4.", "## 5.", r"T\d+-\d+", "T works")
    s = _table(repo.DOC_PLAN, plan, "## 2.", "## 3.", r"S-\d+", "S numbers")
    r = _table(repo.DOC_REVIEW, review, None, None, r"R-\d+", "R numbers")
    works = {**w, **t}
    sections = set(spec_blocks.headings(repo.read(root, repo.SPEC)))
    if not sections:
        raise DocsError(f"{repo.SPEC}: no numbered heading found")
    return Docs(works=set(works), done={k for k, d in works.items() if d}, reasons=set(s) | set(r), sections=sections)


def load(path):
    """Read the list. Returns (entries, errors); entries are the well-formed ones."""
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return [], [f"{path}: not found"]
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        return [], [f"{path}: {e}"]
    errors = [f"{path}: unknown top-level key `{k}` (only [[pending]])" for k in data if k != "pending"]
    raw = data.get("pending", [])
    if not isinstance(raw, list):
        return [], errors + [f"{path}: `pending` must be an array of tables ([[pending]])"]
    entries = []
    for i, item in enumerate(raw):
        where = f"pending[{i}]"
        if not isinstance(item, dict):
            errors.append(f"{where}: not a table")
            continue
        bad = False
        for k in item:
            if k not in FIELDS and k not in OPTIONAL_FIELDS:
                errors.append(f"{where}: unknown field `{k}`")
                bad = True
        for k in FIELDS:
            if k not in item:
                errors.append(f"{where}: missing field `{k}`")
                bad = True
        if bad:
            continue
        for k in ("kind", "target", "until", "note"):
            if not isinstance(item[k], str) or not item[k].strip():
                errors.append(f"{where}: `{k}` must be a non-empty string")
                bad = True
        reasons = item["reasons"]
        if not isinstance(reasons, list) or not all(isinstance(r, str) for r in reasons):
            errors.append(f"{where}: `reasons` must be an array of strings")
            bad = True
        elif not reasons:
            errors.append(f"{where}: `reasons` needs at least one S / R number")
            bad = True
        expect = item.get("expect")
        if expect is not None and expect not in EXPECTS:
            errors.append(f"{where}: `expect` must be one of {', '.join(repr(x) for x in EXPECTS)}")
            bad = True
        rows = item.get("rows")
        if rows is not None and (not isinstance(rows, int) or isinstance(rows, bool) or rows < 1):
            errors.append(f"{where}: `rows` must be a positive integer (the failing rows the entry holds)")
            bad = True
        digest = item.get("digest")
        if digest is not None and (not isinstance(digest, str) or not DIGEST.fullmatch(digest)):
            errors.append(f"{where}: `digest` must be 16 lowercase hex digits (which rows fail, as the item prints it)")
            bad = True
        if bad:
            continue
        entries.append(
            Entry(i, item["kind"], item["target"], tuple(reasons), item["until"], item["note"], expect, rows, digest)
        )
    return entries, errors


def validate(entries, docs, root=ROOT, pendable_steps=None):
    """Check the entries against their forms and the documents. Returns errors.

    `pendable_steps` are the gate items that may be listed (default: the
    pendable items of `gate_steps.STEPS`)."""
    if pendable_steps is None:
        pendable_steps = gate_steps.pendable()
    errors = []
    seen = {}
    for e in entries:
        where = e.label()
        if e.kind not in KINDS:
            errors.append(f"{where}: unknown kind `{e.kind}` (one of {', '.join(KINDS)})")
            continue
        errors += [f"{where}: {m}" for m in _check_target(e, root, pendable_steps)]
        counted = e.kind == "gate" and "/" in e.target and e.target.split("/", 1)[0] in gate_steps.counts_rows()
        for field, value in (("rows", e.rows), ("digest", e.digest)):
            if counted and value is None:
                errors.append(
                    f"{where}: `{field}` is required: the item counts the failing rows of a case, and the entry holds "
                    "exactly those rows (`rows`, how many; `digest`, which)"
                )
            if not counted and value is not None:
                errors.append(
                    f"{where}: `{field}` is only for a case entry of the gate items "
                    f"{', '.join(f'`{n}`' for n in gate_steps.counts_rows())}"
                )
        if e.expect is not None and not _may_expect(e):
            errors.append(
                f"{where}: `expect` is only for a `test-case` entry of a whole case (no `::<test name>`), or a case "
                f"entry of the gate items {', '.join(f'`{n}`' for n in gate_steps.expect_internal())}"
            )
        for r in e.reasons:
            if SECTION.fullmatch(r):
                if e.until != PHASE2:
                    errors.append(f"{where}: reason `{r}`: a spec section is a reason only of `until = \"{PHASE2}\"`")
                elif r[1:] not in docs.sections:
                    errors.append(f"{where}: reason `{r}` is not a numbered heading of {repo.SPEC}")
            elif not REASON.fullmatch(r):
                errors.append(f"{where}: reason `{r}` is not an S / R number (`S-45`, `R-23`)")
            elif r not in docs.reasons:
                errors.append(f"{where}: reason `{r}` is not in the tables (plan §2 for S, review for R)")
        if len(set(e.reasons)) != len(e.reasons):
            errors.append(f"{where}: a reason is listed twice")
        if e.until == PHASE2:
            if e.kind not in PHASE2_KINDS:
                errors.append(f"{where}: until `{PHASE2}` (the second phase) is only for {', '.join(PHASE2_KINDS)} entries")
        elif not WORK.fullmatch(e.until):
            errors.append(f"{where}: until `{e.until}` is not a work ID (`W3-07`, `T5-8`) or `{PHASE2}`")
        elif e.until not in docs.works:
            errors.append(f"{where}: until `{e.until}` is not in the tables (rework §3 for W, plan §4 for T)")
        elif e.until in docs.done:
            errors.append(f"{where}: until `{e.until}` is a work marked done; remove the entry or change `until`")
        key = (e.kind, e.target)
        if key in seen:
            errors.append(f"{where}: the same target as pending[{seen[key]}]")
        else:
            seen[key] = e.index
    errors += _whole_and_cases(entries)
    return errors


def _may_expect(e):
    """Whether the entry may say `expect = "internal"`."""
    if e.kind == "test-case":
        return "::" not in e.target
    if e.kind == "gate" and "/" in e.target:
        return e.target.split("/", 1)[0] in gate_steps.expect_internal()
    return False


def _whole_and_cases(entries):
    """A gate item listed both as a whole and by case (`<item>/<case>`), and a
    whole entry of an item listed only by case."""
    gate = [e for e in entries if e.kind == "gate"]
    whole = {e.target: e for e in gate if "/" not in e.target}
    out = [
        f"{e.label()}: `{e.target}` may be listed only by case (`{e.target}/<case>`): a whole entry hides every new "
        "failure of the item"
        for e in whole.values()
        if e.target in gate_steps.by_case_only()
    ]
    for e in gate:
        item = e.target.split("/", 1)[0]
        if "/" in e.target and item in whole:
            out.append(f"{e.label()}: `{item}` is also listed as a whole (pending[{whole[item].index}]); keep one")
    return out


def _check_target(e, root, pendable_steps):
    if not TARGET_FORMS[e.kind].fullmatch(e.target):
        return [f"target is not of the {e.kind} form"]
    if e.kind == "gate":
        item = e.target.split("/", 1)[0]
        if item not in pendable_steps:
            listed = ", ".join(pendable_steps) or "none yet"
            return [f"`{item}` is not a gate item that may be listed (pendable items: {listed})"]
    if e.kind in ("test-case", "fuzz-input"):
        path = e.target.split("::", 1)[0]
        problem = path_problem(path)
        if problem:
            return [problem]
        if not (root / path).exists():
            return [f"`{path}` does not exist (remove the entry, or fix the path)"]
    return []


def path_problem(path):
    """Why `path` is not a canonical repository path, or None."""
    if "\\" in path:
        return "the path must use `/`, not `\\`"
    if path.startswith("/"):
        return "the path must be relative to the repository root"
    parts = path.split("/")
    if any(p in ("", ".", "..") for p in parts):
        return f"the path must be canonical (`{posixpath.normpath(path)}`: no `./`, `..`, `//` or trailing `/`)"
    return None


def of_kind(entries, kind):
    return [e for e in entries if e.kind == kind]


def stage_counts(entries):
    counts = {}
    for e in entries:
        s = stage_of(e.until) or "?"
        counts[s] = counts.get(s, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: stage_key(kv[0])))


def stage_key(stage):
    """W stages, then M stages, then the second phase, then anything else."""
    m = re.fullmatch(r"([WMP])(\d+)", stage)
    if not m:
        return (3, 99, stage)
    return ("WMP".index(m.group(1)), int(m.group(2)), stage)


def stages_line(entries):
    counts = stage_counts(entries)
    if not counts:
        return "pending: none"
    body = ", ".join(f"{s} {n}" for s, n in counts.items())
    return f"pending by stage: {body} (total {len(entries)})"


def known_stages(docs):
    return {stage_of(w) for w in docs.works}


def stage_problem(stage, docs):
    """Why `stage` is not a usable `--stage-end` value, or None."""
    if not stage:
        return "--stage-end needs a stage (W3, M5)"
    if stage == PHASE2:
        return f"`{PHASE2}` is the second phase, which the first phase does not end; the last stage is {PHASE1_END}"
    if stage not in known_stages(docs):
        known = ", ".join(sorted(known_stages(docs), key=stage_key))
        return f"unknown stage `{stage}` (one of {known})"
    return None


def stage_end_errors(entries, stage):
    """The entries left at the end of `stage`. At the end of the first phase
    (`PHASE1_END`), every entry but those of the second phase."""
    if stage == PHASE1_END:
        left = [e for e in entries if e.until != PHASE2]
    else:
        left = [e for e in entries if stage_of(e.until) == stage]
    return [f"{e.label()}: still pending at the end of {stage} (until {e.until}): {e.note}" for e in left]


def show_path(path, root):
    try:
        return str(Path(path).resolve().relative_to(Path(root).resolve()))
    except ValueError:
        return str(path)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Validate tests/pending.toml.")
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--pending", type=Path, default=None)
    ap.add_argument("--gate-steps", default=None, help="comma separated pendable gate items (default: tools/gate_steps.py)")
    ap.add_argument("--stage-end", default=None, metavar="STAGE", help="fail if entries of STAGE (W3, M5) remain")
    args = ap.parse_args(argv)
    root = args.root
    path = args.pending or root / PENDING
    try:
        docs = load_docs(root)
    except DocsError as e:
        print(f"the document tables are not found: {e}")
        return 1
    if args.stage_end is not None:
        problem = stage_problem(args.stage_end, docs)
        if problem:
            print(problem, file=sys.stderr)
            return 2
    steps = None if args.gate_steps is None else [n for n in args.gate_steps.split(",") if n]
    entries, errors = load(path)
    errors += validate(entries, docs, root, steps)
    if args.stage_end is not None:
        errors += stage_end_errors(entries, args.stage_end)
    for m in errors:
        print(m)
    print(stages_line(entries))
    if errors:
        print(f"{len(errors)} problem(s) in {show_path(path, root)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
