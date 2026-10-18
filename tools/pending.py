#!/usr/bin/env python3
"""The list of things that are expected not to pass yet (D-16 7, Q-08, rules/process.md 8.6).

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
    fix-contract  one fix candidate that breaks the contract of spec §18.1
                  (S-236): "<file from the repository root>:<line>:<col>
                  <code> fix<K>", the K-th candidate of the diagnostic of that
                  code at that place of a case's check (matched by the test
                  runner, `onsa_tests::run::reconcile`, W3-17)
    foreign-form  a row of the closed list of the forms of other languages,
                  `spec/foreign-forms.toml` (S-250), whose examples do not pass
                  yet: the row's `id`, "semicolon" (matched by
                  `onsa_tests::foreign_forms`, W3-15)

Paths are in their canonical form: relative, `/`-separated, no `.` or `..`
component, no empty component, no trailing `/`.

Every entry has all of: kind, target, reasons (S / R numbers, one or more),
until (the work that removes it: a W ID of `tasks/W/`, not marked done), note.

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

`until = "PH2"` names the second phase instead of a work (K-13 rule 3): a code
of the second phase waits for no work of the first. Only the kinds of
`PHASE2_KINDS` may use it. Its reasons may also name a section of the spec
("§20", a numbered heading of `spec/`): the spec itself sets
the scope of the first phase; other entries name S / R numbers only. The summary counts it as the stage `PH2`, after
every stage. The stages and their order are the table of `tasks/stages.md` (`repo.Layout.stages`); its last stage
(M9) ends the first phase. `--stage-end PH2` is a usage error (the first phase never ends
the second); `--stage-end` the last stage fails on every
entry left whose until is not PH2 (K-13: what is left after M9 is only PH2).

This module is the only place that validates the list (the Rust reader in
`onsa_tests::pending` only reads it). Its commands are `check`, `list`, `add`
and `remove` (COMMANDS, rules/tools.md 9.1); `pending.py help` shows their
purposes, times, roles and examples (`--help` lists them). A call with no
command (no argument, or a first argument `-…` but `-h` and `--help`: the
gate's `pending`) is `check`: exit 0 if the list is
valid (and, with --stage-end, nothing of that stage is left), 1 otherwise, 2 on
a usage error. `list` prints `until<TAB>reasons<TAB>kind<TAB>target`. `remove`
takes off every entry whose target is exactly one of the targets, with the
blank lines before it; `add` appends an entry written like the others after a
blank line, only when `check` finds no new problem with it. Both write only when
every target is found (or the entry passes), keep the rest of the file byte for
byte, and stop on a table that is not one `[[pending]]` line followed by its
`key = value` lines.
"""
import posixpath
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs as docs_tool  # noqa: E402
import gate_steps  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
PENDING = repo.PENDING

KINDS = ("spec-example", "diag-code", "gate", "test-case", "fuzz-input", "fix-contract", "foreign-form")

FIELDS = repo.PENDING_FIELDS

# The form of `target` per kind. Paths are checked further in `_check_target`.
TARGET_FORMS = {
    "spec-example": spec_blocks.ID_FORM,
    "diag-code": re.compile(r"E\d{4}"),
    "gate": re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*(?:/\S+)?"),
    "test-case": re.compile(r"[^\s:][^:]*(?:::\S.*)?"),
    "fuzz-input": re.compile(r"[^\s:][^:]*"),
    "fix-contract": re.compile(r"[^\s:][^:\s]*:[1-9]\d*:[1-9]\d* E\d{4} fix[1-9]\d*"),
    "foreign-form": re.compile(r"[a-z][a-z0-9]*(?:_[a-z0-9]+)*"),
}
# The closed list of the forms of other languages (S-250): the rows a
# `foreign-form` entry names.

REASON = repo.id_form("S", "R")
# A spec section as a reason, only of `until = "PH2"` (the spec §20 sets what the first phase is).
SECTION = re.compile(r"§\d+(?:\.\d+)*")
WORK = re.compile(repo.KIND["W"].pattern)
# A unit of an item of `issues/X/` (`X-3/U1`, `X-3/U1c-1`): `--work` takes it besides a W ID (X-1 U3).
UNIT = re.compile(r"(%s)/U\d+[a-z]*(?:-\d+)*" % repo.KIND["X"].pattern)

# The second phase as an `until` (K-13 rule 3) and the kinds that may use it. The stage that ends the
# first phase is the last of the table of the stages (`Docs.stages`).
PHASE2 = repo.PHASE2
PHASE2_KINDS = ("diag-code",)

# The documents keep the IDs in table rows `| ID |`, `| ID ✅ |` (done).
DocsError = repo.RepoError


Entry = repo.PendingEntry
load = repo.load_pending


@dataclass
class Docs:
    works: set  # W IDs
    done: set  # the works done (`status = "DONE"`)
    reasons: set  # S and R IDs
    stages: tuple  # in their order (`repo.Layout.stages`); the last ends the first phase
    works_at: str  # where the works are read, for messages (`docs.Index.place`)
    sections: set = frozenset()  # the numbered headings of the spec ("20", "11.4")
    reasons_at: str = ""  # where the S and R IDs are read, for messages (`docs.Index.place`)
    items: frozenset = frozenset()  # the X IDs (`issues/X/`; empty when it is not there)


def work_known(work, docs):
    """`--work` names a W of `docs.works` or a unit (`UNIT`) of an item of `docs.items`."""
    m = UNIT.fullmatch(work)
    return work in docs.works if m is None else m.group(1) in docs.items


def stage_of(work):
    """`W3-07` -> `W3`, a stage (`M5`) -> itself, `PH2` -> `PH2`; None for anything else."""
    if work == PHASE2 or repo.STAGE_NAME.fullmatch(work):
        return work
    return work.split("-")[0] if WORK.fullmatch(work) else None


def load_docs(root=ROOT):
    """The IDs of the documents, each kind from the files of its directory (`docs.Index`; a work is done
    when its `status` is DONE). Raises DocsError when a directory is not there or has no file of an ID."""
    index = docs_tool.Index.of(root)
    lay, works = index.layout, dict(index.work_done())
    if not works:
        raise DocsError(f"{repo.KIND['W'].dir}/: no file of an ID")
    at = index.place("W")
    reasons = index.ids("S") | index.ids("R")
    spec = repo.spec_doc(root)
    sections = set(spec_blocks.headings(spec.text))
    if not sections:
        raise DocsError(f"{spec.parts[0][0]}: no numbered heading found")
    return Docs(works=set(works), done={k for k, d in works.items() if d}, reasons=reasons, sections=sections,
                stages=lay.stages(), works_at=at, reasons_at=f"{index.place('S')}, {index.place('R')}",
                items=frozenset(index.known("X") or ()))  # fmt: skip


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
                    errors.append(f"{where}: reason `{r}` is not a numbered heading of {repo.SPEC_SHOWN}")
            elif not REASON.fullmatch(r):
                errors.append(f"{where}: reason `{r}` is not an S / R number (`S-45`, `R-23`)")
            elif r not in docs.reasons:
                errors.append(f"{where}: reason `{r}` is not in {docs.reasons_at}")
        if len(set(e.reasons)) != len(e.reasons):
            errors.append(f"{where}: a reason is listed twice")
        if e.until == PHASE2:
            if e.kind not in PHASE2_KINDS:
                errors.append(f"{where}: until `{PHASE2}` (the second phase) is only for {', '.join(PHASE2_KINDS)} entries")
        elif e.until not in docs.works:
            errors.append(f"{where}: until `{e.until}` is not a work of {docs.works_at} (`W3-07`) or `{PHASE2}`")
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


def foreign_form_ids(root):
    """The `id`s of the rows of the table of the foreign forms under `root`
    (`repo.FOREIGN_FORMS`), or an error message (the file is missing or not TOML)."""
    rel = repo.FOREIGN_FORMS.as_posix()
    try:
        data = tomllib.loads((Path(root) / rel).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return f"`{rel}` does not exist"
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as err:
        return f"`{rel}` is not TOML: {err}"
    forms = data.get("form", [])
    return {f.get("id") for f in forms if isinstance(f, dict)} if isinstance(forms, list) else set()


def _check_target(e, root, pendable_steps):
    if not TARGET_FORMS[e.kind].fullmatch(e.target):
        return [f"target is not of the {e.kind} form"]
    if e.kind == "foreign-form":
        ids = foreign_form_ids(root)
        if isinstance(ids, str):
            return [ids]
        if e.target not in ids:
            return [f"`{e.target}` is not the `id` of a row of `{repo.FOREIGN_FORMS.as_posix()}` (remove the entry, or fix the id)"]
    if e.kind == "gate":
        item = e.target.split("/", 1)[0]
        if item not in pendable_steps:
            listed = ", ".join(pendable_steps) or "none yet"
            return [f"`{item}` is not a gate item that may be listed (pendable items: {listed})"]
    if e.kind in ("test-case", "fuzz-input", "fix-contract"):
        path = e.target.split(" ", 1)[0].rsplit(":", 2)[0] if e.kind == "fix-contract" else e.target.split("::", 1)[0]
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


def stage_counts(entries, stages):
    counts = {}
    for e in entries:
        s = stage_of(e.until) or "?"
        counts[s] = counts.get(s, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: stage_key(kv[0], stages)))


def stage_key(stage, stages):
    """The stages in the order of `stages` (the table), then the second phase, then anything else."""
    if stage in stages:
        return (0, stages.index(stage), stage)
    return (1, 0, stage) if stage == PHASE2 else (2, 0, stage)


def stages_line(entries, stages):
    counts = stage_counts(entries, stages)
    if not counts:
        return "pending: none"
    body = ", ".join(f"{s} {n}" for s, n in counts.items())
    return f"pending by stage: {body} (total {len(entries)})"


def stage_problem(stage, docs):
    """Why `stage` is not a usable `--stage-end` value, or None."""
    if not stage:
        return "--stage-end needs a stage (W3, M5)"
    if stage == PHASE2:
        return f"`{PHASE2}` is the second phase, which the first phase does not end; the last stage is {docs.stages[-1]}"
    if stage not in docs.stages:
        return f"unknown stage `{stage}` (one of {', '.join(docs.stages)}: {repo.STAGES})"
    return None


def left_at_end(until, stage, stages):
    """Whether something waiting for `until` (a work, or `PH2`) may not be left at
    the end of `stage`: a work of that stage; at the end of the first phase
    (the last of `stages`), anything but the second phase. Also used by `tools/ignores.py stale`."""
    return until != PHASE2 if stage == stages[-1] else stage_of(until) == stage


def stage_end_errors(entries, stage, stages):
    """The entries left at the end of `stage` (`left_at_end`)."""
    left = [e for e in entries if left_at_end(e.until, stage, stages)]
    return [f"{e.label()}: still pending at the end of {stage} (until {e.until}): {e.note}" for e in left]


def show_path(path, root):
    try:
        return str(Path(path).resolve().relative_to(Path(root).resolve()))
    except ValueError:
        return str(path)


# ---------------------------------------------------------------- listing and editing

KEY_LINE = re.compile(r"[a-z]+ = \S")


def blocks(text):
    """The spans of the tables: from the `[[pending]]` line to the end of its last `key = value` line.
    Raises DocsError on any other shape (a value over several lines, a key after a blank line)."""
    spans, start, end, pos = [], None, None, 0
    for line in text.splitlines(keepends=True):
        bare = line.rstrip("\n")
        if bare == "[[pending]]":
            if start is not None:
                spans.append((start, end))
            start, end = pos, pos + len(line)
        elif start is not None and KEY_LINE.match(bare) and end == pos:
            end = pos + len(line)
        elif start is not None and bare.strip() and not bare.startswith("#"):
            raise DocsError(f"line {text.count(chr(10), 0, pos) + 1}: not a `key = value` line of the table above")
        pos += len(line)
    if start is not None:
        spans.append((start, end))
    whole = tomllib.loads(text).get("pending", [])
    if [tomllib.loads(text[a:b]).get("pending", [None])[0] for a, b in spans] != whole:
        raise DocsError("the tables are not read the same one by one as in the whole file")
    return spans


def _write_checked(path, text, expect):
    """Write `text` when its entries are `expect` (as TOML tables) and it reads as tables; else say why."""
    try:
        if tomllib.loads(text).get("pending", []) != expect:
            raise DocsError("the edited list does not hold the expected entries")
        blocks(text)
    except (DocsError, tomllib.TOMLDecodeError) as e:
        print(f"{e}; nothing written")
        return False
    Path(path).write_text(text, encoding="utf-8")
    return True


def list_args(p):
    p.add_argument("--until", help="a work or a stage (W3-11, W3)")
    p.add_argument("--reason")
    p.add_argument("--kind")


def add_args(p):
    for k in ("kind", "target", "reasons", "until", "note"):
        p.add_argument(f"--{k}", required=True, help="comma separated S / R numbers (S-497,S-414)" if k == "reasons" else None)


def edit(args):
    """`list`, `remove` and `add` (`args.cmd`)."""
    path = args.pending or args.root / PENDING
    text = Path(path).read_text(encoding="utf-8")
    entries, errors = load(path, text)
    try:
        spans = blocks(text)
    except (DocsError, tomllib.TOMLDecodeError) as e:
        errors.append(f"{show_path(path, args.root)}: {e}")
    if errors:
        print("\n".join(errors + ["the list is not read; nothing done"]))
        return 1
    whole = tomllib.loads(text).get("pending", [])
    if args.cmd == "list":
        for e in entries:
            if args.until in (None, e.until, stage_of(e.until)) and args.reason in (None, *e.reasons) and args.kind in (None, e.kind):
                print(f"{e.until}\t{', '.join(e.reasons)}\t{e.kind}\t{e.target}")
        return 0
    if args.cmd == "remove":
        missing = [t for t in args.targets if not any(e.target == t for e in entries)]
        if missing:
            print("\n".join(f"no entry of target `{t}`" for t in missing) + "\nnothing written")
            return 1
        out, gone = text, [i for i, e in enumerate(entries) if e.target in args.targets]
        for i in reversed(gone):
            a, b = spans[i]
            if a >= 2 and out[a - 2:a] == "\n\n":
                while a >= 2 and out[a - 2:a] == "\n\n":
                    a -= 1
            else:
                while out[b:b + 1] == "\n":
                    b += 1
            out = out[:a] + out[b:]
        if not _write_checked(path, out, [w for i, w in enumerate(whole) if i not in gone]):
            return 1
        print(f"{len(gone)} entr{'y' if len(gone) == 1 else 'ies'} removed")
        return 0
    q = spec_blocks.toml_string
    reasons = [r.strip() for r in args.reasons.split(",") if r.strip()]
    fields = (("kind", q(args.kind)), ("target", q(args.target)), ("reasons", f"[{', '.join(map(q, reasons))}]"),
              ("until", q(args.until)), ("note", q(args.note)))
    out = text + ("" if text.endswith("\n") or not text else "\n") + ("\n" if text else "")
    out += "[[pending]]\n" + "".join(f"{k} = {v}\n" for k, v in fields)
    docs = load_docs(args.root)
    new_entries, new_errors = load(path, out)
    before = set(validate(entries, docs, args.root))
    new = new_errors + [m for m in validate(new_entries, docs, args.root) if m not in before]
    if new or len(new_entries) != len(entries) + 1:
        print("\n".join(new + ["the entry is not added"]))
        return 1
    if not _write_checked(path, out, whole + [tomllib.loads(out[out.rindex("[[pending]]"):])["pending"][0]]):
        return 1
    print(f"added: {new_entries[-1].label()}")
    return 0


def check_args(p):
    p.add_argument("--gate-steps", default=None, help="comma separated pendable gate items (default: tools/gate_steps.py)")
    p.add_argument("--stage-end", default=None, metavar="STAGE", help="fail if entries of STAGE (W3, M5) remain")


def check(args):
    root = args.root
    path = args.pending or root / PENDING
    try:
        docs = load_docs(root)
    except DocsError as e:
        print(f"cannot read the IDs: {e}")
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
        errors += stage_end_errors(entries, args.stage_end, docs.stages)
    for m in errors:
        print(m)
    print(stages_line(entries, docs.stages))
    if errors:
        print(f"{len(errors)} problem(s) in {show_path(path, root)}")
        return 1
    return 0


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "check": C(check_args, check, ("parent", "i"),
               "一覧を、項目の形・文書の ID・済んだ作業と照らして確かめる（gate の `pending`）。`--stage-end` はその段の項目が残れば失敗にする",
               "一覧を編集した後と、作業の状態を変えた後（gate の `pending` と同じ）。段の終わりは `--stage-end`",
               "pending.py check --stage-end W3"),
    "list": C(list_args, edit, ("parent", "t", "i", "b"),
              "項目を `until<TAB>reasons<TAB>kind<TAB>target` で並べる（`--until` は作業か段。`--reason`・`--kind` でも絞る）",
              "載っている項目を探すとき（実装の担当が外す前、テストの担当と壊す側が載る項目を確かめるとき）",
              "pending.py list --until W3-11 --kind test-case"),
    "add": C(add_args, edit, ("parent", "t", "i"),
             "項目を一つ、他と同じ書き方で末尾に足す（`check` が新しい問題を見つけないときだけ書く）",
             "載せる項目を足すとき（実装の担当は並行の作業が無いとき。テストの担当は仮に入れて回すときだけで、回した後に `remove` で戻す）",
             "pending.py add --kind test-case --target tests/spec/ops/groups.onsa --reasons S-497 --until W3-11 --note '…'"),
    "remove": C(lambda p: p.add_argument("targets", nargs="+"), edit, ("parent", "t", "i"),
                "target がちょうど一致する項目を、前の空行とともに外す（全ての target が見つかったときだけ書く）",
                "実装した作業が、通るようになった項目を外すとき（一覧にあるのに通るものは gate が失敗にする）。テストの担当が、仮に入れた項目を回した後に戻すとき",
                "pending.py remove tests/spec/ops/groups.onsa E0812"),
}  # fmt: skip


def COMMON(p):
    """What every subcommand but `help` takes (`repo.parse_command`; `docs.py check`'s `tools` reads it too)."""
    p.add_argument("--root", type=Path, default=ROOT)
    p.add_argument("--pending", type=Path, default=None, help=f"the list (default: <root>/{PENDING})")


def main(argv=None):
    """`pending.py <command> …`; with no command (no argument, or `-…` first but `-h` and `--help`: the gate's
    `pending`), `check`."""
    argv = sys.argv[1:] if argv is None else list(argv)
    named = argv[:1] and (not argv[0].startswith("-") or argv[0] in ("-h", "--help"))
    args = repo.parse_command("pending.py", __doc__.split("\n")[0], COMMANDS, argv if named else ["check", *argv], COMMON)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
