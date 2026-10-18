"""What the gate's tools share about the repository (D-15: each in one place).

- the paths of the spec and of the documents with tables;
- reading a document, and the cells of a row of a table (`table_cells`, with the code spans of a line);
- running `onsa_cases` (the test runner's and the compiler's lists) and
  reading its JSON;
- reading the table of the codes (`tasks/diag-codes.md`): the retired codes and the codes of the second phase;
- the Markdown documents the document tools read (`doc_files`, X-2 DT-7);
- the kinds of the IDs and their paths (`KINDS`, X-2 DT-1; each read from its directory, X-2 DT-7), and the
  spec as one text (`spec_doc`, `tools_doc`);
- the git directories of a root: the main tree or a worktree (`git_dirs`, `tree_kind`);
- the stages in their order (`Layout.stages`, the table of `tasks/stages.md`, X-2 U6);
- reading `tests/pending.toml` (`load_pending`; `tools/pending.py` validates it);
- the roles and the subcommands of a tool with their help (`ROLES`, `Command`, `parse_command`, X9-7).
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, NamedTuple

import spec_blocks

ROOT = Path(__file__).resolve().parent.parent
PENDING = Path("tests") / "pending.toml"
# The saved fuzz inputs (tools/fuzz.py, W1-04); `onsa_tests::case::EXCLUDED` keeps them out of the cases.
FUZZ_DIR = Path("tests") / "fuzz"
CASES_CMD = ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--")

CODE = re.compile(r"(?<![A-Za-z0-9_])E\d{4}(?![0-9])")


class RepoError(Exception):
    pass


def read(root, rel):
    try:
        return (Path(root) / rel).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise RepoError(f"{rel}: {e}") from e


def read_exact(root, rel):
    """The text of a file with its line ends as they are (no newline translation)."""
    try:
        return (Path(root) / rel).read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise RepoError(f"{rel}: {e}") from e


def cases_json(root, cmd, *args):
    """The JSON `onsa_cases <args>` prints. Raises RepoError when it fails."""
    argv = [*cmd, *args]
    try:
        out = subprocess.run(argv, cwd=root, capture_output=True, text=True)
    except OSError as e:
        raise RepoError(f"cannot run `{' '.join(argv)}`: {e}") from e
    if out.returncode != 0:
        raise RepoError(f"`{' '.join(argv)}` failed (exit {out.returncode}):\n{out.stderr.rstrip()}")
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError as e:
        raise RepoError(f"`{' '.join(argv)}` printed no JSON: {e}") from e


# ---------------------------------------------------------------- a line of Markdown: the code spans, the cells of a table


def code_spans(text):
    """The (start, end) of the code spans of a line: a run of backticks opens one only when a run
    of the same length follows, which closes it (a run with no partner is plain text). Outside the
    spans a backslash escapes the character after it."""
    spans, i, n = [], 0, len(text)
    while i < n:
        if text[i] == "\\":
            i += 2
            continue
        if text[i] != "`":
            i += 1
            continue
        j = i
        while j < n and text[j] == "`":
            j += 1
        k = j
        while (k := text.find("`" * (j - i), k)) != -1:
            end = k + j - i
            if end == n or text[end] != "`":
                break
            while end < n and text[end] == "`":
                end += 1
            k = end
        if k == -1:
            i = j
        else:
            spans.append((i, k + j - i))
            i = k + j - i
    return spans


def plain(text):
    """The indexes of the characters outside the code spans and not escaped, in order."""
    code = set()
    for a, b in code_spans(text):
        code.update(range(a, b))
    i = 0
    while i < len(text):
        if text[i] == "\\":
            i += 2
            continue
        if i not in code:
            yield i
        i += 1


def table_cells(row):
    """The cells of a table row, stripped: `\\|` and a `|` in a code span do not divide (the one way the
    tools read a row, D-15)."""
    s = row.strip()
    bars = [i for i in plain(s) if s[i] == "|"]
    cells = [s[a + 1 : b] for a, b in zip([-1, *bars], [*bars, len(s)])]
    if bars[:1] == [0]:
        cells = cells[1:]
    if len(s) > 1 and bars[-1:] == [len(s) - 1]:
        cells = cells[:-1]
    return [c.strip() for c in cells]


# ---------------------------------------------------------------- tests/pending.toml (read here, validated by tools/pending.py)

PENDING_FIELDS = ("kind", "target", "reasons", "until", "note")
# Optional fields: `expect` (only "internal": a whole test case, a case of an item with
# `expect_internal`), `rows` and `digest` (both required on, and only on, a case of an item with
# `counts_rows`).
PENDING_OPTIONAL = ("expect", "rows", "digest")
DIGEST = re.compile(r"[0-9a-f]{16}")
EXPECTS = ("internal",)


@dataclass(frozen=True)
class PendingEntry:
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


def load_pending(path, text=None):
    """Read the list (or `text`, as the list at `path`). Returns (entries, errors); entries are the well-formed ones."""
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8") if text is None else text)
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
            if k not in PENDING_FIELDS and k not in PENDING_OPTIONAL:
                errors.append(f"{where}: unknown field `{k}`")
                bad = True
        for k in PENDING_FIELDS:
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
            PendingEntry(i, item["kind"], item["target"], tuple(reasons), item["until"], item["note"], expect, rows, digest)
        )
    return entries, errors


# ---------------------------------------------------------------- the table of the codes (tasks/diag-codes.md)

RETIRED_HEAD = "欠番:"
PHASE2_CELL = "第 2 期"
# "E0612〜E0614": every code from the first to the last.
CODE_RANGE_CELL = re.compile(r"E(\d{4})\s*〜\s*E(\d{4})")


def diag_text(root):
    """(the text, the document) of the table of the codes."""
    return read(root, DIAG_CODES), DIAG_CODES


def retired_codes(text, doc=None):
    """The retired codes: the line of the table of the codes (`doc` in messages, default DIAG_CODES) that
    starts with "欠番:". Codes in parentheses and after its first sentence are not retired."""
    name = str(doc or DIAG_CODES)
    lines = [line for line in text.split("\n") if line.startswith(RETIRED_HEAD)]
    if len(lines) != 1:
        raise RepoError(f"{name}: expected one line starting with `{RETIRED_HEAD}`, found {len(lines)}")
    body = re.sub(r"（[^）]*）|\([^)]*\)", "", lines[0][len(RETIRED_HEAD) :]).split("。", 1)[0]
    codes = set(CODE.findall(body))
    if not codes:
        raise RepoError(f"{name}: the `{RETIRED_HEAD}` line names no code")
    return codes


def phase2_codes(text, doc=None):
    """The codes of the rows of the table of the codes whose last cell is "第 2 期" (`doc` as in
    `retired_codes`). Ranges in the first cell (`E0612〜E0614`) are expanded."""
    codes, name = set(), str(doc or DIAG_CODES)
    for line in text.split("\n"):
        if not line.startswith("|"):
            continue
        cells = table_cells(line)
        if len(cells) < 2 or cells[-1] != PHASE2_CELL:
            continue
        first = cells[0]
        for m in CODE_RANGE_CELL.finditer(first):
            lo, hi = int(m.group(1)), int(m.group(2))
            if hi < lo:
                raise RepoError(f"{name}: the range `{m.group(0)}` goes down")
            codes |= {f"E{n:04d}" for n in range(lo, hi + 1)}
        codes |= set(CODE.findall(CODE_RANGE_CELL.sub("", first)))
    if not codes:
        raise RepoError(f"{name}: no row of the table is `{PHASE2_CELL}`")
    return codes


# ---------------------------------------------------------------- the documents (X-2 DT-7)

# The directories of the new layout (X-2 DS-1). `history/` is never read.
DOC_DIRS = ("decisions", "issues", "tasks", "spec", "rules", "design")
SPEC_DIR = "spec"
SPEC_SHOWN = f"{SPEC_DIR}/"  # the spec's name in messages
ROOT_DOCS = (Path("README.md"), Path("CLAUDE.md"))


def doc_files(root, spec=True):
    """The Markdown documents the document tools read (`tools/docs.py`), relative to the root and
    sorted: the files under DOC_DIRS (the decisions, the issues, the tasks, the spec, the rules and the
    design notes) and the root's README.md and CLAUDE.md (nothing else: not `history/`). The spec
    (`spec/`) only with `spec`."""
    root = Path(root)
    found = [p.relative_to(root) for d in DOC_DIRS for p in (root / d).rglob("*.md") if p.is_file()]
    found += [p for p in ROOT_DOCS if (root / p).is_file()]
    return sorted({p for p in found if spec or not is_spec_doc(p)})


def is_spec_doc(rel):
    """`rel` (relative to the root) is the spec: a file of `spec/` (the spec of the tools too)."""
    return Path(rel).parts[:1] == (SPEC_DIR,)



# ---------------------------------------------------------------- the IDs and their paths (X-2 DT-1, DS-1)


@dataclass(frozen=True)
class Kind:
    name: str
    pattern: str  # the spelling of an ID: the file name and the bare ID in the text
    dir: str = None  # the directory of its files; None: no file to check (the history, PH2)
    draft: bool = False  # has drafts `S-xxx.draft.md`
    bare: bool = True  # looked for as a bare ID in the text


PHASE2 = "PH2"  # the second phase: in `tasks` and `before`, and an `until` of tests/pending.toml (K-13 rule 3)
KINDS = (
    Kind("S", r"S-\d+", "decisions/S", True),
    Kind("D", r"D-\d+", "decisions/D"),
    Kind("K", r"K-\d+", "decisions/K"),
    Kind("Q", r"Q-\d+", "decisions/Q"),
    Kind("A", r"A-\d+", "decisions/A"),
    Kind("R", r"R-\d+", "issues/R"),
    Kind("RF", r"RF-\d+", "issues/RF"),
    Kind("X", r"X-\d+", "issues/X"),
    Kind("W", r"W\d+-\d+", "tasks/W"),
    # the kinds whose files are in the history: their IDs are not checked (X-2 DF-6 `refs`)
    Kind("C", r"C-\d+"),
    Kind("T", r"T\d+-\d+"),
    Kind(PHASE2, re.escape(PHASE2), bare=False),  # the second phase in `tasks` (X-2 DF-4); not an ID in the text
)
KIND = {k.name: k for k in KINDS}
# A bare ID: not after a letter, a digit, `_` or `-`, not before a digit (no `F-8` in `UTF-8`).
ID_RE = re.compile(
    r"(?<![A-Za-z0-9_-])(?:"
    + "|".join(k.pattern for k in sorted(KINDS, key=lambda k: -len(k.name)) if k.bare)
    + r")(?![0-9])"
)
SECTION_RE = re.compile(r"(?:(?P<tools>tools\.md) )?§(?P<num>\d+(?:\.\d+)*)")


def id_form(*names):
    """The spelling of an ID of one of the kinds `names` (`id_form("S", "R")`), to match the whole of a
    string (`fullmatch`): the patterns of KINDS, not written again (D-15)."""
    return re.compile("|".join(f"(?:{KIND[n].pattern})" for n in names))


def kind_of(id_):
    """The Kind whose spelling is the whole of `id_`, or None."""
    return next((k for k in KINDS if re.fullmatch(k.pattern, id_)), None)


def path_of(id_, draft=False):
    """`S-537` -> `decisions/S/S-537.md` (`.draft.md` with `draft`)."""
    kind = kind_of(id_)
    if kind is None or kind.dir is None or (draft and not kind.draft):
        raise RepoError(f"{id_}: no {'draft' if draft else 'file'} of the new layout for it")
    return Path(kind.dir) / f"{id_}{'.draft' if draft else ''}.md"


def section_path(root, sec):
    """`§6.1` -> `spec/06-<name>.md` (the chapter), `§0` and `§1` -> `spec/README.md`, `§0.5.1` -> its
    part (`SPEC_PARTS`), as `spec_file` says; `tools.md §3.2` -> `spec/tools.md`. Only in the new layout."""
    m = SECTION_RE.fullmatch(sec)
    if m is None:
        raise RepoError(f"{sec}: not a section (`§6.1` or `tools.md §3.2`)")
    if not (Path(root) / SPEC_README).is_file():
        raise RepoError(f"{sec}: the spec is not split into {SPEC_DIR}/ (no {SPEC_README})")
    if m.group("tools"):
        return SPEC_TOOLS
    path = spec_file(m.group("num"), chapters(root))
    if path is None:
        raise RepoError(f"{sec}: no chapter file {SPEC_DIR}/{int(m.group('num').split('.')[0]):02d}-*.md")
    return path


# ---------------------------------------------------------------- the files that are not kinds of IDs

SPEC_README = Path(SPEC_DIR) / "README.md"
SPEC_TOOLS = Path(SPEC_DIR) / "tools.md"
DIAG_CODES = Path("tasks") / "diag-codes.md"
# The table of the stages (X-2 U6): its first column `段` lists the stages in their order; the last ends
# the first phase. A stage is `W4`, `M5`: one capital and digits (`PH2`, the second phase, is none).
STAGES = Path("tasks") / "stages.md"
STAGES_HEAD = "段"
STAGE_NAME = re.compile(r"[A-Z]\d+")
FOREIGN_FORMS = Path(SPEC_DIR) / "foreign-forms.toml"


class Layout:
    """The documents read once (`text`) and the stages (`stages`). Each kind of ID is read from its
    directory (`KINDS`, X-2 DT-7) by `tools/docs.py`'s `Index`."""

    def __init__(self, root):
        self.root, self._texts, self._stages = Path(root), {}, None

    def text(self, rel):
        if rel not in self._texts:
            self._texts[rel] = read(self.root, rel)
        return self._texts[rel]

    def stages(self):
        """The stages in their order: the first column of the table of STAGES (the one place, D-15).
        RepoError when the file, its table or a stage is not there or not of the form."""
        if self._stages is None:
            lines = self.text(STAGES).split("\n")
            at = [i for i, line in enumerate(lines) if _first_cell(line) == STAGES_HEAD]
            if len(at) != 1:
                raise RepoError(f"{STAGES}: expected one table whose first column is `{STAGES_HEAD}`, found {len(at)}")
            if at[0] + 1 == len(lines) or not re.fullmatch(r"\|(?:\s*:?-+:?\s*\|)+", lines[at[0] + 1].strip()):
                raise RepoError(f"{STAGES}:{at[0] + 2}: no delimiter row under the header of the stages")
            names, i = [], at[0] + 2
            while i < len(lines) and lines[i].startswith("|"):
                cell = _first_cell(lines[i])
                if not STAGE_NAME.fullmatch(cell) or cell in names:
                    why = "given twice" if cell in names else "not a stage (`W4`, `M5`)"
                    raise RepoError(f"{STAGES}:{i + 1}: `{cell}` is {why}")
                names.append(cell)
                i += 1
            if not names:
                raise RepoError(f"{STAGES}:{at[0] + 1}: the table of the stages has no row")
            self._stages = tuple(names)
        return self._stages


def _first_cell(line):
    """The first cell of a table row, stripped ("" for another line)."""
    return table_cells(line)[0] if line.startswith("|") else ""


# ---------------------------------------------------------------- the spec as one text (X-2 DS-4, DF-2)

# The heading of `spec/README.md` that starts its list of the chapters: what is before it is the head
# of the spec (its H1 to the end of §1); it and what follows are not part of the spec's text.
SPEC_INDEX_HEAD = "## 章の一覧"
CHAPTER_FILE = re.compile(r"(\d{2})-[a-z0-9-]+\.md")
# The sections of the spec in a file of their own with their subsections, not in the file of their
# chapter: {section: file}. Each is joined into the text of its chapter's file before the first numbered
# heading after it there (`spec_doc`); a file that is not there joins nothing.
SPEC_PARTS = {"0.5": Path(SPEC_DIR) / "00-principles.md"}


def spec_file(num, found):
    """The file of the spec that holds the section `num` ("6.1"), the one place that says it: its part
    (SPEC_PARTS), else `spec/README.md` for §0 and §1, else its chapter in `found` (`chapters`) or None."""
    part = next((rel for sec, rel in SPEC_PARTS.items() if num == sec or num.startswith(sec + ".")), None)
    n = int(num.split(".")[0])
    return part or (SPEC_README if n <= 1 else found.get(n))


@dataclass(frozen=True)
class Joined:
    """A text joined from files: `parts` are (file, the line of the text where it starts[, the line of
    the file where the part starts; 1 when left out]). A file cut by a part (`SPEC_PARTS`) is two parts."""

    text: str
    parts: tuple

    @property
    def shown(self):
        """Its name in messages: its file when it is of one, else the spec's (`spec/`, joined from the chapters)."""
        return Path(self.parts[0][0]).as_posix() if len(self.parts) == 1 else SPEC_SHOWN

    def locate(self, line):
        """(file, line in it) of a line (from 1) of the text."""
        rel, start, *first = next(p for p in reversed(self.parts) if p[1] <= line)
        return rel, line - start + (first[0] if first else 1)

    def where(self, line):
        rel, n = self.locate(line)
        return f"{Path(rel).as_posix()}:{n}"


def chapters(root):
    """{number: path} of the chapter files of `spec/`. Raises RepoError on another file or a number
    given twice (a file put in the wrong place is never skipped)."""
    out = {}
    for p in sorted((Path(root) / SPEC_DIR).glob("*.md")):
        if p.name in (SPEC_README.name, SPEC_TOOLS.name) or Path(SPEC_DIR) / p.name in SPEC_PARTS.values():
            continue
        m = CHAPTER_FILE.fullmatch(p.name)
        if m is None:
            raise RepoError(f"{SPEC_DIR}/{p.name}: not a chapter file (`NN-<name>.md`), the README or tools.md")
        n = int(m.group(1))
        if n in out:
            raise RepoError(f"{SPEC_DIR}/{p.name}: the chapter {n} is also {out[n].as_posix()}")
        out[n] = Path(SPEC_DIR) / p.name
    return out


def spec_doc(root):
    """The spec as one text: the head of `spec/README.md` (before SPEC_INDEX_HEAD) and the chapters in
    the order of their numbers, joined as they are (each chapter keeps the `---` that ends it), with
    the parts (`SPEC_PARTS`) put into their chapters. Every numbered heading must be in the file
    `spec_file` says (a section in two files is an error)."""
    lines = read_exact(root, SPEC_README).split("\n")
    at = [i for i, line in enumerate(lines) if line == SPEC_INDEX_HEAD]
    if len(at) != 1:
        raise RepoError(f"{SPEC_README}: expected one line `{SPEC_INDEX_HEAD}`, found {len(at)}")
    pieces = [(SPEC_README, "\n".join(lines[: at[0]]) + "\n", 1)]  # (file, text, its first line in the file)
    found = chapters(root)
    if not found:
        raise RepoError(f"{SPEC_DIR}/: no chapter file (`NN-<name>.md`)")
    for n, rel in sorted(found.items()):
        text = read_exact(root, rel)
        if not text.startswith(f"## {n}. "):
            raise RepoError(f"{rel.as_posix()}:1: a chapter file starts with its heading `## {n}. `")
        pieces.append((rel, text, 1))
    for sec, rel in SPEC_PARTS.items():
        if (Path(root) / rel).is_file():
            pieces = _with_part(pieces, sec, rel, read_exact(root, rel), found)
    parts, line = [], 1
    for i, (rel, text, first) in enumerate(pieces):
        if i and not pieces[i - 1][1].endswith("\n"):
            raise RepoError(f"{Path(pieces[i - 1][0]).as_posix()}: does not end with a line end")
        parts.append((rel, line, first))
        line += text.count("\n")
    doc = Joined("".join(p[1] for p in pieces), tuple(parts))
    for line, sec in spec_blocks.heading_lines(doc.text):
        want, (rel, n) = spec_file(sec, found), doc.locate(line)
        if want != Path(rel):
            its = want.as_posix() if want else "(no file of its chapter)"
            raise RepoError(f"{Path(rel).as_posix()}:{n}: the heading of §{sec} is not in its file {its}")
    return doc


def _with_part(pieces, sec, rel, text, found):
    """`pieces` with the part `sec` (its file `rel`, its text) put into the piece of its chapter's file,
    before the first numbered heading after `sec` there (at its end when there is none)."""
    if spec_blocks.heading_lines(text)[:1] != [(1, sec)]:
        raise RepoError(f"{rel.as_posix()}:1: the file of §{sec} starts with its heading")
    key, host = tuple(map(int, sec.split("."))), spec_file(sec.split(".")[0], found)
    i = next((i for i, p in enumerate(pieces) if p[0] == host), None)
    if i is None:
        raise RepoError(f"{rel.as_posix()}: no file of the chapter of §{sec}")
    h_rel, h_text, h_first = pieces[i]
    at = next((ln for ln, s in spec_blocks.heading_lines(h_text) if tuple(map(int, s.split("."))) > key), None)
    if at is None:
        before, after = h_text, ""
    else:
        h_lines = h_text.split("\n")
        before, after = "".join(x + "\n" for x in h_lines[: at - 1]), "\n".join(h_lines[at - 1 :])
    rest = [(h_rel, after, h_first + before.count("\n"))] if after else []
    return [*pieces[:i], (h_rel, before, h_first), (rel, text, 1), *rest, *pieces[i + 1 :]]


def spec_text(root):
    return spec_doc(root).text


def tools_doc(root):
    """The spec of the tools: `spec/tools.md`."""
    return Joined(read_exact(root, SPEC_TOOLS), ((SPEC_TOOLS, 1),))


def tools_text(root):
    return tools_doc(root).text


# ---------------------------------------------------------------- build outputs

BUILD_MANIFESTS = ("onsa.toml", "Cargo.toml")


def is_build_output(root, rel):
    """`rel` (relative to the root, `/`-separated) is inside a build output
    directory: `target/` at the root, or a `target/` next to an `onsa.toml` or a
    `Cargo.toml` (spec §15.1; cargo). A `target` anywhere else is an ordinary name."""
    parts = [p for p in rel.split("/") if p]
    for i, p in enumerate(parts):
        if p == "target":
            parent = Path(root).joinpath(*parts[:i])
            if i == 0 or any((parent / m).is_file() for m in BUILD_MANIFESTS):
                return True
    return False


# ---------------------------------------------------------------- git trees

GIT_TIMEOUT = 60


def git_dirs(root):
    """(git directory, common git directory), absolute, when `root` is the top of a git work
    tree; None otherwise (not git, git missing, a directory inside a tree: the self-tests'
    made-up roots)."""
    try:
        r = subprocess.run(
            ["git", "rev-parse", "--path-format=absolute", "--show-toplevel", "--git-dir", "--git-common-dir"],
            cwd=root, capture_output=True, text=True, timeout=GIT_TIMEOUT,
        )  # fmt: skip
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = r.stdout.splitlines()
    if r.returncode != 0 or len(lines) != 3 or Path(lines[0]).resolve() != Path(root).resolve():
        return None
    return Path(lines[1]), Path(lines[2])


def main_tree(root):
    """The main tree of the repository of `root` (the parent of the common git directory), or None."""
    dirs = git_dirs(root)
    return dirs[1].parent if dirs else None


def tree_hash(root, paths=()):
    """What `root` holds now, untracked files too (`add -A` in an index of its own: the real index is
    not touched; X-1 U3, U4; one place, D-15). With no `paths`, the git tree of the whole; with
    `paths`, a hash of their entries alone (`ls-files -s`): the other paths of HEAD (a commit of the
    documents) do not change it. A path that is in neither HEAD nor the tree adds nothing. RepoError
    when git fails."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    with tempfile.TemporaryDirectory() as d:
        env["GIT_INDEX_FILE"] = os.path.join(d, "index")
        adds = [["add", "-A", "--", p] for p in paths] if paths else [["add", "-A"]]
        out = ""
        last = ["ls-files", "-s", "-z", "--", *paths] if paths else ["write-tree"]
        for args in (["read-tree", "HEAD"], *adds, last):
            try:
                r = subprocess.run(["git", *args], cwd=root, env=env, capture_output=True, text=True,
                                   timeout=GIT_TIMEOUT)  # fmt: skip
            except (OSError, subprocess.TimeoutExpired) as e:
                raise RepoError(f"git {args[0]}: {e}") from None
            if r.returncode != 0 and not (args[0] == "add" and "did not match any files" in r.stderr):
                raise RepoError(f"git {' '.join(args)}: {r.stderr.strip() or f'exit {r.returncode}'}")
            out = r.stdout if paths else r.stdout.strip()
    return hashlib.sha256(out.encode("utf-8", "surrogateescape")).hexdigest()[:40] if paths else out


def tree_kind(root):
    """`"main"` (the main tree), `"worktree"` (a git worktree of it), or None (not the top of a git tree)."""
    dirs = git_dirs(root)
    if dirs is None:
        return None
    return "main" if dirs[0].resolve() == dirs[1].resolve() else "worktree"


# ---------------------------------------------------------------- the subcommands of a tool (X9-7)

# The roles of the help: the name in the rules -> its agent definition (`.claude/agents/<name>.md`; None: the
# parent, the main session). The help shows them in this order.
ROLES = {"parent": None, "t": "onsa-test", "i": "onsa-impl", "b": "onsa-break", "advisor": "onsa-advisor",
         "gap": "onsa-gap", "docs": "onsa-docs"}  # fmt: skip


class Command(NamedTuple):
    """A subcommand of a tool: its argparse arguments and its run, then its help in Japanese (X9-7): the roles
    that use it in their work (ROLES), its purpose in one line, when to use it, and an example (`<tool> <name> …`)."""

    add_arguments: Callable
    run: Callable
    roles: tuple
    purpose: str
    when: str
    example: str


def parse_command(prog, description, commands, argv=None, common=lambda p: None):
    """The arguments of `prog <name> …` for `commands` ({name: Command}) and `help`; `args.run_` is the run.
    `common(p)` adds what every subcommand but `help` takes. argparse's errors exit 2 (an unknown role or
    command of `help` too)."""
    return command_parsers(prog, description, commands, common)[0].parse_args(argv)


def command_parsers(prog, description, commands, common=lambda p: None):
    """(the parser of `prog`, {name: the parser of the subcommand}, `help` too): `parse_command`'s, and the
    arguments `docs.py check`'s `tools` reads (X9-9)."""
    ap = argparse.ArgumentParser(prog=prog, description=description)
    sub = ap.add_subparsers(dest="cmd", required=True)
    parsers = {}
    for name, c in commands.items():
        parsers[name] = p = sub.add_parser(name, help=c.purpose, description=c.purpose)
        common(p)
        c.add_arguments(p)
        p.set_defaults(run_=c.run)
    parsers["help"] = h = sub.add_parser("help", help="命令の目的・時機・役割・例を出す")
    h.add_argument("--role", choices=ROLES, help="この役割が使う命令だけを、時機と例とともに出す")
    h.add_argument("command", nargs="?", choices=commands, help="この命令の全てと引数の説明を出す")
    h.set_defaults(run_=lambda a: print(help_text(prog, commands, parsers, a.role, a.command), end="") or 0)
    return ap, parsers


def help_text(prog, commands, parsers, role=None, name=None):
    """`help`: the names and the purposes; with `role`, its commands with when and an example; with `name`, all
    of the command and its argparse help (with `role` too, a line when the role does not use it)."""
    width = max(map(len, commands))
    if name:
        c = commands[name]
        out = [f"{name}: {c.purpose}", f"  時機: {c.when}", f"  役割: {' '.join(c.roles)}", f"  例:   {c.example}"]
        if role and role not in c.roles:
            out.append(f"  （役割 {role} はこの命令を使わない）")
        return "\n".join(out) + "\n\n" + parsers[name].format_help()
    if role:
        out = [f"{n:<{width}}  {c.purpose}\n  時機: {c.when}\n  例:   {c.example}\n"
               for n, c in commands.items() if role in c.roles]  # fmt: skip
        return "".join(out) or f"（役割 {role} が使う命令は無い）\n"
    roles = "、".join(f"{r}（{d or '親'}）" for r, d in ROLES.items())
    return "".join(f"{n:<{width}}  {c.purpose}\n" for n, c in commands.items()) + (
        f"\n`{prog} help --role <役割>` はその役割の命令と時機と例を、`{prog} help <命令>` はその命令の全てを出す。\n"
        f"役割: {roles}\n")
