#!/usr/bin/env python3
"""The tool of the documents (X-2 DT-0): one tool, one subcommand per job.

    python3 -B tools/docs.py fmt [PATH...] [--check | --list] [--spec] [--root DIR]
    python3 -B tools/docs.py swaps [--root DIR]
    python3 -B tools/docs.py check [--root DIR]
    python3 -B tools/docs.py due [--stage-end STAGE] [--root DIR]
    python3 -B tools/docs.py path ID|§... [--abs] | back ID [--history] | refs ID|PATH
                             | graph ID|STAGE [--back] [--depth N (1 to 5)] [--typed]
    python3 -B tools/docs.py show ID [--relations] | list KIND [--status S] [--stage W4] [--group N]
                             [--before W4-02|W4] [--no-fix] [--waiting] [--count] | changes [--since DATE]
                             [--stage W3] [--section §6] | ticket W UNIT/ROLE [--out FILE]
    python3 -B tools/docs.py set ID KEY=VALUE... | note ID LABEL TEXT [--by WHO] | new KIND [--title T]
                             [--stage W4] [KEY=VALUE...] | draft S... --group N

Exit: 0 nothing found, 1 found, 2 an error of the tool (a file it cannot read, no document, a
broken round trip of `fmt`; argparse's usage errors too). The documents are `repo.doc_files`.
The commands of the IDs (X-2 DT-2, DT-3, DT-6): 0 done, 1 not found or refused (nothing is
written), 2 an error of the tool or of the use (not an ID, a kind not in the new layout, `new` in a
git worktree, a write that fails). Their lines are `\\t`-separated: `ID status place title` (`refs`),
`label ID status title sections` (the relations of `show`), `ID status fields title` (`list`), `ID
decided sections title` (`changes`), `depth node type from status title` (`graph`; the start at the
depth 0 with `-` for the type and from).

- `path`, `back`, `refs` read the files of the IDs (`Ids`; a `§` is `file:line` of its heading).
  `graph` shows the relations of the decisions as a graph made on the spot (`cmd_graph`).
  `show`, `list`, `changes`, `ticket` and the writes need the directory of the kind. The writes check the swap files first, write through `write_atomic`, and
  `set`, `new` refuse a text whose head fields would break (a) or (b) of the file or (c) of it
  and its partners (`check_write`).

- `fmt` (DT-4): breaks each line longer than LONG after a `。` at the depth 0 of the brackets
  （）()「」『』【】 and outside the code spans and the bold, packing the line to WIDTH characters
  after its indentation; the lines go on at the indentation of the item (`> ` in a quote). It never
  touches the head fields (`+++`), the code blocks, the HTML comments, the table rows, the headings,
  the line of the retired codes (`欠番:`), and never breaks where the next line would start like a
  block. It only breaks (never joins), so a second run changes nothing. Every broken line must give
  the line back when the breaks are taken out, or nothing is written (exit 2). `--check` writes
  nothing and exits 1 when a line would change; `--list` (the gate's `docs-fmt`, an `info` item)
  shows the same and exits 0. The spec is left out unless `--spec` (DS-4). A file with a vim swap
  file is not written (exit 1).
- `swaps`: the vim swap files (`.*.sw?`) of the tree, out of `.git`, the build outputs and
  `.claude/worktrees/`.
- `due` (X-9 U1, the gate's `docs-due`): the documents of DUE_DOCS changed from the last commit with a
  `Docs-Checked:` trailer (the parent's mark of a check of onsa-docs taken in) to the working tree, untracked
  files too: none exits 0; some, or no mark, exit `gate_steps.PARENT` (3), and 1 with `--stage-end`.
- `check` (DT-5, the gate's `docs`): the checks of CHECKS on one reading of the documents (`Tree`),
  `path:line: what` under a heading per check: (d) `tables`, and on the files of the IDs of the new
  layout (`Index`; `history/` and `tests/pending.toml` are not read) (a) `heads` (the field table of
  the directory's README, the head fields against it, the heading), (b) `refs` (the IDs and the `§`
  are there), (c) `relations` (the keys named in `check_relations`, and a direction in `RESTS_ON` for
  each ID field of the field tables), and (e) `links` (the relative
  links of the READMEs). To add a check, add `(name, fn(tree) -> Findings)` to CHECKS; to add a
  subcommand, add `name: repo.Command(add_arguments, run, roles, purpose, when, example)` to COMMANDS
  (its help, X9-7; `docs.py help`).

The head fields (DF-1) are read by `read_head` and written in the normal form by `head_update` /
`write_head` (U3's `set`); the field table of a directory is `field_table`.
"""
import fnmatch
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from collections import deque
from dataclasses import dataclass
from datetime import date
from pathlib import Path

import gate_steps
import repo
import spec_blocks

ROOT = repo.ROOT


class DocsError(repo.RepoError):
    """An error of the tool: exit 2 (a RepoError, so the readers of `pending.load_docs` catch it)."""


def read_doc(root, rel):
    """The text of a document, its line ends as they are."""
    try:
        return (Path(root) / rel).read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise DocsError(f"{rel}: {e}") from e


# ---------------------------------------------------------------- the kinds of the lines

HEAD, CODE, COMMENT, TEXT = "head", "code", "comment", "text"
HEAD_LINE = "+++"
FENCE = re.compile(r"\s*(`{3,}|~{3,})")


def line_kinds(lines):
    """(the kind of each line, the index of a code fence left open or None). The head fields run
    from a first line `+++` to the next line `+++` (to the end when it does not close); a code
    block from a fence to a line of the same character at least as long; an HTML comment from a
    line with `<!--` to the line with `-->`."""
    kinds, i = [], 0
    if lines and lines[0] == HEAD_LINE:
        end = next((j for j in range(1, len(lines)) if lines[j] == HEAD_LINE), len(lines) - 1)
        kinds, i = [HEAD] * (end + 1), end + 1
    fence = start = None
    comment = False
    for j, line in enumerate(lines[i:], i):
        m = None if fence or comment else FENCE.match(line)
        if fence:
            kinds.append(CODE)
            s = line.strip()
            if s.startswith(fence) and set(s) == {fence[0]}:
                fence = None
        elif comment:
            kinds.append(COMMENT)
            comment = "-->" not in line
        elif m:
            kinds.append(CODE)
            fence, start = m.group(1), j
        elif "<!--" in line:
            kinds.append(COMMENT)
            comment = "-->" not in line[line.rfind("<!--") :]
        else:
            kinds.append(TEXT)
    return kinds, (start if fence else None)


# The code spans and the cells of a row are read in `repo` (its readers of the tables use them too, D-15).
code_spans, _plain, table_cells = repo.code_spans, repo.plain, repo.table_cells


# ---------------------------------------------------------------- fmt

LONG = 250  # the lines longer than this are broken
WIDTH = 200  # the characters of a line after its indentation
OPEN = "（(「『【"
CLOSE = "）)」』】"
KEEP = ("|", "#", repo.RETIRED_HEAD)  # table rows, headings, the retired codes of tasks/diag-codes.md
MARKER = re.compile(r"(\s*)((?:[-*+]|\d+\.)\s+|>\s?)?")
# A line must not start with these: a block (an item, a quote, a table, a heading, a fence, HTML),
# an underline or a rule, or a space that would change the indentation.
NO_START = re.compile(r"\s|[-*+>|#`~<=_]|\d+[.)]")


def break_points(body):
    """The indexes just after each `。` at the depth 0 of the brackets, outside the code spans and
    the bold."""
    out, depth, bold = [], 0, False
    for i in _plain(body):
        ch = body[i]
        if ch == "*" and body.startswith("**", i) and (i == 0 or body[i - 1] != "*"):
            bold = not bold
        elif bold:
            continue
        elif ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth = max(0, depth - 1)
        elif ch == "。" and depth == 0:
            out.append(i + 1)
    return out


def wrap(line):
    """(the lines of `line`, the head of the lines after the first)."""
    m = MARKER.match(line)
    lead, marker = m.group(1), m.group(2) or ""
    body = line[m.end() :]
    cont = lead + ("> " if marker.startswith(">") else " " * len(marker))
    cuts = [p for p in break_points(body) if p < len(body) and not NO_START.match(body, p)]
    pieces = [body[a:b] for a, b in zip([0, *cuts], [*cuts, len(body)])]
    lines, cur = [], ""
    for s in pieces:
        if cur and len(cur) + len(s) > WIDTH:
            lines.append(cur)
            cur = s
        else:
            cur += s
    lines.append(cur)
    return [m.group(0) + lines[0]] + [cont + x for x in lines[1:]], cont


def fmt_text(text):
    """(the text with its long lines broken, the numbers of the lines broken, (number, length) of
    the long lines left). Raises DocsError when a broken line does not give the line back."""
    lines = text.split("\n")
    out, wrapped, left = [], [], []
    for no, (line, kind) in enumerate(zip(lines, line_kinds(lines)[0]), 1):
        if kind != TEXT or len(line) <= LONG or line.lstrip().startswith(KEEP):
            out.append(line)
            continue
        new, cont = wrap(line)
        back = new[0] + "".join(x[len(cont) :] for x in new[1:])
        if back != line or not all(x.startswith(cont) for x in new[1:]):
            raise DocsError(f"line {no}: the broken line does not give the line back")
        if len(new) > 1:
            wrapped.append(no)
        if max(map(len, new)) > LONG:
            left.append((no, max(map(len, new))))
        out += new
    return "\n".join(out), wrapped, left


def write_atomic(path, text):
    """Write through a temporary file in the same directory, so a stop never leaves half a file."""
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(text.encode("utf-8"))
        shutil.copymode(path, tmp)
        os.replace(tmp, path)
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def _targets(args):
    root = Path(args.root)
    if not args.paths:
        rels = repo.doc_files(root, spec=args.spec)
        if not rels:
            raise DocsError(f"no document found under {root}")
        return rels
    rels = []
    for p in map(Path, args.paths):
        rel = p.resolve()
        if rel.is_relative_to(root.resolve()):
            rel = rel.relative_to(root.resolve())
        if repo.is_spec_doc(rel) and not args.spec:
            print(f"{rel.as_posix()}: skipped, the spec (pass --spec)")
        else:
            rels.append(rel)
    return rels


def cmd_fmt(args):
    root, mode = Path(args.root), ("check" if args.check else "list" if args.list else "write")
    done = []  # all computed before anything is written: a broken round trip writes nothing
    for rel in _targets(args):
        text = read_doc(root, rel)
        if "\r" in text:
            print(f"{rel.as_posix()}: skipped, it has CR line ends")
            continue
        try:
            new, wrapped, left = fmt_text(text)
        except DocsError as e:
            raise DocsError(f"{rel.as_posix()}: {e}; nothing is written") from e
        done.append((rel, new, wrapped, left))
    skipped, lines, files = 0, 0, 0
    verb = "wrapped" if mode == "write" else "would be wrapped"
    for rel, new, wrapped, left in sorted(done, key=lambda d: -len(d[2])):
        if not wrapped:
            continue
        if mode == "write":
            swaps = swap_files_of(root / rel)
            if swaps:
                print(f"{rel.as_posix()}: skipped, the swap file {swaps[0].name} (open in vim?)")
                skipped += 1
                continue
            write_atomic(root / rel, new)
        print(f"{rel.as_posix()}: {len(wrapped)} line(s) {verb} (lines {', '.join(map(str, wrapped))})")
        lines, files = lines + len(wrapped), files + 1
    for rel, _, _, left in done:
        for no, n in left:
            print(f"{rel.as_posix()}:{no}: {n} characters left on one line (no place to break)")
    print(f"docs fmt: {lines} line(s) in {files} file(s) {verb}; "
          f"{sum(len(d[3]) for d in done)} long line(s) have no place to break")  # fmt: skip
    if mode == "check":
        return 1 if lines else 0
    return 1 if skipped else 0


def fmt_args(p):
    p.add_argument("paths", nargs="*", help="the documents (default: repo.doc_files)")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--check", action="store_true", help="write nothing; exit 1 when a line would change")
    g.add_argument("--list", action="store_true", help="write nothing; exit 0 (the gate's info item)")
    p.add_argument("--spec", action="store_true", help="the spec too (it is left out by default, DS-4)")


# ---------------------------------------------------------------- swaps

SWAP = ".*.sw?"
WORKTREES = ".claude/worktrees"


def swap_files_of(path):
    """The vim swap files of one file (`.<name>.sw?` next to it)."""
    path = Path(path)
    try:
        names = os.listdir(path.parent)
    except OSError as e:
        raise DocsError(f"{path.parent}: {e}") from e
    return sorted(path.parent / n for n in names if len(n) == len(path.name) + 5 and n[:-1] == f".{path.name}.sw")


def swap_files(root):
    """The vim swap files of the tree, relative to the root: not in `.git`, the build outputs and
    the git worktrees of the agents (other trees; their swap files never meet this tree's edits)."""
    root, found = Path(root), []

    def fail(e):
        raise DocsError(f"{e.filename}: {e.strerror}")

    for dirpath, dirs, files in os.walk(root, onerror=fail):
        rel = Path(dirpath).relative_to(root)
        dirs[:] = sorted(
            d for d in dirs
            if d != ".git" and (rel / d).as_posix() != WORKTREES and not repo.is_build_output(root, (rel / d).as_posix())
        )  # fmt: skip
        found += [rel / f for f in files if fnmatch.fnmatchcase(f, SWAP)]
    return sorted(found)


def cmd_swaps(args):
    found = swap_files(args.root)
    for p in found:
        print(p.as_posix())
    print(f"docs swaps: {len(found)} swap file(s)")
    return 1 if found else 0


# ---------------------------------------------------------------- due (X-9 U1)

DOCS_CHECKED = "Docs-Checked"  # the trailer of the commit that takes in a check of onsa-docs
# The documents a change of which calls for a check of onsa-docs (git pathspecs): the rules, the spec, the
# definitions of the agents, the root's README.md and CLAUDE.md, and the README.md (the field tables, the
# forms) of the other directories of the documents and of their kinds; not `history/`.
DUE_WHOLE = ("rules", repo.SPEC_DIR, ".claude/agents")
DUE_DOCS = tuple(f"{d}/" for d in DUE_WHOLE) + tuple(p.as_posix() for p in repo.ROOT_DOCS) + tuple(
    f":(glob){d}/{sub}README.md" for d in repo.DOC_DIRS if d not in DUE_WHOLE for sub in ("", "*/")
)


def git_lines(root, *args):
    """The lines git prints in `root`; a DocsError when git fails."""
    try:
        r = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, timeout=repo.GIT_TIMEOUT)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise DocsError(f"git {args[0]}: {e}") from e
    if r.returncode != 0:
        raise DocsError(f"git {args[0]}: {r.stderr.strip() or f'exit {r.returncode}'}")
    return r.stdout.splitlines()


def last_docs_check(root):
    """(commit, trailer value) of the first commit from HEAD with a `Docs-Checked:` trailer, or None."""
    form = f"--format=%H%x09%(trailers:key={DOCS_CHECKED},valueonly,separator=%x3B%x20)"
    for line in git_lines(root, "log", form, "HEAD"):
        commit, _, value = line.partition("\t")
        if value.strip():
            return commit, value.strip()
    return None


def due_changes(root, commit):
    """{path: how} of the documents of DUE_DOCS changed from `commit` to the working tree, untracked files too."""
    changed = {p: "changed" for p in git_lines(root, "diff", "--name-only", "--no-renames", commit, "--", *DUE_DOCS)}
    new = git_lines(root, "ls-files", "--others", "--exclude-standard", "--", *DUE_DOCS)
    changed |= {p: "untracked" for p in new if not fnmatch.fnmatchcase(Path(p).name, SWAP)}  # not a vim swap file
    return dict(sorted(changed.items()))


def cmd_due(args):
    if repo.git_dirs(args.root) is None:
        raise DocsError(f"{args.root} is not the top of a git tree")
    mark, lines = last_docs_check(args.root), []
    if mark is None:
        lines.append(f"no commit from HEAD has a `{DOCS_CHECKED}:` trailer")
    else:
        lines = [f"{p}: {how} after the docs check {mark[0][:7]}" for p, how in due_changes(args.root, mark[0]).items()]
        print(f"docs due: the last docs check is {mark[0][:7]} ({DOCS_CHECKED}: {mark[1]})")
    prefix = "" if args.stage_end else "parent: "
    for line in lines:
        print(prefix + line)
    if not lines:
        print("docs due: no document changed after the docs check")
        return 0
    print(f"docs due: run the check of onsa-docs and put `{DOCS_CHECKED}:` in the commit that takes it in"
          + (f" (fails at the stage end {args.stage_end})" if args.stage_end else ""))  # fmt: skip
    return 1 if args.stage_end else gate_steps.PARENT


# ---------------------------------------------------------------- check


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    message: str

    def __str__(self):
        line = "" if self.line is None else f":{self.line}"  # None: of a directory
        return f"{Path(self.path).as_posix()}{line}: {self.message}"


class Tree:
    """One reading of the documents, shared by the checks: each file, its lines, their kinds and its
    head fields are read once; `index` (the files of the IDs) is made once."""

    def __init__(self, root, files):
        self.root, self.files = Path(root), list(files)
        self._lines, self._kinds, self._heads, self._index = {}, {}, {}, None
        self.notes = []  # lines printed before the summary of `check`

    def lines(self, rel):
        if rel not in self._lines:
            self._lines[rel] = read_doc(self.root, rel).split("\n")
        return self._lines[rel]

    def head(self, rel):
        """The head fields of a file (`read_head`)."""
        if rel not in self._heads:
            self._heads[rel] = read_head("\n".join(self.lines(rel)))
        return self._heads[rel]

    @property
    def index(self):
        if self._index is None:
            self._index = Index(self)
        return self._index

    def kinds(self, rel):
        """(the kind of each line, the index of a code fence left open or None): `line_kinds`."""
        if rel not in self._kinds:
            self._kinds[rel] = line_kinds(self.lines(rel))
        return self._kinds[rel]


DELIMITER = re.compile(r"\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?")


def cell_count(row):
    """The cells of a table row: `\\|` and a `|` in a code span do not divide."""
    return len(table_cells(row))


def check_tables(tree):
    """(d) The tables: every row has the cells of the header; rows with no header and delimiter
    row before them (a blank line inside a table); a code fence left open (it hides the rest)."""
    for rel in tree.files:
        lines, (kinds, open_fence) = tree.lines(rel), tree.kinds(rel)
        if open_fence is not None:
            yield Finding(rel, open_fence + 1, "the code fence is not closed")
        rows = [kinds[i] == TEXT and lines[i].lstrip().startswith("|") for i in range(len(lines))]
        i = 0
        while i < len(lines):
            if not rows[i]:
                i += 1
                continue
            j = i
            while j < len(lines) and rows[j]:
                j += 1
            if j - i < 2 or not DELIMITER.fullmatch(lines[i + 1].strip()):
                yield Finding(rel, i + 1, "table rows with no header and delimiter row before them")
            else:
                head = cell_count(lines[i])
                for k in range(i + 1, j):
                    n = cell_count(lines[k])
                    if n != head:
                        what = "the delimiter row" if k == i + 1 else "the row"
                        yield Finding(rel, k + 1, f"{what} has {n} cells, the header {head}")
            i = j




# ---------------------------------------------------------------- the head fields (X-2 DF-1, DT-3)

NO_HEAD = "no head fields (a line `+++` first)"
NOT_CLOSED = "the head fields are not closed (no second line `+++`)"
TOML_AT = re.compile(r"\s*\((?:at line \d+, column \d+|at end of document)\)")
KEY_LINE = re.compile(r"\s*([A-Za-z0-9_-]+)\s*=")


@dataclass(frozen=True)
class Head:
    """The head fields of a file and what follows them."""

    values: dict  # what tomllib reads; None when there are none or they cannot be read
    error: str  # why `values` is None
    error_line: int  # the line of the file of the error
    key_lines: dict  # key -> its line in the file
    heading: tuple  # (line, text) of the first line after the head fields that is not blank, or None
    body: str  # all after the line that closes the head fields (the whole text when there are none)


def read_head(text):
    """The head fields: from a first line `+++` to the next line `+++` (`line_kinds`), read by tomllib."""
    lines = text.split("\n")
    n = line_kinds(lines)[0].count(HEAD)  # the lines of the head fields come first
    values, error, error_line, end = None, None, 1, n - 1
    if n == 0:
        error = NO_HEAD
    elif n < 2 or lines[end] != HEAD_LINE:
        error = NOT_CLOSED
    else:
        try:
            values = tomllib.loads("\n".join(lines[1:end]))
        except tomllib.TOMLDecodeError as e:
            m = re.search(r"at line (\d+)", str(e))
            error, error_line = TOML_AT.sub("", str(e)), int(m.group(1)) + 1 if m else end + 1
    key_lines = {}
    for i in range(1, end):
        if m := KEY_LINE.match(lines[i]):
            key_lines.setdefault(m.group(1), i + 1)
    heading = next(((i + 1, lines[i]) for i in range(end + 1, len(lines)) if lines[i].strip()), None)
    return Head(values, error, error_line, key_lines, heading, "\n".join(lines[end + 1 :]))


def toml_value(v):
    """A value of the head fields in the normal form: a string `"…"`, an integer, a TOML date, or an
    array of them on one line."""
    if isinstance(v, str):
        return spec_blocks.toml_string(v)
    if isinstance(v, list) and not any(isinstance(x, list) for x in v):
        return "[" + ", ".join(map(toml_value, v)) + "]"
    if type(v) is int:
        return str(v)
    if type(v) is date:
        return v.isoformat()
    raise DocsError(f"cannot write {v!r} as a head field (strings, integers, dates and arrays of them)")


def render_head(values, order):
    """The head fields in the normal form: the keys in `order` (the README's), a None value left out."""
    extra = [k for k in values if k not in order]
    if extra:
        raise DocsError(f"`{extra[0]}` is not a field of the table ({', '.join(order)})")
    lines = [f"{k} = {toml_value(values[k])}" for k in order if values.get(k) is not None]
    return "\n".join([HEAD_LINE, *lines, HEAD_LINE]) + "\n"


def head_update(root, rel, values, order):
    """The new text of a file with its head fields replaced by `values`, its body kept byte for byte.
    Writes nothing; raises DocsError when the file is open in vim, has CR line ends, or has head fields
    that cannot be read (fixed by hand: nothing is lost), or when the new text does not read back as
    `values` and the same body."""
    swaps = swap_files_of(Path(root) / rel)
    if swaps:
        raise DocsError(f"{rel}: the swap file {swaps[0].name} (open in vim?); nothing is written")
    text = read_doc(root, rel)
    if "\r" in text:
        raise DocsError(f"{rel}: it has CR line ends; nothing is written")
    head = read_head(text)
    if head.values is None and head.error != NO_HEAD:
        raise DocsError(f"{rel}:{head.error_line}: {head.error}; fix the head fields by hand")
    new = render_head(values, order) + head.body
    back = read_head(new)
    if back.values != {k: v for k, v in values.items() if v is not None} or back.body != head.body:
        raise DocsError(f"{rel}: the new head fields do not read back as given; nothing is written")
    return new


def write_head(root, rel, values, order):
    """`head_update` and write it (U3's `set`)."""
    write_atomic(Path(root) / rel, head_update(root, rel, values, order))


# ---------------------------------------------------------------- the field tables of the READMEs (X-2 DT-1, DT-B)

FIELDS_HEAD = "## 頭の欄"
FIELD_COLUMNS = ["キー", "形", "値", "要る", "意味"]
# `<base>` or `<base>の並び` (an array); the IDs name their kinds: `ID（S）`, `ID の並び（W、T、PH2）`, and
# STAGE_KIND for a stage (`W4`, `ID（W、段、PH2）`), which is not a kind of `repo.KINDS` (no file, not in the text).
STAGE_KIND = "段"
FORM = re.compile(
    r"(?P<base>文字列|閉じた値|節|日付|整数)(?P<many>の並び)?|(?P<id>ID)(?P<ids> の並び)?（(?P<kinds>[^）]+)）"
)
REQUIRED = {"はい": True, "いいえ": False}
EXPECTED = {
    "文字列": "a string", "節": "a section (`§6.1`, `tools.md §3.2`)", "日付": "a date", "整数": "an integer",
}  # fmt: skip


@dataclass(frozen=True)
class Field:
    form: str  # as the README writes it
    base: str
    many: bool
    kinds: tuple  # of an ID
    values: tuple  # of 閉じた値: strings, or integers when all are digits
    required: bool

    def fits(self, v):
        if self.base == "閉じた値":
            return type(v) is type(self.values[0]) and v in self.values
        if self.base == "ID":
            if STAGE_KIND in self.kinds and isinstance(v, str) and STAGE.fullmatch(v):
                return True
            kind = repo.kind_of(v) if isinstance(v, str) else None
            return kind is not None and kind.name in self.kinds
        if self.base == "節":
            return isinstance(v, str) and repo.SECTION_RE.fullmatch(v) is not None
        return type(v) is {"文字列": str, "日付": date, "整数": int}[self.base]

    def expected(self):
        if self.base == "閉じた値":
            return "one of " + " / ".join(map(str, self.values))
        if self.base == "ID":
            return f"an ID of {'、'.join(self.kinds)}"
        return EXPECTED[self.base]


@dataclass(frozen=True)
class FieldTable:
    readme: Path
    order: tuple
    fields: dict

    def check_value(self, key, value):
        """Why `value` does not fit the field `key`, or None (the check (a) and U3's `set`)."""
        f = self.fields[key]
        if f.many != isinstance(value, list):
            return f"`{key}` is {'not ' if f.many else ''}an array; its form is {f.form}"
        bad = next((v for v in (value if f.many else [value]) if not f.fits(v)), None)
        return None if bad is None else f"`{key}` has {_shown(bad)}, not {f.expected()}"


def _shown(v):
    try:
        return toml_value(v)
    except DocsError:
        return f"a {type(v).__name__}"


def field_table(tree, kind):
    """The field table of a kind's directory: under FIELDS_HEAD in its README, else in the README one
    up (one table for S, D, K, Q and A). A Finding (one for the directory) when it is broken."""
    d = Path(kind.dir)
    for rel in (d / "README.md", d.parent / "README.md"):
        if (tree.root / rel).is_file():
            lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
            at = [i for i, line in enumerate(lines) if line == FIELDS_HEAD and kinds[i] == TEXT]
            if at:
                return _parse_fields(rel, lines, kinds, at)
    return Finding(d / "README.md", None, f"no field table (`{FIELDS_HEAD}` in {d}/README.md or {d.parent}/README.md)")


def _parse_fields(rel, lines, kinds, at):
    def broken(i, what):
        return Finding(rel, i + 1, f"the field table: {what}; the files of the directory are not checked")

    if len(at) > 1:
        return broken(at[1], f"a second `{FIELDS_HEAD}`")
    i = at[0] + 1
    while i < len(lines) and not (kinds[i] == TEXT and lines[i].lstrip().startswith(("|", "#"))):
        i += 1
    if i == len(lines) or lines[i].lstrip().startswith("#"):
        return broken(at[0], "no table under the heading")
    if table_cells(lines[i]) != FIELD_COLUMNS:
        return broken(i, f"the header is not `| {' | '.join(FIELD_COLUMNS)} |`")
    if i + 1 == len(lines) or not DELIMITER.fullmatch(lines[i + 1].strip()):
        return broken(i + 1, "no delimiter row")
    fields, j = {}, i + 2
    while j < len(lines) and kinds[j] == TEXT and lines[j].lstrip().startswith("|"):
        cells = table_cells(lines[j])
        if len(cells) != len(FIELD_COLUMNS):
            return broken(j, f"{len(cells)} cells, not {len(FIELD_COLUMNS)}")
        key, form, vals, req = cells[0].strip("`"), cells[1], cells[2], cells[3]
        m = FORM.fullmatch(form)
        kinds_ = tuple(k.strip() for k in m.group("kinds").split("、")) if m and m.group("id") else ()
        values = [v.strip().strip("`").strip() for v in vals.split(" / ")]
        if not re.fullmatch(r"[a-z0-9_]+", key):
            return broken(j, f"the key `{key}` is not of lowercase letters, digits and `_`")
        if key in fields:
            return broken(j, f"the key `{key}` is given twice")
        if m is None:
            return broken(j, f"the form `{form}` is not known")
        if any(k not in repo.KIND and k != STAGE_KIND for k in kinds_):
            return broken(j, f"the form `{form}` names a kind that is not one ({', '.join([*repo.KIND, STAGE_KIND])})")
        if m.group("base") == "閉じた値" and ("" in values or len(set(values)) != len(values)):
            return broken(j, f"the values {vals} (write `A / B`, none empty or twice)")
        if m.group("base") != "閉じた値" and vals not in ("", "—"):
            return broken(j, f"the values {vals} of the form {form} (only 閉じた値 has values)")
        if req not in REQUIRED:
            return broken(j, f"要る is `{req}`, not {' or '.join(REQUIRED)}")
        if all(re.fullmatch(r"[0-9]+", v) for v in values):
            values = [int(v) for v in values]
        base = m.group("base") or "ID"
        fields[key] = Field(form, base, bool(m.group("many") or m.group("ids")), kinds_,
                            tuple(values) if base == "閉じた値" else (), REQUIRED[req])  # fmt: skip
        j += 1
    if not fields:
        return broken(i, "no row")
    return FieldTable(rel, tuple(fields), fields)


# ---------------------------------------------------------------- the files of the IDs (X-2 DT-5)


class Index:
    """The files of the IDs over one Tree: `files[kind]` for each kind whose directory is there (the
    one place that says which kinds are read, X-2 DT-7; `docs/` and `history/` are not read)."""

    def __init__(self, tree):
        self.tree, self.layout = tree, repo.Layout(tree.root)
        self.files, self.misnamed, self._tables, self._done, self._headings = {}, {}, {}, None, {}
        for kind in repo.KINDS:
            if kind.dir and (tree.root / kind.dir).is_dir():
                ids, other = {}, []
                for p in sorted((tree.root / kind.dir).glob("*.md")):
                    if p.is_file() and p.name != "README.md" and not p.name.endswith(".draft.md"):
                        rel = p.relative_to(tree.root)
                        if re.fullmatch(kind.pattern, p.name[:-3]):
                            ids[p.name[:-3]] = rel
                        else:
                            other.append(rel)
                self.files[kind.name], self.misnamed[kind.name] = ids, other

    @classmethod
    def of(cls, root):
        return cls(Tree(root, []))

    def table(self, name):
        if name not in self._tables:
            self._tables[name] = field_table(self.tree, repo.KIND[name])
        return self._tables[name]

    def _files(self, name):
        """{id: rel} of a kind; RepoError when its directory is not there (never an empty set)."""
        if name not in self.files:
            raise repo.RepoError(f"{repo.KIND[name].dir or name}/: no directory")
        return self.files[name]

    def ids(self, name):
        """The IDs of a kind: its files (a draft is not one, DF-4). RepoError when its directory is not
        there or has no file of an ID."""
        if not self._files(name):
            raise repo.RepoError(f"{repo.KIND[name].dir}/: no file of an ID")
        return set(self.files[name])

    def known(self, name):
        """The IDs of a kind there are, or None when they are not checked (no directory: the history,
        PH2, a kind whose directory is not made)."""
        return set(self.files[name]) if name in self.files else None

    def place(self, name):
        """Where a kind is read, for messages: its directory."""
        return f"{repo.KIND[name].dir}/"

    def work_done(self):
        """{W: done}: `status = "DONE"` of the files of `tasks/W/` (one place, D-15)."""
        if self._done is None:
            heads = {w: self.tree.head(rel).values or {} for w, rel in self._files("W").items()}
            self._done = {w: v.get("status") == "DONE" for w, v in heads.items()}
        return self._done

    def headings(self, which):
        """The numbered headings of the spec (`spec`) or of the spec of the tools (`tools`)."""
        if which not in self._headings:
            doc = repo.spec_doc(self.tree.root) if which == "spec" else repo.tools_doc(self.tree.root)
            self._headings[which] = set(spec_blocks.headings(doc.text))
        return self._headings[which]



# ---------------------------------------------------------------- check (a), (b), (c), (e)

HEADING_LINE = re.compile(r"# (\S+)(?: .*)?")
# (b) A `§` after a document name or one of these words is not the spec's; after `tools.md` it is the
# spec of the tools'. A run of `§` joined by `・`, `、` or spaces keeps what the first was (E3).
SEC_QUALIFIERS = ("計画", "rework", "レビュー", "変更点", "点検", "C11")
SEC_BEFORE = re.compile(r"(?P<doc>\S+\.md)`?\s*$|(?:" + "|".join(SEC_QUALIFIERS) + r")\s*$")
TOOLS_NAME = re.compile(r"(?:^|[^\w.-])tools\.md$")
SEC_CHAIN = re.compile(r"[・、 ]*")
BODY_SECTION = re.compile(r"§(\d+(?:\.\d+)*)")
LINK = re.compile(r"\]\(([^()\s]*)(?:\s+[^()]*)?\)")
EXTERNAL = re.compile(r"[A-Za-z][A-Za-z0-9+.-]*:|#")


def _id_files(tree):
    """(table, id, rel, head) of the files of the IDs whose directory has a good field table."""
    for name, files in tree.index.files.items():
        table = tree.index.table(name)
        if isinstance(table, FieldTable):
            for id_, rel in files.items():
                yield table, id_, rel, tree.head(rel)


def check_heads(tree):
    """(a) The field table of each directory, the names of the files, the head fields against it, and
    the heading `# <ID> <title>`."""
    idx = tree.index
    if not idx.files:
        tree.notes.append("heads, refs, relations: no directory of the new layout")
    for name, files in idx.files.items():
        kind, table = repo.KIND[name], idx.table(name)
        if not isinstance(table, FieldTable):
            yield table
            continue
        for rel in idx.misnamed[name]:
            yield Finding(rel, 1, f"the name is not an ID of {name} ({kind.dir}/<ID>.md)")
        if not files:
            yield Finding(Path(kind.dir), None, "no file of an ID; the checks would pass reading nothing")
        for id_, rel in files.items():
            if name == "W" and (why := _missing(idx, id_.split("-")[0], STAGE_KIND)):
                yield Finding(rel, 1, f"{why}; the stage of {id_}")
            head = tree.head(rel)
            if head.values is None:
                yield Finding(rel, head.error_line, head.error)
                continue
            for key, value in head.values.items():
                where = head.key_lines.get(key, 1)
                if key not in table.fields:
                    yield Finding(rel, where, f"`{key}` is not a field of {table.readme.as_posix()}")
                elif why := table.check_value(key, value):
                    yield Finding(rel, where, why)
            for key in table.order:
                if table.fields[key].required and key not in head.values:
                    yield Finding(rel, 1, f"the field `{key}` is required ({table.readme.as_posix()})")
            m = HEADING_LINE.fullmatch(head.heading[1]) if head.heading else None
            if m is None or m.group(1) != id_:
                at = head.heading[0] if head.heading else 1
                yield Finding(rel, at, f"the first line after the head fields is not `# {id_} <title>`")


def body_sections(line):
    """(start, number, "spec" | "tools" | None) of each `§` of a line of the text (None: not the spec's)."""
    out, last, which = [], None, "spec"
    for m in BODY_SECTION.finditer(line):
        if last is None or not SEC_CHAIN.fullmatch(line[last : m.start()]):
            q = SEC_BEFORE.search(line[: m.start()])
            which = "spec" if q is None else "tools" if q.group("doc") and TOOLS_NAME.search(q.group("doc")) else None
        out.append((m.start(), m.group(1), which))
        last = m.end()
    return out


def check_refs(tree, only=None):
    """(b) The IDs of the head fields and of the text are there (the kinds whose directory is there,
    `Index.known`; the history and PH2 are not checked; a stage has a work), and the sections are numbered headings of
    the spec. Of the files `only` when it is given."""
    idx = tree.index
    for table, id_, rel, head in _id_files(tree):
        if head.values is None or (only is not None and rel not in only):
            continue
        found = []  # (line, key or None, id or section, which)
        for key, value in head.values.items():
            field = table.fields.get(key)
            for v in value if isinstance(value, list) else [value]:
                if not isinstance(v, str):
                    continue
                if field is not None and field.base == "節":
                    if m := repo.SECTION_RE.fullmatch(v):
                        which = "tools" if m.group("tools") else "spec"
                        found.append((head.key_lines.get(key, 1), key, m.group("num"), which))
                elif field is not None and STAGE_KIND in field.kinds and STAGE.fullmatch(v):
                    found.append((head.key_lines.get(key, 1), key, v, STAGE_KIND))
                else:
                    found += [(head.key_lines.get(key, 1), key, m.group(0), None) for m in repo.ID_RE.finditer(v)]
        lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
        # the text: after the heading (its ID is (a)'s), or after the head fields when there is no heading
        start = len(lines) - len(head.body.split("\n"))
        if head.heading and HEADING_LINE.fullmatch(head.heading[1]):
            start = head.heading[0]
        for i in range(start, len(lines)):
            if kinds[i] == TEXT:
                found += [(i + 1, None, m.group(0), None) for m in repo.ID_RE.finditer(lines[i])]
                found += [(i + 1, None, num, which) for _, num, which in body_sections(lines[i]) if which]
        seen = set()
        for line, key, ref, which in found:
            if (line, ref, which) in seen:
                continue
            seen.add((line, ref, which))
            what = _missing(idx, ref, which)
            if what:
                yield Finding(rel, line, (f"{key}: " if key else "") + what)


def _missing(idx, ref, which):
    """Why a reference is not found, or None. A stage (`W4`, `M5`) is found when the table of the stages
    has it (`repo.Layout.stages`), with or without a work."""
    if which == STAGE_KIND:
        return None if ref in idx.layout.stages() else _not_a_stage(idx.layout, ref)
    if which:
        if ref in idx.headings(which):
            return None
        return f"{'tools.md ' if which == 'tools' else ''}§{ref} is not a numbered heading of the spec" + (
            " of the tools" if which == "tools" else ""
        )
    known = idx.known(repo.kind_of(ref).name)
    return None if known is None or ref in known else f"{ref} is not found ({idx.place(repo.kind_of(ref).name)})"


def _not_a_stage(layout, ref):
    return f"{ref}: not a stage of {repo.STAGES} ({', '.join(layout.stages())})"


# The direction of each ID field of the field tables (`Field.base == "ID"`) for `graph`: True when the file
# that writes the field rests on the IDs it names (`depends`: the work on the works before it), False when they
# rest on it (`tasks`: the works on the decision; `before`: a deadline, not a dependence). Check (c) finds an
# ID field of a README that has no row here.
RESTS_ON = {"depends": True, "decisions": True, "tasks": False, "fix": False, "before": False}


def undirected(tree):
    """(README, line, key) of the ID fields of the field tables that have no direction in RESTS_ON."""
    seen = set()
    for name in tree.index.files:
        table = tree.index.table(name)
        if isinstance(table, FieldTable) and table.readme not in seen:
            seen.add(table.readme)
            lines = tree.lines(table.readme)
            at = lines.index(FIELDS_HEAD)
            rows = [(i + 1, table_cells(x)[:1]) for i, x in enumerate(lines) if i > at and x.startswith("|")]
            for key in (k for k, f in table.fields.items() if f.base == "ID" and k not in RESTS_ON):
                yield table.readme, next((i for i, first in rows if first in ([key], [f"`{key}`"])), None), key


def check_relations(tree):
    """(c) The relations the fields keep (the keys are named here, DT-1): each ID field has a direction
    in RESTS_ON, a decision OPEN when every work of `tasks` is DONE, an issue OPEN when every work of
    `fix` is DONE, `doing` on a work that is not DOING. A missing ID is (b)'s."""
    for readme, line, key in undirected(tree):
        yield Finding(readme, line, f"the ID field `{key}` has no direction in `docs.RESTS_ON` (`graph` needs it)")
    idx = tree.index
    for _, id_, rel, head in _id_files(tree):
        v = head.values
        if v is None:
            continue
        line = head.key_lines.get
        for key in ("tasks", "fix"):
            works = v.get(key)
            if v.get("status") == "OPEN" and isinstance(works, list) and works:
                if all(idx.work_done().get(w) is True for w in works):
                    done = ", ".join(map(str, works))
                    yield Finding(rel, line("status", 1), f"OPEN, but every work of `{key}` is DONE ({done})")
        if "doing" in v and v.get("status") != "DOING":
            yield Finding(rel, line("doing", 1), f"`doing` on a work that is {v.get('status')}, not DOING")


def check_links(tree):
    """(e) The relative links of the READMEs reach a file or a directory."""
    for rel in tree.files:
        if rel.name != "README.md":
            continue
        lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
        for i, line in enumerate(lines):
            if kinds[i] != TEXT:
                continue
            spans = code_spans(line)
            for m in LINK.finditer(line):
                target = re.split(r"[#?]", m.group(1), maxsplit=1)[0]
                if any(a <= m.start() < b for a, b in spans) or not target or EXTERNAL.match(m.group(1)):
                    continue
                base = tree.root if target.startswith("/") else tree.root / rel.parent
                if not (base / target.lstrip("/")).exists():
                    yield Finding(rel, i + 1, f"the link {m.group(1)} is not found")


CHECKS = [
    ("tables", check_tables),
    ("heads", check_heads),
    ("refs", check_refs),
    ("relations", check_relations),
    ("links", check_links),
]


def cmd_check(args):
    files = repo.doc_files(args.root)
    if not files:
        raise DocsError(f"no document found under {args.root}")
    tree, counts = Tree(args.root, files), []
    for name, check in CHECKS:
        found = list(check(tree))
        if found:
            print(f"== {name}")
            print("\n".join(map(str, found)))
        counts.append((name, len(found)))
    for note in tree.notes:
        print(note)
    total = sum(n for _, n in counts)
    if total:
        print(f"docs check: {total} problem(s) (" + ", ".join(f"{name} {n}" for name, n in counts) + ")")
    else:
        print(f"docs check: no problem in {len(files)} document(s) (" + ", ".join(n for n, _ in counts) + ")")
    return 1 if total else 0


# ---------------------------------------------------------------- the IDs for the commands (X-2 DT-2, DT-3, DT-6)

DECISIONS = ("S", "D", "K", "Q", "A")  # the kinds of decisions/ (DF-4)
ISSUES = ("R", "RF")  # the kinds with `fix` and `decisions` (DF-5)
NONE = "-"
GAP_LABEL = re.compile(r"\s*- 空白[:：]\s*(.*)")
GAP_TITLE = 40  # the characters of `空白` shown for an S with no title (DT-3)
STAGE = repo.STAGE_NAME  # the form of a stage; the stages are the table's (`repo.Layout.stages`)
INF = float("inf")
EXCERPT = 60  # the characters `back` shows around a mention


def _listed(value):
    """The strings of a field: its items, or the value itself."""
    return [v for v in (value if isinstance(value, list) else [value]) if isinstance(v, str)]


def id_key(id_):
    """The order of the IDs: the kinds as in `repo.KINDS`, then their numbers (`W3-9` before `W3-13`)."""
    kind = repo.kind_of(id_)
    return (repo.KINDS.index(kind) if kind else len(repo.KINDS), tuple(map(int, re.findall(r"\d+", id_))), id_)


def due_key(due, stages):
    """The order of the deadlines of `before` (the one place to compare them), or None for another value:
    a work `W4-02` < `W4-99` < its stage `W4` (the end of the stage) < `W5-01` < … < `M5` < `PH2` (after
    every stage), the stages in the order of `stages` (the table)."""
    if due == repo.PHASE2:
        return (INF,)
    if not isinstance(due, str):
        return None
    if due in stages:
        return (stages.index(due), INF)
    stage = due.split("-")[0]
    if repo.kind_of(due) is repo.KIND["W"] and stage in stages:
        return (stages.index(stage), int(due.split("-")[1]))
    return None


def section_key(sec):
    m = repo.SECTION_RE.fullmatch(sec)
    return (bool(m.group("tools")), tuple(map(int, m.group("num").split(".")))) if m else (True, (), sec)


def has_heading(id_, head):
    """The first line after the head fields is `# <ID> …`."""
    m = HEADING_LINE.fullmatch(head.heading[1]) if head.heading else None
    return m is not None and m.group(1) == id_


def heading_title(id_, head):
    """The title of the heading `# <ID> <title>`, or ""."""
    return head.heading[1][len(id_) + 2 :].strip() if has_heading(id_, head) else ""


def title_of(id_, head):
    """The title, or for an S with none the head of its `空白` (DF-4: 399 S have no title)."""
    title = heading_title(id_, head)
    if not title and repo.kind_of(id_).name == "S":
        gap = next((m.group(1) for line in head.body.split("\n") if (m := GAP_LABEL.fullmatch(line))), "")
        return gap[:GAP_TITLE]
    return title


@dataclass(frozen=True)
class Where:
    """Where an ID is (its file), or a `§` (`path`: the file and the line of its heading)."""

    id: str
    rel: Path  # None: not found, `reason` says where it was looked for
    line: int  # the line of the heading of a `§`; None for a file
    status: str  # `status` of the head fields
    title: str
    values: dict  # the head fields
    reason: str = None

    def place(self, root=None):
        """`rel` or `rel:line` (absolute under `root` when given), or `not found (…)`."""
        if self.rel is None:
            return f"not found ({self.reason})"
        rel = (Path(root) / self.rel).resolve() if root else self.rel
        return rel.as_posix() + (f":{self.line}" if self.line else "")

    def spec(self):
        return ", ".join(_listed(self.values.get("spec"))) or NONE


class Ids:
    """What the commands know about the IDs, on one Tree: the files of `Index` (their head fields read
    once)."""

    def __init__(self, root, files=()):
        self.root = Path(root)
        self.tree = Tree(root, files)
        self.index, self.layout, self._where = self.tree.index, self.tree.index.layout, {}

    def has(self, name):
        """The directory of the kind is there (`Index.files`)."""
        return name in self.index.files

    def require(self, id_or_kind, kinds=None):
        """The Kind of an ID (or a kind's name) that has its directory of the new layout; DocsError
        (exit 2) otherwise."""
        kind = repo.KIND.get(id_or_kind) or repo.kind_of(id_or_kind)
        names = kinds or [k.name for k in repo.KINDS if k.dir]
        if kind is None or kind.name not in names:
            raise DocsError(f"{id_or_kind}: not an ID or a kind of {', '.join(names)}")
        if not self.has(kind.name):
            raise DocsError(f"{kind.name}: not in the new layout (no {kind.dir}/)")
        return kind

    def table(self, name):
        table = self.index.table(name)
        if isinstance(table, Finding):
            raise DocsError(str(table))
        return table

    def heads(self, names):
        """(id, rel, head fields) of the files of the kinds in the new layout."""
        for name in names:
            if self.has(name):
                for id_, rel in self.index.files[name].items():
                    yield id_, rel, self.tree.head(rel).values or {}

    def having(self, names, key, id_):
        """The IDs of the kinds whose field `key` has `id_`, in order."""
        return sorted((i for i, _, v in self.heads(names) if id_ in _listed(v.get(key))), key=id_key)

    def where(self, id_):
        if id_ not in self._where:
            self._where[id_] = self._find(id_)
        return self._where[id_]

    def _find(self, id_):
        kind = repo.kind_of(id_)
        if self.has(kind.name):
            rel = self.index.files[kind.name].get(id_)
            if rel is None:
                return Where(id_, None, None, NONE, "", {}, f"{kind.dir}/")
            head = self.tree.head(rel)
            values = head.values or {}
            return Where(id_, rel, None, str(values.get("status", NONE)), title_of(id_, head), values)
        # no directory, or a kind with no file: the history (C, T) or the second phase (PH2)
        why = f"no {kind.dir}/" if kind.dir else "a kind with no file: the history or the second phase"
        return Where(id_, None, None, NONE, "", {}, why)

    def state(self, ref):
        """The status of an ID, or of a stage (`depends`, DF-6): DONE when every work of it is DONE, else
        `残り N` (its works not DONE, `work_done`); `-` when it has none (an M stage before its works are
        made; a stage not in the table, which `check` (b) finds)."""
        if not STAGE.fullmatch(ref):
            return self.where(ref).status
        done = [d for w, d in self.index.work_done().items() if w.startswith(ref + "-")]
        return NONE if not done else "DONE" if all(done) else f"残り {done.count(False)}"

    def row(self, id_):
        """`ID<TAB>status<TAB>title<TAB>sections` (the relations of `show`, the items of `ticket`)."""
        w = self.where(id_)
        return f"{id_}\t{w.status}\t{w.title or NONE}\t{w.spec()}"


def _rel_arg(root, arg):
    """A path given to a command: relative to the root, or absolute inside it."""
    p = Path(arg)
    if not p.is_absolute():
        return p
    try:
        return p.resolve().relative_to(Path(root).resolve())
    except ValueError:
        raise DocsError(f"{arg}: not under the root {root}") from None


def _id_arg(arg):
    if repo.kind_of(arg) is None:
        raise DocsError(f"{arg}: not an ID")
    return arg


def _mentions(text_line, id_):
    return [m.span() for m in repo.ID_RE.finditer(text_line) if m.group(0) == id_]


def named_ids(tree, rel, text=True):
    """[(key or None, ID)] a file names, in order (`refs`, `graph`, `check_write`; one reading, D-15): the
    bare IDs (`repo.ID_RE`; no stage, no PH2) of the strings of each head field (its key), then with
    `text` of each line after the head fields (None; every line when they are not there or broken)."""
    lines, head = tree.lines(rel), tree.head(rel)
    found = [(key, m) for key, value in (head.values or {}).items() for v in _listed(value) for m in repo.ID_RE.findall(v)]
    if text:
        start = 0 if head.values is None else len(lines) - len(head.body.split("\n"))
        found += [(None, m) for line in lines[start:] for m in repo.ID_RE.findall(line)]
    return found


def excerpt(line, a, b):
    lo, hi = max(0, a - EXCERPT), min(len(line), b + EXCERPT)
    return ("…" if lo else "") + line[lo:hi].strip() + ("…" if hi < len(line) else "")


# ---------------------------------------------------------------- path, back, refs (DT-2)


def path_args(p):
    p.add_argument("refs", nargs="+", metavar="ID|§", help="IDs, `§6.1`, `tools.md §3.2`")
    p.add_argument("--abs", action="store_true", help="absolute paths (the Read tool)")


def cmd_path(args):
    ids, missing = Ids(args.root), 0
    for ref in args.refs:
        if m := repo.SECTION_RE.fullmatch(ref):
            doc = repo.tools_doc(ids.root) if m.group("tools") else repo.spec_doc(ids.root)
            line = spec_blocks.heading_line(doc.text, m.group("num"))
            if line is None:
                spec = "the spec of the tools" if m.group("tools") else "the spec"
                where = Where(ref, None, None, NONE, "", {}, f"not a numbered heading of {spec}")
            else:
                where = Where(ref, *doc.locate(line), NONE, "", {})
        elif repo.kind_of(ref):
            where = ids.where(ref)
        else:
            raise DocsError(f"{ref}: not an ID or a section (`S-537`, `§6.1`, `tools.md §3.2`)")
        if where.rel is None:
            print(f"{ref}: {where.place()}", file=sys.stderr)
            missing += 1
        else:
            print(where.place(ids.root if args.abs else None))
    return 1 if missing else 0


def back_args(p):
    p.add_argument("id")
    p.add_argument("--history", action="store_true", help="`history/` too")


def cmd_back(args):
    id_, root = _id_arg(args.id), Path(args.root)
    files = repo.doc_files(root)
    if args.history:
        files += sorted(p.relative_to(root) for p in (root / "history").rglob("*.md") if p.is_file())
    ids = Ids(root, files)
    own, tree, keys, text, hit = ids.where(id_), ids.tree, [], [], set()
    for rel in files:
        if rel == own.rel:
            continue  # the file of the ID itself
        lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
        head = tree.head(rel) if HEAD in kinds else None
        for key, value in (head.values or {}).items() if head else ():
            if any(v == id_ or _mentions(v, id_) for v in _listed(value)):
                keys.append(f"{rel.as_posix()}:{head.key_lines.get(key, 1)}: {key}")
                hit.add(rel)
        for i, line in enumerate(lines):
            if kinds[i] == HEAD and head.values is not None:
                continue  # the head fields read above
            if spans := _mentions(line, id_):
                text.append(f"{rel.as_posix()}:{i + 1}: {excerpt(line, *spans[0])}")
                hit.add(rel)
    for title, found in (("keys", keys), ("text", text)):
        if found:
            print(f"== {title}\n" + "\n".join(found))
    print(f"docs back: {id_}: {len(keys)} key(s), {len(text)} line(s) of text in {len(hit)} file(s)")
    return 0


def refs_args(p):
    p.add_argument("target", metavar="ID|PATH", help="an ID, or a path relative to the root")


def cmd_refs(args):
    ids, target = Ids(args.root), args.target
    if repo.kind_of(target):
        w = ids.where(target)
        if w.rel is None:
            print(f"{target}: {w.place()}")
            return 1
        rel, own = w.rel, target
    else:
        rel = _rel_arg(ids.root, target)
        own = rel.name[:-3] if rel.name.endswith(".md") and repo.kind_of(rel.name[:-3]) else None
        if not (ids.root / rel).is_file():
            print(f"{target}: not found")
            return 1
    found = [i for i in dict.fromkeys(i for _, i in named_ids(ids.tree, rel)) if i != own]
    for id_ in found:
        w = ids.where(id_)
        print(f"{id_}\t{w.status}\t{w.place()}\t{w.title or NONE}")
    lost = sum(ids.where(i).rel is None for i in found)
    print(f"docs refs: {rel.as_posix()}: {len(found)} ID(s), {lost} not found")
    return 0


# ---------------------------------------------------------------- graph (X-2 U7b)

GRAPH_DEPTH_MAX = 5  # the deepest `--depth` (tentative: tuned in use; no unbounded depth)
MENTION, STAGE_EDGE = "text", "stage"  # the types of the edges that are not of an ID field


def graph_args(p):
    p.add_argument("start", metavar="ID|STAGE", help="an ID of a kind (`S-239`, `C-40`, `PH2`) or a stage (`W3`)")
    p.add_argument("--back", action="store_true", help="what rests on START (what to look at again when it changes)")
    p.add_argument("--depth", type=int, default=1, help=f"1 to {GRAPH_DEPTH_MAX} (default 1)")
    p.add_argument("--typed", action="store_true", help="only the edges of the ID fields and of the stages")


def typed_edge(type_):
    return type_ in RESTS_ON or type_ == STAGE_EDGE


def node_key(node):
    """The order of the nodes: the IDs and the stages (`id_key`), then the paths."""
    return (1, node.as_posix()) if isinstance(node, Path) else (0, id_key(node))


def edges(ids):
    """{(on, base, type)}: `on` rests on `base`. Each file names IDs (`named_ids`): `text` edges from it
    (`text(key)` in a string field, `found_by = "W1-01/t"`). Its ID fields are typed edges, turned by
    RESTS_ON (DocsError when a field has no direction). A stage rests on each of its works (`stage`). A
    file of no ID (rules, the spec, the design notes, the table of the stages, a draft) is its path: only its edges to the
    IDs it names. O(characters)."""
    bad = [f"`{key}` of {readme.as_posix()}" for readme, _, key in undirected(ids.tree)]
    if bad:
        raise DocsError(f"no direction in docs.RESTS_ON for the ID field(s) {', '.join(bad)}")
    id_of = {rel: i for files in ids.index.files.values() for i, rel in files.items()}
    out = set()

    def add(on, base, type_):
        if on != base:  # an edge to itself (a file names its own ID) is dropped here, the one place
            out.add((on, base, type_))

    for rel in ids.tree.files:
        node = id_of.get(rel, rel)
        fields = ids.table(repo.kind_of(node).name).fields if rel in id_of else {}
        typed = [key for key, f in fields.items() if f.base == "ID"]
        for key, ref in named_ids(ids.tree, rel):
            if key not in typed:
                add(node, ref, MENTION if key is None else f"{MENTION}({key})")
        values = ids.tree.head(rel).values or {}
        for key in typed:
            for v in _listed(values.get(key)):
                if fields[key].fits(v):
                    add(*((node, v) if RESTS_ON[key] else (v, node)), key)
    for work in ids.index.files.get("W", {}):
        add(work.split("-")[0], work, STAGE_EDGE)
    return out


def walk(near, start, depth):
    """Breadth first from `start` over `near` ({node: [(next, type)]}) with a queue, no recursion: each
    node enters the queue once (the set `seen`), so a cycle stops it; the new nodes at depth+1 are only
    counted. (rows (depth, node, type, from) in the order of depth and `node_key`, the count): a node
    by the first edge that reaches it, the edges of a node taken typed first, then `text(key)`, then
    `text`, each in `node_key` and then the type (no order of a set is left). O(V+E), and the sorting."""

    def order(edge):
        return not typed_edge(edge[1]), edge[1] == MENTION, node_key(edge[0]), edge[1]

    seen, queue, rows, more = {start}, deque([(start, 0)]), [], 0
    while queue:
        node, d = queue.popleft()
        for nxt, type_ in sorted(near.get(node, ()), key=order):
            if nxt not in seen:
                seen.add(nxt)
                if d == depth:
                    more += 1
                else:
                    rows.append((d + 1, nxt, type_, node))
                    queue.append((nxt, d + 1))
    return sorted(rows, key=lambda r: (r[0], node_key(r[1]))), more


def cmd_graph(args):
    """The relations of the decisions, made on the spot from the text and the ID fields (`edges`), every
    edge turned to `on -> base` (what rests on what). For "what to look at again when S-239 changes":

    1. `graph S-239 --back`: what rests on it directly (some 20 in the real tree).
    2. `graph S-239 --back --typed --depth 2`: the chain of the works and the issues. Through the stages
       the chain goes on to the later stages (S-239 reaches 70 nodes and W1-01 103 with no bound), so read
       the typed edges at the depth 1 or 2 too.
    3. The mentions of the text spread to hundreds beyond the depth 2: read one depth at a time and decide.

    `--depth` is 1 to GRAPH_DEPTH_MAX. Known: a draft (`S-1.draft.md`) is a path that rests on its S; a
    work rests on its stage one depth below (`graph W3-05 --back` has the stage W3 at the depth 1, and the
    works that depend on W3, the `depended_by` of `show`, at the depth 2: the same set one depth deeper)."""
    if not 1 <= args.depth <= GRAPH_DEPTH_MAX:
        raise DocsError(f"--depth {args.depth}: not 1 to {GRAPH_DEPTH_MAX}")
    ids, start = Ids(args.root, repo.doc_files(args.root)), args.start
    if repo.kind_of(start) is None and start not in ids.layout.stages():
        raise DocsError(f"{start}: not an ID or a stage of {repo.STAGES.as_posix()}")
    near = {}
    for on, base, type_ in edges(ids):
        if typed_edge(type_) or not args.typed:
            a, b = (base, on) if args.back else (on, base)
            near.setdefault(a, []).append((b, type_))
    rows, more = walk(near, start, args.depth)

    def shown(node):
        """(the node, its status, its title): of its file, of the works of a stage (`state`), `-` for a path."""
        if isinstance(node, Path):
            return node.as_posix(), NONE, NONE
        if STAGE.fullmatch(node):
            return node, ids.state(node), NONE
        w = ids.where(node)
        return node, w.status, w.title or NONE

    w = None if STAGE.fullmatch(start) else ids.where(start)
    if w is not None and w.rel is None:
        print(f"{start}: {w.place()}")
    else:
        name, status, title = shown(start)
        print(f"0\t{name}\t{NONE}\t{NONE}\t{status}\t{title}")
    for depth, node, type_, came in rows:
        name, status, title = shown(node)
        print(f"{depth}\t{name}\t{type_}\t{shown(came)[0]}\t{status}\t{title}")
    typed, n = sum(typed_edge(r[2]) for r in rows), len(rows)
    flags = "".join(f" --{f}" for f in ("back", "typed") if getattr(args, f))
    print(f"docs graph: {start}{flags}: {n} node(s) at depth ≤ {args.depth} ({typed} typed, {n - typed} text);"
          f" {more} more at depth {args.depth + 1}")  # fmt: skip
    return 0


# ---------------------------------------------------------------- show, list, changes (DT-2, DT-3, DT-6; the new layout)


def show_args(p):
    p.add_argument("id")
    p.add_argument("--relations", action="store_true", help="the head fields and the relations, no body")


def waiting(ids):
    """{work: the decisions it waits for}: OPEN, and the work carries it or it is due `before` the work.
    A stage or PH2 in `before` makes no work wait (which work of the stage needs it is not known)."""
    out = {}
    for i, _, v in sorted(ids.heads(DECISIONS), key=lambda r: id_key(r[0])):
        if v.get("status") == "OPEN":
            due = [b for b in _listed(v.get("before")) if repo.kind_of(b) is repo.KIND["W"]]
            for work in dict.fromkeys(_listed(v.get("tasks")) + due):
                out.setdefault(work, []).append(i)
    return out


def relations(ids, kind, id_, values):
    """The lines of the relations of `show` (DT-2): `label<TAB>ID<TAB>status<TAB>title<TAB>sections`."""
    out = []

    def add(label, refs):
        out.extend(f"{label}\t{ids.row(r)}" for r in refs)

    if kind == "W":
        add("decision", ids.having(DECISIONS, "tasks", id_))
        add("fixes", ids.having(ISSUES, "fix", id_))
        # its own `depends` and those that name its stage (`W4`: every work of W4)
        by = {*ids.having(["W"], "depends", id_), *ids.having(["W"], "depends", id_.split("-")[0])} - {id_}
        add("depended_by", sorted(by, key=id_key))
        add("waiting", waiting(ids).get(id_, []))
    elif kind in DECISIONS:
        add("tasks", _listed(values.get("tasks")))
        add("issue", ids.having(ISSUES, "decisions", id_))
        path = ids.root / repo.PENDING
        entries, errors = repo.load_pending(path) if path.is_file() else ([], [])
        out += [f"pending\t{e.kind}\t{e.target}\tuntil {e.until}" for e in entries if id_ in e.reasons]
        if errors:
            out.append(f"pending\t{repo.PENDING}: {len(errors)} error(s); `pending.py` shows them")
    elif kind in ISSUES:
        for key in ("fix", "decisions"):
            add(key, _listed(values.get(key)))
    return out


def cmd_show(args):
    ids = Ids(args.root)
    kind = ids.require(_id_arg(args.id))
    w = ids.where(args.id)
    if w.rel is None:
        print(f"{args.id}: {w.place()}")
        return 1
    head, lines = ids.tree.head(w.rel), ids.tree.lines(w.rel)
    body = len(lines) - len(head.body.split("\n"))  # the first line after the head fields
    top = head.heading[0] if has_heading(args.id, head) else body
    print(f"== {w.rel.as_posix()}")
    print("\n".join(lines[:top]))
    print("== relations")
    for line in relations(ids, kind.name, args.id, w.values):
        print(line)
    body = "\n".join(lines[top:]).strip("\n")
    if not args.relations and body:
        print("== body\n" + body)
    return 0


def list_args(p):
    p.add_argument("kind")
    p.add_argument("--status")
    p.add_argument("--stage", help="W: the works of the stage; decisions (PH2 too): `tasks` or `before`; issues: `fix`")
    p.add_argument("--group", type=int, help="decisions")
    p.add_argument("--before", help="decisions: `before` this work or stage (its end) or an earlier one (`due_key`)")
    p.add_argument("--no-fix", action="store_true", help="issues with no `fix`")
    p.add_argument("--waiting", action="store_true", help="works waiting for a decision")
    p.add_argument("--count", action="store_true", help="the numbers of each status (W: per stage)")


MAIN_FIELDS = {"W": ("size", "depends", "doing"), "R": ("severity", "fix", "decisions"), "RF": ("severity", "fix")}
DECISION_FIELDS = ("tasks", "spec", "before", "group")
LIST_ONLY = {"group": DECISIONS, "before": DECISIONS, "no_fix": ISSUES, "waiting": ("W",)}


def _stage_arg(layout, stage, ph2=False):
    """`--stage`: a stage of the table (`repo.Layout.stages`), or PH2 with `ph2`."""
    if stage is not None and not (stage in layout.stages() or (ph2 and stage == repo.PHASE2)):
        raise DocsError(_not_a_stage(layout, stage) + (f", or {repo.PHASE2}" if ph2 else ""))
    return stage


def _in_stage(works, stage):
    """A work of the stage, or the stage (or PH2) itself, in `works`."""
    return any(w == stage or w.startswith(stage + "-") for w in works)


def _stage_works(kind, id_, values):
    if kind in DECISIONS:
        return _listed(values.get("tasks")) + _listed(values.get("before"))
    return [id_] if kind == "W" else _listed(values.get("fix"))


def cmd_list(args):
    ids = Ids(args.root)
    kind = ids.require(args.kind).name
    for opt, kinds in LIST_ONLY.items():
        if getattr(args, opt) not in (None, False) and kind not in kinds:
            raise DocsError(f"--{opt.replace('_', '-')} is for {', '.join(kinds)}, not {kind}")
    if args.stage and kind == "X":
        raise DocsError("--stage is not for X")
    _stage_arg(ids.layout, args.stage, kind in DECISIONS)
    stages = ids.layout.stages() if args.before else ()
    if args.before and (due_key(args.before, stages) is None or args.before == repo.PHASE2):
        raise DocsError(f"--before {args.before}: not a work or a stage (`W4-02`, `W4`)")
    status = ids.table(kind).fields.get("status")
    if args.status and (status is None or args.status not in status.values):
        raise DocsError(f"--status {args.status}: not one of {' / '.join(map(str, status.values if status else ()))}")
    rows, total, waits = [], 0, waiting(ids) if args.waiting else {}
    for id_, _, v in sorted(ids.heads([kind]), key=lambda r: id_key(r[0])):
        total += 1
        if args.status and v.get("status") != args.status:
            continue
        if args.stage and not _in_stage(_stage_works(kind, id_, v), args.stage):
            continue
        if args.group is not None and v.get("group") != args.group:
            continue
        due = due_key(v.get("before"), stages)
        if args.before and not (due is not None and due <= due_key(args.before, stages)):
            continue
        if (args.no_fix and v.get("fix")) or (args.waiting and id_ not in waits):
            continue
        rows.append((id_, v))
    if args.count:
        groups = {}
        for id_, v in rows:
            groups.setdefault(id_.split("-")[0] if kind == "W" else kind, []).append(str(v.get("status", NONE)))
        known = [str(s) for s in (status.values if status else ())]
        order = ids.layout.stages() if kind == "W" else ()
        at = {s: i for i, s in enumerate(order)}
        for group, found in sorted(groups.items(), key=lambda g: (at.get(g[0], len(order)), id_key(g[0] + "-0"))):
            order = known + sorted(set(found) - set(known))
            counts = ", ".join(f"{s} {found.count(s)}" for s in order if s in found)
            print(f"{group}\t{counts} ({len(found)})")
    else:
        main = DECISION_FIELDS if kind in DECISIONS else MAIN_FIELDS.get(kind, ())
        for id_, v in rows:
            fields = " ".join(f"{k}={','.join(map(str, v[k] if isinstance(v[k], list) else [v[k]]))}" for k in main if k in v)
            print(f"{id_}\t{v.get('status', NONE)}\t{fields or NONE}\t{ids.where(id_).title or NONE}")
    print(f"docs list: {len(rows)} of {total} {kind}")
    return 0


def changes_args(p):
    p.add_argument("--since", type=date.fromisoformat, help="decided on this day or after (2026-10-01)")
    p.add_argument("--stage", help="a work of the stage in `tasks`")
    p.add_argument("--section", help="a section in `spec` (`§6` takes `§6.1` too)")


def cmd_changes(args):
    ids = Ids(args.root)
    names = [n for n in DECISIONS if ids.has(n)]
    if not names:
        raise DocsError("the decisions are not in the new layout (no decisions/S/ …)")
    _stage_arg(ids.layout, args.stage)
    if args.section and not re.fullmatch(r"§\d+(?:\.\d+)*", args.section):
        raise DocsError(f"--section {args.section}: not a section (`§6`)")
    rows, undated = [], []
    for id_, _, v in ids.heads(names):
        if v.get("status") != "DECIDED" or (args.stage and not _in_stage(_listed(v.get("tasks")), args.stage)):
            continue
        if args.section and not any(s == args.section or s.startswith(args.section + ".") for s in _listed(v.get("spec"))):
            continue
        if type(v.get("decided")) is not date:
            undated.append(id_)
        elif not args.since or v["decided"] >= args.since:
            rows.append((v["decided"], id_))
    for decided, id_ in sorted(rows, key=lambda r: (-r[0].toordinal(), id_key(r[1]))):
        w = ids.where(id_)
        print(f"{id_}\t{decided.isoformat()}\t{w.spec()}\t{w.title or NONE}")
    for id_ in sorted(undated, key=id_key):
        print(f"note: {id_} is DECIDED with no `decided`")
    print(f"docs changes: {len(rows)} decision(s); {len(undated)} DECIDED with no `decided`")
    return 0


# ---------------------------------------------------------------- set, note, new, draft (DT-3; the new layout)

DEFAULT_STATUS = {"W": "PLAN"}  # the others start OPEN (decisions, issues)
LABELS_HEAD = "## 本文のラベル"  # in a README: the labels of the body of a new file, ``- `空白`: …``
LABEL_ITEM = re.compile(r"- `([^`]+)`")
DRAFT_LABELS = ("決定済みで戻さないもの", "論点", "今の実装", "案", "他言語", "推奨と理由", "影響", "独立のレビュー", "回答")  # DF-4
DRAFT_ORDER = ("group", "drafted")


def today():
    return date.today()


def _refused(command, why):
    """Print why nothing is written; exit 1."""
    for line in why:
        print(line)
    print(f"docs {command}: nothing is written")
    return 1


def _swapped(root, rels):
    """The lines for the files open in vim (`.<name>.sw?`)."""
    return [f"{Path(rel).as_posix()}: the swap file {s[0].name} (open in vim?)"
            for rel in rels if (s := swap_files_of(Path(root) / rel))]  # fmt: skip


def field_value(field, text):
    """A value of KEY=VALUE in the form of the field: `,` divides an array, "" is None (the field is
    removed). A text that is not a date or an integer stays a string, for `check_value` to report."""
    if text == "":
        return None
    items = [s.strip() for s in text.split(",")] if field.many else [text.strip()]
    integer = field.base == "整数" or (field.base == "閉じた値" and isinstance(field.values[0], int))
    out = []
    for s in items:
        try:
            out.append(date.fromisoformat(s) if field.base == "日付" else int(s) if integer else s)
        except ValueError:
            out.append(s)
    return out if field.many else out[0]


def parse_fields(table, items):
    """({key: value or None}, the reasons the values do not fit the field table)."""
    out, why, seen = {}, [], set()
    for item in items:
        key, eq, text = item.partition("=")
        if not eq:
            raise DocsError(f"{item}: not KEY=VALUE")
        field, twice = table.fields.get(key), key in seen
        seen.add(key)
        if twice:
            why.append(f"`{key}` is given twice")
        elif field is None:
            why.append(f"`{key}` is not a field of {table.readme.as_posix()} ({', '.join(table.order)})")
        elif field.many and text and "" in [s.strip() for s in text.split(",")]:
            why.append(f"`{key}` has an empty item: {text}")
        else:
            value = field_value(field, text)
            bad = None if value is None else table.check_value(key, value)
            if bad:
                why.append(bad)
            else:
                out[key] = value
    return out, why


def check_write(root, texts, new=()):
    """The findings, as if `texts` ({rel: text}) were written: (a) and (b) of the head fields of those
    files, (c) of them and of their partners (the files their head fields name, and the files whose
    head fields name them). `new` are (kind, id, rel) of files not there yet."""
    tree = Tree(root, [])
    for rel, text in texts.items():
        tree._lines[Path(rel)] = text.split("\n")
    for name, id_, rel in new:
        tree.index.files[name][id_] = Path(rel)
    written = {Path(r) for r in texts}
    rel_of = {i: r for files in tree.index.files.values() for i, r in files.items()}
    own = {i for i, r in rel_of.items() if r in written}
    partners = set()
    for _, _, rel, _ in _id_files(tree):
        named = {i for _, i in named_ids(tree, rel, text=False)}
        if rel in written:
            partners |= {rel_of[i] for i in named if i in rel_of}
        elif named & own:
            partners.add(rel)
    found = [f for f in check_heads(tree) if f.path in written]
    heads = {rel: tree.head(rel) for rel in written}
    ends = {rel: len(tree.lines(rel)) - len(h.body.split("\n")) for rel, h in heads.items() if h.values is not None}
    found += [f for f in check_refs(tree, written) if f.line <= ends.get(f.path, 0)]  # the head fields, not the text
    return found + [f for f in check_relations(tree) if f.path in written | partners]


def write_new(path, text):
    """Create a file (never over one that is there)."""
    try:
        with open(path, "x", encoding="utf-8", newline="") as f:
            f.write(text)
    except OSError as e:
        raise DocsError(f"{path}: {e}") from e


def _found(ids, id_):
    w = ids.where(id_)
    if w.rel is None:
        print(f"{id_}: {w.place()}")
    return w


def set_args(p):
    p.add_argument("id")
    p.add_argument("fields", nargs="+", metavar="KEY=VALUE", help="`,` divides an array; `KEY=` removes the field")


def cmd_set(args):
    ids = Ids(args.root)
    kind = ids.require(_id_arg(args.id))
    table, w = ids.table(kind.name), _found(ids, args.id)
    if w.rel is None:
        return 1
    if swapped := _swapped(ids.root, [w.rel]):
        return _refused("set", swapped)
    changes, why = parse_fields(table, args.fields)
    if why:
        return _refused("set", why)
    text = head_update(ids.root, w.rel, {**w.values, **changes}, table.order)
    if found := check_write(ids.root, {w.rel: text}):
        return _refused("set", map(str, found))
    write_atomic(ids.root / w.rel, text)
    shown = [f"{k} = {toml_value(v)}" if v is not None else f"{k} removed" for k, v in changes.items()]
    print(f"{w.rel.as_posix()}: {'; '.join(shown)}")
    return 0


def note_args(p):
    p.add_argument("id")
    p.add_argument("label", help="判断, 保留, 補い, …")
    p.add_argument("text")
    p.add_argument("--by", default="親", help="the writer (default: 親)")


def cmd_note(args):
    ids = Ids(args.root)
    ids.require(_id_arg(args.id))
    w = _found(ids, args.id)
    if w.rel is None:
        return 1
    if any("\n" in s or not s.strip() for s in (args.label, args.text, args.by)):
        return _refused("note", ["the label, the text and the writer are each one line, not empty"])
    if swapped := _swapped(ids.root, [w.rel]):
        return _refused("note", swapped)
    text = read_doc(ids.root, w.rel)
    if "\r" in text:
        raise DocsError(f"{w.rel}: it has CR line ends; nothing is written")
    line = f"- {args.label}（{today().isoformat()}、{args.by}）: {args.text}"
    write_atomic(ids.root / w.rel, text + ("" if text.endswith("\n") else "\n") + line + "\n")
    print(f"{w.rel.as_posix()}: {line}")
    return 0


def new_args(p):
    p.add_argument("kind")
    p.add_argument("fields", nargs="*", metavar="KEY=VALUE")
    p.add_argument("--title")
    p.add_argument("--stage", help="W: the stage of the new work (`W4`)")


def next_id(root, kind, stage):
    """The next number of a kind: the largest of its files and drafts + 1 (W: in the stage)."""
    if (kind.name == "W") != bool(stage):
        raise DocsError("new W takes --stage (`W4`); the other kinds do not")
    if stage and not re.fullmatch(repo.KIND["W"].pattern, f"{stage}-1"):
        raise DocsError(f"{stage}: not a stage of W (`W4`)")
    prefix = stage or kind.name
    pattern = re.compile(re.escape(prefix) + r"-(\d+)(?:\.draft)?\.md")
    numbers = [int(m.group(1)) for p in (Path(root) / kind.dir).iterdir() if (m := pattern.fullmatch(p.name))]
    n = max(numbers, default=0) + 1
    return f"{prefix}-{n:02d}" if stage else f"{prefix}-{n}"


def body_labels(tree, kind):
    """The labels of the body of a new file: the items ``- `<label>` …`` under LABELS_HEAD in the README
    of the kind's directory, else of the one up (as `field_table`); none when neither has it."""
    d = Path(kind.dir)
    for rel in (d / "README.md", d.parent / "README.md"):
        if (tree.root / rel).is_file():
            lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
            at = next((i for i, line in enumerate(lines) if line == LABELS_HEAD and kinds[i] == TEXT), None)
            if at is not None:
                end = next((i for i in range(at + 1, len(lines)) if lines[i].startswith("#")), len(lines))
                return [m.group(1) for line in lines[at + 1 : end] if (m := LABEL_ITEM.match(line))]
    return []


def _labels(labels):
    return "".join(["\n", *(f"- {label}:\n" for label in labels)]) if labels else ""


def cmd_new(args):
    root = Path(args.root)
    if repo.tree_kind(root) == "worktree":
        raise DocsError("the numbers are given in the main tree only (this is a git worktree; write NEW)")
    ids = Ids(root)
    kind = ids.require(args.kind)
    table = ids.table(kind.name)
    id_ = next_id(root, kind, _stage_arg(ids.layout, args.stage))
    values, why = parse_fields(table, args.fields)
    if args.title is not None and ("\n" in args.title or not args.title.strip()):
        why.append("the title is one line, not empty")
    if why:
        return _refused("new", why)
    values = {k: v for k, v in values.items() if v is not None}
    if "status" in table.fields:
        values.setdefault("status", DEFAULT_STATUS.get(kind.name, "OPEN"))
    rel = repo.path_of(id_)
    missing = [f"the field `{k}` is required ({table.readme.as_posix()})"
               for k in table.order if table.fields[k].required and k not in values]  # fmt: skip
    if missing:
        return _refused("new", missing)
    heading = f"# {id_}" + (f" {args.title.strip()}" if args.title else "") + "\n"
    text = render_head(values, table.order) + heading + _labels(body_labels(ids.tree, kind))
    if found := check_write(root, {rel: text}, [(kind.name, id_, rel)]):
        return _refused("new", map(str, found))
    if swapped := _swapped(root, [rel]):
        return _refused("new", swapped)
    write_new(root / rel, text)
    print(rel.as_posix())
    return 0


def draft_args(p):
    p.add_argument("ids", nargs="+", metavar="S")
    p.add_argument("--group", type=int, required=True)


def cmd_draft(args):
    ids, plan, why = Ids(args.root), [], []
    ids.require("S")
    for id_ in dict.fromkeys(args.ids):
        ids.require(_id_arg(id_), ["S"])
        w, rel = ids.where(id_), repo.path_of(id_, draft=True)
        if w.rel is None:
            why.append(f"{id_}: {w.place()}")
        elif (ids.root / rel).exists():
            print(f"{rel.as_posix()}: there already; not written")
        else:
            why += _swapped(ids.root, [rel])
            head = render_head({"group": args.group, "drafted": today()}, DRAFT_ORDER)
            title = heading_title(id_, ids.tree.head(w.rel))
            plan.append((rel, head + f"# {id_}" + (f" {title}" if title else "") + "\n" + _labels(DRAFT_LABELS)))
    if why:
        return _refused("draft", why)
    for rel, text in plan:
        write_new(ids.root / rel, text)
        print(rel.as_posix())
    return 0


# ---------------------------------------------------------------- ticket (DT-6, DF-6)

UNIT_ROLE = re.compile(r"[^/\s]+/[tib](?:-fix\d+)?")
CARRIED = re.compile(r"- 持ち越し[:：]")
# the fields of a ticket the parent fills (DF-6)
TICKET_FIELDS = ("する", "しない", "書く場所", "読むもの", "期待値", "危険な経路", "進め方", "見積もり", "予算", "受け入れ条件",
                 "使う番号が登録済みか")  # fmt: skip


def ticket_args(p):
    p.add_argument("id", metavar="W")
    p.add_argument("unit", metavar="UNIT/ROLE", help="`U2/i`, `U1/t`, `U2/i-fix1`")
    p.add_argument("--out", help="write it to this new file instead")


def cmd_ticket(args):
    ids = Ids(args.root)
    ids.require(_id_arg(args.id), ["W"])
    if not UNIT_ROLE.fullmatch(args.unit):
        raise DocsError(f"{args.unit}: not UNIT/ROLE (`U2/i`; the roles t, i, b)")
    w = _found(ids, args.id)
    if w.rel is None:
        return 1
    v, head = w.values, ids.tree.head(w.rel)
    decisions, issues = ids.having(DECISIONS, "tasks", w.id), ids.having(ISSUES, "fix", w.id)
    secs = {s for i in decisions + issues for s in _listed(ids.where(i).values.get("spec"))}
    depends = "、".join(f"{d}（{ids.state(d)}）" for d in _listed(v.get("depends")))
    doing = ", ".join(_listed(v.get("doing")))

    def item(i):
        x = ids.where(i)
        return f"\n  - {i} {x.status} {x.title or NONE}" + (f"（{x.spec()}）" if x.spec() != NONE else "")

    out = [
        f"# 作業 {w.id} {args.unit}: {w.title or NONE}", "",
        f"- 作業のファイル: {w.rel.as_posix()}（`docs.py show {w.id}`）",
        f"- 状態: {w.status}" + (f"（doing: {doing}）" if doing else ""),
        f"- 規模: {v.get('size', NONE)}",
        f"- 依存: {depends or 'なし'}",
        "- 実現する決定:" + ("".join(map(item, decisions)) or " なし"),
        "- 直す R:" + ("".join(map(item, issues)) or " なし"),
        f"- 仕様の節: {'、'.join(sorted(secs, key=section_key)) or 'なし'}",
        "- 持ち越し: " + ("作業のファイルの `持ち越し` を読む" if any(CARRIED.match(x) for x in head.body.split("\n")) else "なし"),
        f"- 役割と単位: {args.unit}",
        *(f"- {f}:" for f in TICKET_FIELDS),
    ]  # fmt: skip
    text = "\n".join(out) + "\n"
    if args.out:
        if Path(args.out).exists():
            return _refused("ticket", [f"{args.out}: there already"])
        write_new(Path(args.out), text)
        print(args.out)
    else:
        print(text, end="")
    return 0


# ---------------------------------------------------------------- the subcommands

EDITORS = ("parent", "i", "docs")  # the roles that edit the documents (the help of `fmt`, `swaps`, `check`, the writes)
C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "fmt": C(fmt_args, cmd_fmt, EDITORS, "長い行を「。」の後で折る（`--check` は書かずに確かめる）",
             "文書を編集した後に、`docs.py fmt <ファイル>` で行を整える", "docs.py fmt rules/process.md"),
    "swaps": C(lambda p: None, cmd_swaps, EDITORS, "vim のスワップファイル（`.<name>.sw?`）を並べる",
               "文書を編集する前に、スワップファイルが無いことを確かめる。確かめは、編集と別のコマンドで行う"
               "（`.claude/agents/` は見ないので、定義を開いているかは利用者に聞く）", "docs.py swaps"),
    "check": C(lambda p: None, cmd_check, EDITORS, "文書の表・頭の欄・ID と § の参照・関係・README のリンクを確かめる（gate の `docs`）",
               "文書を編集した後に、`fmt` で行を整えてから通す。文書の点検の担当は始めに回し、落ちていれば、その出力を報告して止める",
               "docs.py check"),
    "due": C(lambda p: p.add_argument("--stage-end", metavar="STAGE"), cmd_due, ("parent",),
             "最後の文書の点検（`Docs-Checked:` の行）から改めた文書を並べる（gate の `docs-due`）",
             "規則・仕様・担当の定義・README を改めた後と段の終わりに、文書の点検（onsa-docs）を呼ぶかを見る"
             "（gate の `docs-due` と同じ。段の終わりは `--stage-end`）", "docs.py due"),
    "path": C(path_args, cmd_path, ("parent", "docs"), "ID のファイルか、§ の見出しの場所を出す",
              "作業票に書く ID が登録済みかを確かめるとき（`docs.py path <ID>` で引ける）。ID や § の経路を引くとき",
              "docs.py path S-537 §6.1 --abs"),
    "back": C(back_args, cmd_back, ("parent", "docs"), "ID を名指す頭の欄と本文の行を逆引きする",
              "ID を名指す所を逆引きするとき（`--history` で `history/` も）", "docs.py back S-537"),
    "refs": C(refs_args, cmd_refs, ("parent", "docs"), "ID のファイルか文書が名指す ID を、状態・場所・題と並べる",
              "ファイルが名指す ID の状態と場所を一度に見るとき", "docs.py refs W3-05"),
    "graph": C(graph_args, cmd_graph, ("parent",), "決定の関係を、その場で作ったグラフで出す（`--back` はその上に立つもの）",
               "下書きを確かめる段で、前の決定、付録、登録済みの R と重なる部分を探すとき（`--back`、その決定の上に立つもの）。"
               "決定が変わったときに見直すものを探すとき", "docs.py graph S-239 --back --typed --depth 2"),
    "show": C(show_args, cmd_show, tuple(repo.ROLES), "ID のファイルを読む（`--relations` は頭の欄と関係だけ）",
              "ID のファイルを読むとき（作業票の「実現する決定」と「直す R」の原文など）", "docs.py show S-537 --relations"),
    "list": C(list_args, cmd_list, ("parent",), "種類ごとの ID を、状態・段・組などで絞って並べる",
              "決定の一覧を見るとき（別に書かない）。下書きの組の一覧は `list S --group <N>`", "docs.py list S --status OPEN --count"),
    "changes": C(changes_args, cmd_changes, ("parent",), "決めた日・段・節で絞って、決定の変更点を並べる",
                 "決定の変更点を見るとき（別に書かない）。下書きを確かめる段で、その節の決定を探すとき（`--section <§>`）",
                 "docs.py changes --section §6"),
    "set": C(set_args, cmd_set, EDITORS, "ID のファイルの頭の欄を書く（`KEY=` は欄を消す）",
             "ID のファイルの頭の欄を書くとき（作業のコミットと同じ回に `status=DONE`、決定の反映で "
             "`status=DECIDED decided=<日付>`）", "docs.py set W1-01 status=DONE"),
    "note": C(note_args, cmd_note, EDITORS, "ID のファイルの本文に補いの項目を足す",
              "ID のファイルの本文に補いを書くとき（決定の反映で、関係する R の `判断`・`反映`）",
              "docs.py note R-12 反映 \"W3-05 で直した\""),
    "new": C(new_args, cmd_new, ("parent",), "次の番号で ID のファイルを作る（主のツリーだけ）",
             "S・R などの ID を登録するとき。S は、空白の報告を受け取った回に主のツリーで登録する"
             "（期限の作業か段を `before`、見つけた票を `found_by`）",
             "docs.py new S --title \"…\" before=W4 found_by=W3-05/t"),
    "draft": C(draft_args, cmd_draft, ("parent",), "S の下書き（`S-<番号>.draft.md`、頭の欄 `group`・`drafted`）を作る",
               "確かめた空白の組を下書きに置くとき", "docs.py draft S-537 S-538 --group 12"),
    "ticket": C(ticket_args, cmd_ticket, ("parent",), "作業のファイルと決定から、作業票の骨組みを出す",
                "作業票を書くとき（親は残りの欄を埋める）", "docs.py ticket W3-05 U2/i"),
}  # fmt: skip


def main(argv=None):
    args = repo.parse_command("docs.py", __doc__.split("\n")[0], COMMANDS, argv,
                              lambda p: p.add_argument("--root", type=Path, default=ROOT))  # fmt: skip
    try:
        return args.run_(args)
    except (DocsError, repo.RepoError) as e:
        print(f"docs.py {args.cmd}: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
