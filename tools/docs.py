#!/usr/bin/env python3
"""The tool of the documents (X-2 DT-0): one tool, one subcommand per job.

    python3 -B tools/docs.py fmt [PATH...] [--check | --list] [--spec] [--root DIR]
    python3 -B tools/docs.py swaps [--root DIR]
    python3 -B tools/docs.py check [--root DIR]

Exit: 0 nothing found, 1 found, 2 an error of the tool (a file it cannot read, no document, a
broken round trip of `fmt`; argparse's usage errors too). The documents are `repo.doc_files`.

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
- `check` (DT-5, the gate's `docs`): the checks of CHECKS on one reading of the documents (`Tree`),
  `path:line: what` under a heading per check: (d) `tables`, and on the files of the IDs of the new
  layout (`Index`; `history/` and `tests/pending.toml` are not read) (a) `heads` (the field table of
  the directory's README, the head fields against it, the heading), (b) `refs` (the IDs and the `§`
  are there), (c) `relations` (the keys named in `check_relations`), and (e) `links` (the relative
  links of the READMEs). To add a check, add `(name, fn(tree) -> Findings)` to CHECKS; to add a
  subcommand, add `name: (add_arguments, run)` to COMMANDS.

The head fields (DF-1) are read by `read_head` and written in the normal form by `head_update` /
`write_head` (U3's `set` and `amend`); the field table of a directory is `field_table`.
"""
import argparse
import fnmatch
import os
import re
import shutil
import sys
import tempfile
import tomllib
from dataclasses import dataclass
from datetime import date
from pathlib import Path

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


def _plain(text):
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


# ---------------------------------------------------------------- fmt

LONG = 250  # the lines longer than this are broken
WIDTH = 200  # the characters of a line after its indentation
OPEN = "（(「『【"
CLOSE = "）)」』】"
KEEP = ("|", "#", repo.RETIRED_HEAD)  # table rows, headings, the retired codes of the plan §5
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
    """`head_update` and write it (U3's `set`; `amend` calls `head_update` on both files first)."""
    write_atomic(Path(root) / rel, head_update(root, rel, values, order))


# ---------------------------------------------------------------- the field tables of the READMEs (X-2 DT-1, DT-B)

FIELDS_HEAD = "## 頭の欄"
FIELD_COLUMNS = ["キー", "形", "値", "要る", "意味"]
# `<base>` or `<base>の並び` (an array); the IDs name their kinds: `ID（S）`, `ID の並び（W、T、P2）`.
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


def table_cells(row):
    """The cells of a table row, stripped: `\\|` and a `|` in a code span do not divide."""
    s = row.strip()
    bars = [i for i in _plain(s) if s[i] == "|"]
    cells = [s[a + 1 : b] for a, b in zip([-1, *bars], [*bars, len(s)])]
    if bars[:1] == [0]:
        cells = cells[1:]
    if len(s) > 1 and bars[-1:] == [len(s) - 1]:
        cells = cells[:-1]
    return [c.strip() for c in cells]


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
        if any(k not in repo.KIND for k in kinds_):
            return broken(j, f"the form `{form}` names a kind that is not one ({', '.join(repo.KIND)})")
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
    """The files of the IDs of the new layout over one Tree, the kinds read by `repo.Layout`."""

    def __init__(self, tree):
        self.tree, self.layout = tree, repo.Layout(tree.root)
        self.files, self.misnamed, self._tables, self._done, self._headings = {}, {}, {}, None, {}
        for kind in repo.KINDS:
            if kind.dir and self.layout.source(kind.name) == "new":
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

    def ids(self, name):
        """The IDs of a kind: the files (a draft is not one, DF-4), or the current table."""
        if self.layout.source(name) == "new":
            if not self.files[name]:
                raise repo.RepoError(f"{repo.KIND[name].dir}/: no file of an ID")
            return set(self.files[name])
        return set(self.layout.old_rows(name))

    def known(self, name):
        """The IDs of a kind there are, or None when they are not checked (the history, P2, no reader)."""
        if repo.KIND[name].dir is None or self.layout.source(name) is None:
            return None
        return set(self.files[name]) if self.layout.source(name) == "new" else set(self.layout.old_rows(name))

    def work_done(self):
        """{W: done}: `status = "DONE"` in the new layout, ✅ in the current table (one place, D-15)."""
        if self._done is None:
            if self.layout.source("W") == "new":
                heads = {w: self.tree.head(rel).values or {} for w, rel in self.files["W"].items()}
                self._done = {w: v.get("status") == "DONE" for w, v in heads.items()}
            else:
                self._done = self.layout.old_rows("W")
        return self._done

    def headings(self, which):
        """The numbered headings of the spec (`spec`) or of the spec of the tools (`tools`)."""
        if which not in self._headings:
            doc = repo.spec_doc(self.tree.root, self.layout) if which == "spec" else repo.tools_doc(self.tree.root)
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


def check_refs(tree):
    """(b) The IDs of the head fields and of the text are there (the kinds as `repo.Layout` reads them;
    the history and P2 are not checked), and the sections are numbered headings of the spec."""
    idx = tree.index
    for table, id_, rel, head in _id_files(tree):
        if head.values is None:
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
    """Why a reference is not found, or None."""
    if which:
        if ref in idx.headings(which):
            return None
        return f"{'tools.md ' if which == 'tools' else ''}§{ref} is not a numbered heading of the spec" + (
            " of the tools" if which == "tools" else ""
        )
    kind = repo.kind_of(ref)
    known = idx.known(kind.name)
    if known is None or ref in known:
        return None
    where = f"{kind.dir}/" if idx.layout.source(kind.name) == "new" else idx.layout.old_name(kind.name)
    return f"{ref} is not found ({where})"


def check_relations(tree):
    """(c) The relations the fields keep (the keys are named here, DT-1): a decision OPEN when every
    work of `tasks` is DONE, an issue OPEN when every work of `fix` is DONE, `amends` and `amended_by`
    on both sides, `doing` on a work that is not DOING. A missing ID is (b)'s."""
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
        for key, back in (("amends", "amended_by"), ("amended_by", "amends")):
            for other in v.get(key) if isinstance(v.get(key), list) else []:
                kind = repo.kind_of(other) if isinstance(other, str) else None
                orel = idx.files.get(kind.name, {}).get(other) if kind else None
                theirs = tree.head(orel).values if orel else None
                if theirs is not None and id_ not in (theirs.get(back) if isinstance(theirs.get(back), list) else []):
                    yield Finding(rel, line(key, 1), f"`{key}` has {other}, but {other} has no {id_} in `{back}`")
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


# ---------------------------------------------------------------- the subcommands

COMMANDS = {
    "fmt": (fmt_args, cmd_fmt),
    "swaps": (lambda p: None, cmd_swaps),
    "check": (lambda p: None, cmd_check),
}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="docs.py", description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, (add_arguments, _) in COMMANDS.items():
        p = sub.add_parser(name)
        p.add_argument("--root", type=Path, default=ROOT)
        add_arguments(p)
    args = ap.parse_args(argv)
    try:
        return COMMANDS[args.cmd][1](args)
    except (DocsError, repo.RepoError) as e:
        print(f"docs.py {args.cmd}: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
