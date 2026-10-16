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
  `path:line: what` under a heading per check. To add a check, add `(name, fn(tree) -> Findings)`
  to CHECKS; to add a subcommand, add `name: (add_arguments, run)` to COMMANDS.
"""
import argparse
import fnmatch
import os
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import repo

ROOT = repo.ROOT


class DocsError(Exception):
    """An error of the tool: exit 2."""


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
        return f"{Path(self.path).as_posix()}:{self.line}: {self.message}"


class Tree:
    """One reading of the documents, shared by the checks."""

    def __init__(self, root, files):
        self.root, self.files = Path(root), list(files)
        self._lines, self._kinds = {}, {}

    def lines(self, rel):
        if rel not in self._lines:
            self._lines[rel] = read_doc(self.root, rel).split("\n")
        return self._lines[rel]

    def kinds(self, rel):
        """(the kind of each line, the index of a code fence left open or None): `line_kinds`."""
        if rel not in self._kinds:
            self._kinds[rel] = line_kinds(self.lines(rel))
        return self._kinds[rel]


DELIMITER = re.compile(r"\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?")


def cell_count(row):
    """The cells of a table row: `\\|` and a `|` in a code span do not divide."""
    s = row.strip()
    bars = [i for i in _plain(s) if s[i] == "|"]
    return len(bars) + 1 - (bars[:1] == [0]) - (len(s) > 1 and bars[-1:] == [len(s) - 1])


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


CHECKS = [("tables", check_tables)]


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
