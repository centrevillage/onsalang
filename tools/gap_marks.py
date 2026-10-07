#!/usr/bin/env python3
"""The marks of spec gaps in the code (Q-10, plan §8.2 3).

A worker who meets a gap of the spec implements the most conservative form and
marks the place:

    // SPEC-GAP(S-123): <what the spec does not say>     (Rust, C, Onsa)
    # SPEC-GAP(R-45): <...>                               (Python, shell, TOML)

The ID is a registered number: S (plan §2), R (review §8) or A
(`docs/api-candidates.md`). This check scans `SCANNED` and fails on a mark
without an ID or of another form, on an ID no table has, and on `NEW` (the
parent registers the gap and writes its number before the commit).

    tools/gap_marks.py [--root DIR]

Exit 0 when every mark is well formed and registered, 1 otherwise.
"""
import argparse
import os
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
SCANNED = ("crates", "std", "runtime", "tools")
DOC_API = repo.DOC_API

TOKEN = "SPEC-GAP"
# Any spelling of the token (`spec-gap`, `SPECGAP`, `Spec gap`, `SPEC_GAP`): a
# line with one is a mark, and must be of the one form.
SPELLING = re.compile(r"spec[\s_-]*gap", re.I)
# The files that write the form as data (this check and its self-tests); they hold no mark.
OWN = ("tools/gap_marks.py", "tools/test_gate.py")
HASH_COMMENT = {".py", ".sh", ".toml"}  # `#` comments; every other file uses `//`
ID = re.compile(r"[SRA]-\d+")


def mark_form(leader):
    # The leader starts the comment: at the line start or after whitespace,
    # and `//` is not part of `///` or `//!`.
    lead = re.escape(leader)
    before = r"(?:^|(?<=\s))" + (r"(?<!/)" if leader == "//" else "")
    return re.compile(before + lead + " " + TOKEN + r"\((?P<id>[^()\s]+)\): (?P<text>\S.*)$")


FORMS = {"//": mark_form("//"), "#": mark_form("#")}


def leader_of(path):
    return "#" if Path(path).suffix in HASH_COMMENT else "//"


def find_marks(root, dirs=SCANNED):
    """Every line holding a spelling of the token: [(path, line number, line)].
    The build outputs (`repo.is_build_output`) are not scanned."""
    out = []
    for d in dirs:
        base = root / d
        if not base.is_dir():
            continue
        for here, subdirs, files in os.walk(base):
            rel_here = Path(here).relative_to(root).as_posix()
            subdirs[:] = sorted(x for x in subdirs if not repo.is_build_output(root, f"{rel_here}/{x}"))
            for name in sorted(files):
                rel = f"{rel_here}/{name}"
                if rel in OWN:
                    continue
                try:
                    text = (root / rel).read_text(encoding="utf-8")
                except (UnicodeDecodeError, OSError):
                    continue  # not a text file
                if not SPELLING.search(text):
                    continue
                for i, line in enumerate(text.split("\n"), 1):
                    if SPELLING.search(line):
                        out.append((rel, i, line))
    return out


def api_ids(root):
    """The A numbers of the table of `docs/api-candidates.md`."""
    rows = repo.rows(repo.read(root, DOC_API), r"A-\d+")
    if not rows:
        raise repo.RepoError(f"{DOC_API}: no table rows of A numbers found")
    return set(rows)


def check(marks, known):
    """Problems of the marks against the known IDs."""
    problems = []
    for path, line, text in marks:
        where = f"{path}:{line}"
        leader = leader_of(path)
        m = FORMS[leader].search(text)
        if not m or len(SPELLING.findall(text)) != 1:
            problems.append(
                f"{where}: a malformed {TOKEN} mark; write `{leader} {TOKEN}(<S / R / A number>): <what is missing>` "
                "(if this is not a mark, avoid spellings like `spec_gap` or `spec gap`)"
            )
            continue
        mid = m.group("id")
        if mid == "NEW":
            problems.append(f"{where}: {TOKEN}(NEW): report it; the parent registers the gap and writes its number")
        elif not ID.fullmatch(mid):
            problems.append(f"{where}: `{mid}` is not an S / R / A number")
        elif mid not in known:
            problems.append(f"{where}: {mid} is not in the tables (plan §2 for S, review for R, {DOC_API} for A)")
    return problems


def main(argv=None, root=ROOT):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=None)
    args = ap.parse_args(argv)
    root = args.root or root
    try:
        known = pending.load_docs(root).reasons | api_ids(root)
    except repo.RepoError as e:
        print(f"the document tables are not found: {e}")
        return 1
    marks = find_marks(root)
    problems = check(marks, known)
    for p in problems:
        print(p)
    print(f"{len(marks)} {TOKEN} mark(s) in {', '.join(SCANNED)}; " + (f"{len(problems)} problem(s)" if problems else "all registered"))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
