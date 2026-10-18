#!/usr/bin/env python3
"""The marks of spec gaps in the code (Q-10, rules/process.md 8.2 3).

A worker who meets a gap of the spec implements the most conservative form and
marks the place:

    // SPEC-GAP(S-123): <what the spec does not say>     (Rust, C, Onsa)
    # SPEC-GAP(R-45): <...>                               (Python, shell, TOML)

The ID is a registered number: S (`decisions/S/`), R (`issues/R/`) or A
(`decisions/A/`). This check scans `SCANNED` and fails on a mark
without an ID or of another form, on an ID no table has, and on `NEW` (the
parent registers the gap and writes its number before the commit).

    tools/gap_marks.py [--root DIR]

Exit 0 when every mark is well formed and registered, 1 otherwise. In a git
worktree of a worker (`repo.tree_kind`), `NEW` and an ID no table has wait for
the parent, who registers the gap: when they are all that is left, they are
listed as `parent: ...` and the exit is `gate_steps.PARENT` (3; the gate shows
PARENT and does not fail). A malformed mark fails everywhere: the worker fixes it.

A mark that names an S whose `status` is DROPPED is told as `parent: ...` (PARENT)
in every tree, and never fails: the S is dropped in the commit of the decision and
the mark is fixed in a commit of the code, so failing would stop that order.
"""
import argparse
import os
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import docs as docs_tool  # noqa: E402
import gate_steps  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
SCANNED = ("crates", "std", "runtime", "tools")

TOKEN = "SPEC-GAP"
# Any spelling of the token (`spec-gap`, `SPECGAP`, `Spec gap`, `SPEC_GAP`): a
# line with one is a mark, and must be of the one form.
SPELLING = re.compile(r"spec[\s_-]*gap", re.I)
# The files that write the form as data (this check and its self-tests); they hold no mark.
OWN = ("tools/gap_marks.py", "tools/test_gate.py")
HASH_COMMENT = {".py", ".sh", ".toml"}  # `#` comments; every other file uses `//`
ID = repo.id_form("S", "R", "A")


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
    """The A numbers: the files of `decisions/A/` (`docs.Index`)."""
    return docs_tool.Index.of(root).ids("A")


def dropped_ids(index):
    """The S whose head field `status` is DROPPED (`index`: a `docs.Index`)."""
    heads = {i: index.tree.head(rel).values or {} for i, rel in index.files.get("S", {}).items()}
    return {i for i, v in heads.items() if v.get("status") == "DROPPED"}


def mark_id(path, text):
    """The ID of a well-formed mark, or None."""
    m = FORMS[leader_of(path)].search(text)
    return m.group("id") if m and len(SPELLING.findall(text)) == 1 else None


def on_dropped(marks, dropped, at):
    """The well-formed marks that name a dropped S (`at`: where the S are read, for messages)."""
    return [f"{path}:{line}: {mid} is DROPPED in {at}; point the mark to the decision that replaced it, or remove it"
            for path, line, text in marks if (mid := mark_id(path, text)) in dropped]  # fmt: skip


def check(marks, known, known_at):
    """The marks against the known IDs (`known_at`: where they are read, for messages): (problems, what
    waits for the parent: `NEW` and the IDs that are not there)."""
    problems, for_parent = [], []
    for path, line, text in marks:
        where = f"{path}:{line}"
        mid = mark_id(path, text)
        if mid is None:
            leader = leader_of(path)
            problems.append(
                f"{where}: a malformed {TOKEN} mark; write `{leader} {TOKEN}(<S / R / A number>): <what is missing>` "
                "(if this is not a mark, avoid spellings like `spec_gap` or `spec gap`)"
            )
            continue
        if mid == "NEW":
            for_parent.append(f"{where}: {TOKEN}(NEW): report it; the parent registers the gap and writes its number")
        elif not ID.fullmatch(mid):
            problems.append(f"{where}: `{mid}` is not an S / R / A number")
        elif mid not in known:
            for_parent.append(f"{where}: {mid} is not in {known_at}")
    return problems, for_parent


def main(argv=None, root=ROOT):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=None)
    args = ap.parse_args(argv)
    root = args.root or root
    try:
        docs, index = pending.load_docs(root), docs_tool.Index.of(root)
        known, known_at = docs.reasons | api_ids(root), f"{docs.reasons_at}, {index.place('A')}"
        dropped = dropped_ids(index)
    except repo.RepoError as e:
        print(f"cannot read the IDs: {e}")
        return 1
    marks = find_marks(root)
    problems, for_parent = check(marks, known, known_at)
    if repo.tree_kind(root) != "worktree":  # the main tree and the made-up roots: the parent registers now
        problems, for_parent = problems + for_parent, []
    told = on_dropped(marks, dropped, index.place("S"))  # told in every tree, never failed
    for p in problems:
        print(p)
    for p in for_parent + told:
        print(f"parent: {p}")
    left = [f"{len(problems)} problem(s)"] if problems else []
    left += [f"{len(for_parent)} for the parent to register"] if for_parent else []
    left += [f"{len(told)} naming a dropped S"] if told else []
    print(f"{len(marks)} {TOKEN} mark(s) in {', '.join(SCANNED)}; " + ("; ".join(left) or "all registered"))
    return 1 if problems else gate_steps.PARENT if for_parent or told else 0


if __name__ == "__main__":
    sys.exit(main())
