#!/usr/bin/env python3
"""The documents write the `init` of a delay in the omitted form (spec §11.4, S-539 (c3a)).

`onsa fmt` keeps an `init` equal to the default value (the literal may decide
the type), so the omitted form of the documents rests on the writer: this
check fails when a delay call (`prev~`, `delay~`, `vdelay~`) in them has an
`init` that is a literal of the default value (0 in any spelling of §2.4, the
integer `-0`, `+0.0`, `false`, also in parentheses; not `-0.0`).

The documents are the ```onsa blocks of the spec and of `spec/tools.md`,
and the `.onsa` files of `examples/` and `std/`. The text of the documents
outside the blocks is not read: it names the written form on purpose (§11.4,
`spec/tools.md` §3.3). The records (plan §2, the drafts of the gaps)
are not documents.

The calls and the values are the compiler's (`onsa_cases --default-inits`,
`onsa_tests::default_inits`): this tool only gathers the sources and reports.
It also fails when it reads nothing (no block of the spec, no file of
`examples/` and `std/`, no delay call at all), when a fence cannot be trusted,
when the compiler cannot read a source, and when it cannot read every call:
- a source whose tokens show more delay calls than its tree (the tree has no
  item with a syntax error, so a call there would pass unread);
- a file of `examples/` or `std/` with a diagnostic of the syntax stage (they
  are files without errors; a block of the spec may be a negative example,
  so only the count above applies to it).

Usage: tools/default_inits.py
Exit 0 if no document writes such an `init`, 1 otherwise.
"""
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402
import spec_blocks  # noqa: E402

TOOLS_DOC = repo.DOC_TOOLS  # the current spec of the tools (`repo.tools_doc` reads it or spec/tools.md)
FILE_DIRS = ("examples", "std")


class Source:
    """A text to read: a block of a document (`first` is its first line there) or a file."""

    def __init__(self, shown, text, first=1, whole=False):
        # whole: a file that has no error (examples/, std/), not a block that may be a negative example
        self.shown, self.text, self.first, self.whole = shown, text, first, whole


def sources(root):
    """(sources, counts, problems)."""
    out, counts, problems = [], {}, []
    for doc in (repo.spec_doc(root), repo.tools_doc(root)):
        blocks, errors = spec_blocks.scan(doc.text)
        problems += [f"{doc.where(line)}  {m}" for line, m in errors]
        for b in blocks:
            rel, first = doc.locate(b.line)
            out.append(Source(Path(rel).as_posix(), b.code, first))
        counts[f"{_name(doc)} blocks"] = len(blocks)
    for d in FILE_DIRS:
        files = [
            p
            for p in sorted((Path(root) / d).rglob("*.onsa"))
            if not repo.is_build_output(root, p.relative_to(root).as_posix())
        ]
        out += [Source(p.relative_to(root).as_posix(), repo.read(root, p.relative_to(root)), whole=True) for p in files]
        counts[f"{d} files"] = len(files)
    for what in (next(iter(counts)), *(f"{d} files" for d in FILE_DIRS)):  # the spec's blocks first
        if counts[what] == 0:
            problems.append(f"no {what} to read; the check would pass reading nothing")
    return out, counts, problems


def _name(doc):
    """A document in the counts: its file, or `spec/` when it is joined from the chapters."""
    return Path(doc.parts[0][0]).as_posix() if len(doc.parts) == 1 else f"{repo.SPEC_DIR}/"


def check(root=repo.ROOT, cmd=repo.CASES_CMD):
    """Return (problems, summary)."""
    srcs, counts, problems = sources(root)
    with tempfile.TemporaryDirectory(prefix="onsa-default-inits-") as tmp:
        paths = []
        for i, s in enumerate(srcs):
            p = Path(tmp) / f"{i:05d}.onsa"
            p.write_text(s.text, encoding="utf-8")
            paths.append(str(p))
        reports = repo.cases_json(root, cmd, "--default-inits", *paths) if paths else []
    by_file = {r.get("file"): r for r in reports}
    calls = 0
    for s, p in zip(srcs, paths):
        r = by_file.get(p)
        if r is None or not {"calls", "lexed", "syntax_errors", "hits"} <= r.keys():
            why = "no report" if r is None else r.get("unreadable") or r.get("internal")
            problems.append(f"{s.shown}:{s.first}  the compiler could not read it: {why}")
            continue
        calls += r["calls"]
        where = f"{s.shown}:{s.first}"
        if r["lexed"] > r["calls"]:
            problems.append(
                f"{where}  {r['lexed'] - r['calls']} of its {r['lexed']} delay calls are not in the tree (an item "
                f"with a syntax error); their init is not checked"
            )
        if s.whole and r["syntax_errors"]:
            problems.append(f"{where}  has a diagnostic of the syntax stage (`onsa check` shows it); a file of "
                            f"{' or '.join(d + '/' for d in FILE_DIRS)} has none")
        for h in r["hits"]:
            problems.append(
                f"{s.shown}:{s.first + h['line'] - 1}  `{h['call']}~` has the init `{h['init']}`, the default "
                f"value; write the omitted form (spec §11.4, S-539)"
            )
    if srcs and calls == 0:
        problems.append("no delay call in the documents; the check would pass reading nothing")
    summary = ", ".join(f"{n} {what}" for what, n in counts.items()) + f"; {calls} delay calls"
    return problems, summary


def main(argv=None, root=repo.ROOT, cmd=repo.CASES_CMD):
    if argv:
        print(__doc__.split("\n\n")[-2])
        return 2
    try:
        problems, summary = check(root, cmd)
    except repo.RepoError as e:
        print(e)
        return 1
    for p in problems:
        print(p)
    print(summary)
    if problems:
        print(f"{len(problems)} problem(s) with the `init` of the documents")
        return 1
    print("no document writes an init equal to the default")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
