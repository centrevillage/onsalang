#!/usr/bin/env python3
"""The spec sections the test cases name (`[test] spec`, Q-05, plan D-16 1).

    spec_sections.py --check   fail when a case names a section the spec has no heading for
    spec_sections.py --list    show the sections no case names (information; never fails on them)

The cases and their fragments come from the test runner's own reader (the
`onsa_cases` binary of `onsa_tests`), the headings from `spec_blocks.py`: each
rule is in one place. A section counts as tested when a case names it or one
of its subsections; a case with `mode = "none"` never runs and tests nothing
(`--check` still checks the sections it names).
"""
import argparse
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
SPEC = repo.SPEC


def load_cases(root=ROOT, cmd=repo.CASES_CMD):
    """The cases as `onsa_cases` lists them. Raises repo.RepoError when it fails."""
    return repo.cases_json(root, cmd, str(root))


def unknown(cases, headings):
    """(case path, section) for every named section the spec has no heading for."""
    known = set(headings)
    return [(c["path"], s) for c in cases for s in c["spec"] if s.removeprefix("§") not in known]


def untested(cases, headings):
    """The headings no case that runs names, by itself or through a subsection."""
    named = {s.removeprefix("§") for c in cases if c.get("mode") != "none" for s in c["spec"]}
    return [h for h in headings if not any(n == h or n.startswith(h + ".") for n in named)]


def main(argv=None, root=ROOT, cmd=repo.CASES_CMD):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true")
    g.add_argument("--list", action="store_true")
    args = ap.parse_args(argv)
    try:
        cases = load_cases(root, cmd)
    except (repo.RepoError, OSError, json.JSONDecodeError) as e:
        print(f"cannot list the cases: {e}")
        return 1
    headings = spec_blocks.headings((root / SPEC).read_text(encoding="utf-8"))
    if args.check:
        bad = unknown(cases, headings)
        for path, s in bad:
            print(f"{path}: [test] spec names {s}, which is not a numbered heading of {SPEC}")
        named = sum(1 for c in cases if c["spec"])
        print(f"{len(cases)} cases, {named} name sections; " + (f"{len(bad)} unknown" if bad else "all are headings"))
        return 1 if bad else 0
    left = untested(cases, headings)
    print(f"{len(headings) - len(left)} of {len(headings)} sections have a case; without one:")
    for h in left:
        print(f"  {'  ' * h.count('.')}§{h}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
