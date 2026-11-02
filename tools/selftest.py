#!/usr/bin/env python3
"""Runs the self-tests of every tool (the `gate-selftest` item of tools/gate_steps.py): the files under tools/
of the forms of `repo.NOT_CODE` (tools/test_*.py, tools/*/test_*.py), found by their names. Each also runs alone.
The self-test of `tools/<tool>.py` is `tools/test_<tool>.py`; this collector and the helpers
(tools/selftest_support.py) are not of that form.

    python3 -B tools/selftest.py                          every self-test
    python3 -B tools/selftest.py --changed-since auto     the ones the diff since `git merge-base HEAD dev` reads

With `--changed-since REV|auto` (the work check passes it, `gate_steps`: `picks`) it runs the self-test of each
changed tool and those whose imports reach it (`pick`), and says how many of them; all of them when the diff
touches this collector, a file of tools/ that is not a module, a module that is gone, when two modules have one
name, or when none would run. The data the self-tests do not read (`gate_steps.SELFTEST_UNREAD`) does not count.
The self-tests read made-up inputs, not the repository (`REAL_READS`, checked by tools/test_selftest.py): what
is checked of the repository itself is the gate's items' (`builtin-names`, `docs`, `vectors`, `cross-check`).
"""
import argparse
import ast
import importlib
import re
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_steps  # noqa: E402
import narrowing  # noqa: E402
import repo  # noqa: E402

SELF = "tools/selftest.py"
# How a self-test would read the repository instead of made-up inputs (its `tools/` is the tools' own): the
# root of a tool, the committed test vectors, the spec of the repository, the compiler built from it.
REAL_READS = (
    (re.compile(r'\b\w+\.ROOT\b(?!\s*/\s*"tools/)'), "the root of the repository"),
    (re.compile(r"\bgen\.DATA\b"), "the committed test vectors"),
    (re.compile(r"\bspec_text\(\)"), "the spec of the repository"),
    (re.compile(r"\brepo\.CASES_(?:BIN|CMD|BUILD)\b"), "the onsa_cases of the repository"),
)
picked = None  # the files `load_tests` runs (None: all)


def real_reads(text):
    """(line, what) of each line of Python source, outside the comments, that reads the repository (`REAL_READS`)."""
    return [(i, why) for i, line in enumerate(text.splitlines(), 1) if not line.lstrip().startswith("#")
            for form, why in REAL_READS if form.search(line)]  # fmt: skip


def self_tests(root):
    """The self-test files under `root`/tools, by the forms of `repo.NOT_CODE`."""
    return sorted({p.resolve() for form in repo.NOT_CODE if form.startswith("tools/") for p in Path(root).glob(form)})


def _imports(path, modules):
    """The modules of tools/ that `path` imports anywhere in it (inside a function too)."""
    names = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            names |= {a.name.split(".")[0] for a in node.names}
        elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            names.add(node.module.split(".")[0])
    return {modules[n] for n in names if n in modules}


def _reaches(test, graph, hit):
    seen, todo = set(), [test]
    while todo:
        p = todo.pop()
        if p in hit:
            return True
        if p not in seen:
            seen.add(p)
            todo += graph.get(p, ())
    return False


def pick(root, changed, unread=gate_steps.SELFTEST_UNREAD):
    """(the self-test files to run for the changed paths, what the first line says): see the docstring."""
    root, tests = Path(root), self_tests(root)
    paths = sorted(p for p in changed if narrowing.under(p, ("tools",)) and not narrowing.under(p, unread))
    found = {}
    for p in sorted((root / "tools").rglob("*.py")):
        found.setdefault(p.stem, []).append(p.resolve())
    why = next((f"two modules are named {n}" for n, ps in found.items() if len(ps) > 1), None)
    hit = set()
    for rel in paths:
        if why:
            break
        if rel == SELF or not rel.endswith(".py"):
            why = f"the diff touches {rel}" + ("" if rel == SELF else ", not a module")
        elif not (root / rel).is_file():
            why = f"{rel} is gone"
        else:
            hit.add((root / rel).resolve())
    if why is None:
        modules = {n: ps[0] for n, ps in found.items()}
        graph = {p: _imports(p, modules) for p in modules.values()}
        own = {t: t.with_name(t.name.removeprefix("test_")) for t in tests}
        chosen = [t for t in tests if own[t] in hit or _reaches(t, graph, hit)]
        if chosen:
            return chosen, f"self-tests: {len(chosen)} of {len(tests)} files (the diff touches {', '.join(paths)})"
        why = f"none reads {', '.join(paths) or 'the diff'}"
    return tests, f"self-tests: all {len(tests)} files ({why})"


def load_tests(loader, tests, pattern):
    """The tests of the self-test files, found by their names so that a new file is not left out."""
    suite = unittest.TestSuite()
    for path in self_tests(repo.ROOT) if picked is None else picked:
        sys.path.insert(0, str(path.parent))
        module = importlib.import_module(path.stem)
        if Path(module.__file__).resolve() != path:
            raise SystemExit(f"two self-tests have the name {path.stem}: {module.__file__} and {path}")
        suite.addTests(loader.loadTestsFromModule(module))
    return suite


def main(argv=None):
    global picked
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--changed-since", metavar="REV|auto", help="only the self-tests the diff since REV reads")
    args, rest = ap.parse_known_args(sys.argv[1:] if argv is None else argv)
    if args.changed_since is not None:
        try:
            since = narrowing.merge_base(repo.ROOT) if args.changed_since == "auto" else args.changed_since
            picked, line = pick(repo.ROOT, narrowing.changed_paths(repo.ROOT, since))
        except narrowing.NarrowError as e:
            print(f"selftest: cannot read the diff: {e}", file=sys.stderr)
            return 2
        print(line, flush=True)
    result = unittest.main(argv=[sys.argv[0], *rest], verbosity=1, exit=False).result
    return 0 if result.wasSuccessful() and result.testsRun else 1  # none run is a failure


if __name__ == "__main__":
    sys.exit(main())
