#!/usr/bin/env python3
"""Runs the self-tests of every tool (the `gate-selftest` item of tools/gate_steps.py): the files under tools/
of the forms of `repo.NOT_CODE` (tools/test_*.py, tools/*/test_*.py), found by their names. Each also runs alone.
The self-test of `tools/<tool>.py` is `tools/test_<tool>.py`; this collector and the helpers
(tools/selftest_support.py) are not of that form.

    python3 -B tools/selftest.py
"""
import importlib
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402


def load_tests(loader, tests, pattern):
    """The tests of the self-test files, found by their names so that a new file is not left out."""
    suite = unittest.TestSuite()
    files = {p.resolve() for form in repo.NOT_CODE if form.startswith("tools/") for p in repo.ROOT.glob(form)}
    for path in sorted(files):
        sys.path.insert(0, str(path.parent))
        module = importlib.import_module(path.stem)
        if Path(module.__file__).resolve() != path:
            raise SystemExit(f"two self-tests have the name {path.stem}: {module.__file__} and {path}")
        suite.addTests(loader.loadTestsFromModule(module))
    return suite


if __name__ == "__main__":
    unittest.main(verbosity=1)
