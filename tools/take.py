#!/usr/bin/env python3
"""Moved: `patch`, `check` and `apply` are `tools/work.py`'s (X-9 U4; `tools/work.py help`). This passes its
arguments to the same command there, until the rules name work.py (X9-8). Exit 2 for another command."""
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import work  # noqa: E402


def main(argv=None):
    argv = sys.argv[1:] if argv is None else list(argv)
    if argv[:1] not in (["patch"], ["check"], ["apply"]):
        print("usage: tools/take.py patch|check|apply ... (moved to tools/work.py; see tools/work.py help)")
        return 2
    return work.main(argv)


if __name__ == "__main__":
    sys.exit(main())
