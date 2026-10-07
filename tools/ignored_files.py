#!/usr/bin/env python3
"""Files of the repository that its `.gitignore` files ignore (W1-02).

A file the `.gitignore` patterns match is never committed, so a test case, a
golden file, a std module or a tool named like a build output (`build/`,
`*.out`, `*.log`) would silently stay on one machine (W1-03: `tests/build/` was
not committed). Under `SCANNED`, this check fails on:
- an untracked file or directory that the repository's `.gitignore` files
  ignore, and
- a tracked file that they match (a sibling written next to it, by
  `UPDATE_GOLDEN` for example, would be ignored).
Only the `.gitignore` files of the repository count: the user's global
excludes file and `.git/info/exclude` are not read, so the result is the same
on every machine. The build outputs (`repo.is_build_output`: `target/` at the
root or next to an `onsa.toml` / `Cargo.toml`) are expected to be ignored.

    tools/ignored_files.py [--root DIR]

Exit 0 when nothing is ignored, 1 otherwise (or when git fails).
"""
import argparse
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

ROOT = repo.ROOT
SCANNED = ("crates", "std", "runtime", "tools", "tests")
# Only the `.gitignore` files: no `--exclude-standard` (it adds `.git/info/exclude`
# and `core.excludesFile`), and no global excludes file.
GIT = ("git", "-c", "core.excludesFile=")
EXCLUDES = ("--exclude-per-directory=.gitignore",)


def _git(root, *args):
    return subprocess.run([*GIT, *args], cwd=root, capture_output=True, text=True, check=True).stdout


def ignored(root):
    """(untracked ignored, tracked ignored) paths under `SCANNED`. Raises
    CalledProcessError / OSError when git fails."""
    untracked = _git(root, "ls-files", "--others", "--ignored", *EXCLUDES, "--directory", "-z", "--", *SCANNED)
    tracked = _git(root, "ls-files", "--cached", "--ignored", *EXCLUDES, "-z", "--", *SCANNED)

    def split(out):
        return sorted(p for p in out.split("\0") if p)

    return [p for p in split(untracked) if not repo.is_build_output(root, p)], split(tracked)


def main(argv=None, root=ROOT):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=None)
    args = ap.parse_args(argv)
    root = args.root or root
    try:
        untracked, tracked = ignored(root)
    except (subprocess.CalledProcessError, OSError) as e:
        print(f"cannot ask git: {e}\n{getattr(e, 'stderr', '') or ''}".rstrip())
        return 1
    for p in untracked:
        print(f"{p}: the .gitignore ignores it, so it is never committed; rename it, or narrow the pattern")
    for p in tracked:
        print(f"{p}: committed, but a .gitignore pattern matches it; a file written next to it would be ignored")
    n = len(untracked) + len(tracked)
    print(f"{', '.join(d + '/' for d in SCANNED)}: " + (f"{n} ignored path(s)" if n else "nothing ignored (build outputs aside)"))
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
