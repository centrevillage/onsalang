#!/usr/bin/env python3
"""Take the work of a worktree into another tree as a patch (docs/leader-rules.md 3.2 to 3.5).

    tools/take.py patch <worktree> <base> <out.patch> [--main DIR]
    tools/take.py check <patch> [--to DIR]
    tools/take.py apply <patch> [--to DIR]

`patch` runs, in the worktree (`git -C`, no `cd`), `add -A`,
`diff --cached --binary <base>` into the patch and `reset` (the index of the
worktree is left empty). It stops when the base is not an ancestor of the
worktree's HEAD. When the HEAD of the main tree (`--main`, default this
repository) differs from the base, it prints the files that differ between
them and the files of the patch among them (3.3: when only documents moved,
the patch from the base still applies). It prints the lines added and removed
per file, the new files, the totals, and the totals without the tests and
the data (`is_code`: the files ending in `CODE_SUFFIXES` that are not under
`tests/` or `crates/*/tests/`, not `tests.rs` nor `*_tests.rs`, and not
`tools/test_*.py` nor `tools/*/test_*.py`; in a Rust file of the code, the
lines of a `#[cfg(test)] mod … { … }` block are tests too, on the new side for
the added lines and on the old side for the removed ones: `test_lines`).

`check` (`--to`, default this repository) says whether `git apply --check`
passes, else whether `git apply --check -3` does (and whether with
conflicts; or that the patch is already there: its reverse applies), and lists the files of the patch that have uncommitted changes
or are untracked in the tree. `apply` applies the patch the way `check`
found; after `-3` it runs `git restore --staged` on the files of the patch,
so nothing of it stays in the index. It prints the applied files.

Nothing here commits, stashes, resets the tree or checks paths out.
Exit 0 on success, 1 when a step fails or the patch does not apply, 2 on a
usage error.
"""
import argparse
import re
import subprocess
import sys
from fnmatch import fnmatch
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

ROOT = repo.ROOT
CODE_SUFFIXES = (".rs", ".py", ".sh", ".c", ".h", ".js")
ALREADY = "already in the tree (its reverse applies); nothing to do"
NOT_CODE = ("tests/*", "crates/*/tests/*", "*/tests.rs", "*_tests.rs", "tools/test_*.py", "tools/*/test_*.py")


class Failed(Exception):
    pass


def is_code(path):
    return path.endswith(CODE_SUFFIXES) and not any(fnmatch(path, p) for p in NOT_CODE)


# The pieces of Rust source that may hold a brace that is not one (`test_lines`).
RAW_STRING = re.compile(r'b?r(#*)"')
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.)|[^\\'\n])'")
TEST_MOD = re.compile(r"\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*\{")
HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def block_end(text, i):
    """The offset of the `}` that closes the first `{` from `i` in Rust source, skipping
    comments, strings, raw strings and character literals (a test holds the source of
    other languages in strings, with braces that do not pair); the end of the text if none."""
    depth, n = 0, len(text)
    while i < n:
        c = text[i]
        ident = i > 0 and (text[i - 1].isalnum() or text[i - 1] == "_")
        if text.startswith("//", i):
            i = text.find("\n", i)
            i = n if i < 0 else i
            continue
        if text.startswith("/*", i):
            nest, i = 1, i + 2
            while i < n and nest:
                if text.startswith("/*", i):
                    nest, i = nest + 1, i + 2
                elif text.startswith("*/", i):
                    nest, i = nest - 1, i + 2
                else:
                    i += 1
            continue
        raw = None if ident else RAW_STRING.match(text, i)
        if raw:
            close = '"' + raw.group(1)
            j = text.find(close, raw.end())
            i = n if j < 0 else j + len(close)
            continue
        if c == '"' or (c == "b" and not ident and text.startswith('b"', i)):
            i += 2 if c == "b" else 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c == "'":
            ch = CHAR.match(text, i)
            i = ch.end() if ch else i + 1  # else a lifetime
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return n


def test_lines(text):
    """The numbers (from 1) of the lines of the `#[cfg(test)] mod … { … }` blocks of a
    Rust source: from the attribute to the closing brace."""
    lines, out = text.split("\n"), set()
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line) + 1)
    i = 0
    while i < len(lines):
        j = i + 1
        while j < len(lines) and lines[j].lstrip().startswith(("#[", "//")):
            j += 1
        if lines[i].strip() != "#[cfg(test)]" or j == len(lines) or not TEST_MOD.match(lines[j]):
            i += 1
            continue
        end = block_end(text, starts[j])
        last = next(k for k in range(j, len(lines)) if starts[k + 1] > end)
        out.update(range(i + 1, last + 2))
        i = last + 1
    return out


def in_file_tests(tree, base, paths):
    """{path: [added, removed]}: the lines of the diff of the index of `tree` from `base`
    in the files `paths` that are in a test module of the file (`test_lines`)."""
    out = {}
    if not paths:
        return out
    show = lambda rev: git(tree, "show", rev).stdout.decode(errors="replace")  # noqa: E731
    old = counts = None
    old_tests = new_tests = set()
    for line in git(tree, "diff", "--cached", "-U0", base, "--", *paths).stdout.decode(errors="replace").split("\n"):
        if line.startswith("--- "):
            old = line[6:] if line.startswith("--- a/") else None
        elif line.startswith("+++ "):
            new = line[6:] if line.startswith("+++ b/") else None
            old_tests = test_lines(show(f"{base}:{old}")) if old else set()
            new_tests = test_lines(show(f":{new}")) if new else set()
            counts = out.setdefault(new or old, [0, 0])
        elif line.startswith("@@ ") and counts is not None:
            m = HUNK.match(line)
            a, b = int(m[1]), int(m[2]) if m[2] is not None else 1
            c, d = int(m[3]), int(m[4]) if m[4] is not None else 1
            counts[0] += sum(k in new_tests for k in range(c, c + d))
            counts[1] += sum(k in old_tests for k in range(a, a + b))
    return out


def git(tree, *args, ok=(0,)):
    r = subprocess.run(["git", "-C", str(tree), *args], capture_output=True)
    if r.returncode not in ok:
        raise Failed(f"git {' '.join(args)}: exit {r.returncode}: {r.stderr.decode(errors='replace').strip()}")
    return r


def numstat(tree, *args):
    """[(added, removed, path)] of `git <args> --numstat -z` (`-` for a binary file)."""
    fields, out = git(tree, *args, "--numstat", "-z").stdout.decode().split("\0"), []
    i = 0
    while i < len(fields) - 1:
        add, rm, path = fields[i].split("\t", 2)
        if path:
            i += 1
        else:  # a rename: the old and the new path follow
            path, i = fields[i + 2], i + 3
        out.append((add, rm, path))
    return out


def summary(stats, new, inner=None):
    """Print the lines per file and the totals; `inner` is `in_file_tests` of the code files."""
    total, code = [0, 0], [0, 0]
    for add, rm, path in stats:
        print(f"  {add:>6} {rm:>6}  {path}{'  (new)' if path in new else ''}")
        for acc in (total, code) if is_code(path) else (total,):
            acc[0] += int(add) if add != "-" else 0
            acc[1] += int(rm) if rm != "-" else 0
    left = [sum(v[k] for v in (inner or {}).values()) for k in (0, 1)]
    files = sum(1 for v in (inner or {}).values() if any(v))
    note = f" (the test modules inside {files} file(s), +{left[0]} -{left[1]}, left out)" if files else ""
    print(f"  {len(stats)} file(s), +{total[0]} -{total[1]}; "
          f"without the tests and the data: +{code[0] - left[0]} -{code[1] - left[1]}{note}")


def patch(args):
    wt, base = Path(args.worktree), args.base
    if git(wt, "merge-base", "--is-ancestor", base, "HEAD", ok=(0, 1)).returncode:
        raise Failed(f"{base} is not an ancestor of the HEAD of {wt}")
    git(wt, "add", "-A")
    try:
        diff = git(wt, "diff", "--cached", "--binary", base).stdout
        stats = numstat(wt, "diff", "--cached", base)
        new = set(git(wt, "diff", "--cached", "--name-only", "--diff-filter=A", "-z", base).stdout.decode().split("\0"))
        inner = in_file_tests(wt, base, [p for _, _, p in stats if p.endswith(".rs") and is_code(p)])
    finally:
        git(wt, "reset", "-q")
    Path(args.out).write_bytes(diff)
    print(f"{args.out}: the patch of {wt} from {base}")
    summary(stats, new, inner)
    head = git(args.main, "rev-parse", "HEAD").stdout.decode().strip()
    if git(args.main, "rev-parse", base).stdout.decode().strip() != head:
        moved = set(git(args.main, "diff", "--name-only", "-z", base, head).stdout.decode().split("\0")) - {""}
        both = sorted(moved & {p for _, _, p in stats})
        print(f"the main tree ({head[:9]}) differs from {base} in {len(moved)} file(s); of the patch: "
              + (", ".join(both) if both else "none"))
    return 0


def paths_of(tree, patch_file):
    return [p for _, _, p in numstat(tree, "apply", str(Path(patch_file).resolve()))]


def check(patch_file, to):
    """("plain" | ALREADY | "3way" | "3way with conflicts", the files of the patch, problems of the tree)."""
    p = str(Path(patch_file).resolve())
    paths = paths_of(to, p)
    status = git(to, "status", "--porcelain=v1", "-z", "--", *paths).stdout.decode().split("\0")
    notes, i = [], 0
    while i < len(status) - 1:
        code, path = status[i][:2], status[i][3:]
        notes.append(f"{path}: {'untracked, already there' if code == '??' else f'uncommitted change ({code.strip()})'}")
        i += 2 if code[0] in "RC" else 1
    if git(to, "apply", "--check", p, ok=(0, 1)).returncode == 0:
        return "plain", paths, notes
    if git(to, "apply", "--check", "-R", p, ok=(0, 1)).returncode == 0:
        return ALREADY, paths, notes
    r = git(to, "apply", "--check", "-3", p, ok=(0, 1))
    err = r.stderr.decode(errors="replace")
    if r.returncode:
        raise Failed("\n".join([f"the patch does not apply, plain nor with -3:\n{err.strip()}", *notes]))
    return ("3way with conflicts" if "with conflicts" in err else "3way"), paths, notes


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("patch")
    p.add_argument("worktree")
    p.add_argument("base")
    p.add_argument("out")
    p.add_argument("--main", default=ROOT)
    for name in ("check", "apply"):
        p = sub.add_parser(name)
        p.add_argument("patch")
        p.add_argument("--to", default=ROOT)
    args = ap.parse_args(argv)
    try:
        if args.cmd == "patch":
            return patch(args)
        how, paths, notes = check(args.patch, args.to)
        print(f"applies: {how}")
        for n in notes:
            print(f"  {n}")
        if args.cmd == "check" or how == ALREADY:
            return 0
        r = git(args.to, "apply", *(["-3"] if how != "plain" else []), str(Path(args.patch).resolve()), ok=(0, 1))
        if how != "plain":
            git(args.to, "restore", "--staged", "--", *paths)
        print(r.stderr.decode(errors="replace").strip() or "applied")
        for path in paths:
            print(f"  {path}")
        return r.returncode
    except Failed as e:
        print(e)
        return 1


if __name__ == "__main__":
    sys.exit(main())
