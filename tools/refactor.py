#!/usr/bin/env python3
"""Refactoring: the places to refactor (rules/refactoring.md 8; X-9 X9-74).

Its command is `sizes` (COMMANDS, rules/tools.md 9.1); `refactor.py help` shows it.
`sizes` lists the `.rs` files of `crates/` over the lines of a file and the `fn`s there over the lines of a
function, the most lines first. Both limits are read from the row `BUDGET` of rules/budgets.md (written in one
place); without the row or its numbers it exits 2 (no default). The test files (`repo.NOT_CODE`) are left out,
and the test modules inside a file (`repo.test_lines`): a file is counted without them, and a `fn` in them is
not listed. A `fn` is counted from the line of `fn` to the line of the brace closing its body, a `fn` inside
another too (the outer one with it). The braces in the comments, the strings and the character literals are
not counted (`repo.rust_code`). It lists, and does not fail: whether to divide is the reader's (8.1).
"""
import re
import sys
from bisect import bisect_right
from pathlib import Path

sys.dont_write_bytecode = True
import repo  # noqa: E402

ROOT = repo.ROOT
BUDGETS = "rules/budgets.md"
BUDGET = "リファクタリングの対象の大きさ"  # its value: 「… 関数は 100 行、ファイルは 1000 行を超えるもの …」
LIMITS = {"fn": re.compile(r"関数は\s*(\d+)\s*行"), "file": re.compile(r"ファイルは\s*(\d+)\s*行")}
FN = re.compile(r"fn\s+(?:r#)?(\w+)")


def limits(root):
    """{"fn": lines, "file": lines} of the row BUDGET of rules/budgets.md, or (a str) why not."""
    try:
        text = repo.read(root, BUDGETS)
    except repo.RepoError as e:
        return str(e)
    row = next((c for c in map(repo.table_cells, text.splitlines()) if c[:1] == [BUDGET]), None)
    if row is None:
        return f"{BUDGETS}: no row 「{BUDGET}」"
    found = {k: r.search(row[1] if len(row) > 1 else "") for k, r in LIMITS.items()}
    if not all(found.values()):
        return f"{BUDGETS}: the row 「{BUDGET}」 says no lines of a fn and of a file (「関数は N 行」「ファイルは N 行」)"
    return {k: int(m[1]) for k, m in found.items()}


def functions(text):
    """(name, the line of `fn`, the line of the brace closing its body) of each `fn` with a body in Rust source.
    The body is the first `{` outside `(…)` and `[…]` after the name; a `;` there first: no body."""
    starts = [0]
    for line in text.split("\n"):
        starts.append(starts[-1] + len(line) + 1)
    out, open_, depth, wait, nest = [], [], 0, None, 0
    for j in repo.rust_code(text):
        c = text[j]
        if c == "f" and (m := FN.match(text, j)) and not (j and (text[j - 1].isalnum() or text[j - 1] == "_")):
            wait, nest = (m[1], j), 0
        elif c in "([":
            nest += 1
        elif c in ")]":
            nest -= 1
        elif c == ";" and wait and not nest:
            wait = None
        elif c == "{":
            if wait and not nest:
                open_.append((*wait, depth))
                wait = None
            depth += 1
        elif c == "}":
            depth -= 1
            if open_ and open_[-1][2] == depth:
                name, at, _ = open_.pop()
                out.append((name, bisect_right(starts, at), bisect_right(starts, j)))
    return out


def sizes(args):
    root = Path(args.root)
    over = limits(root)
    if isinstance(over, str):
        print(f"sizes: {over}; nothing listed")
        return 2
    paths = sorted(p.relative_to(root).as_posix() for p in root.glob("crates/**/*.rs"))
    paths = [p for p in paths if not repo.is_test_file(p) and not repo.is_build_output(root, p)]
    if not paths:
        print(f"sizes: no .rs file in {root}/crates/ but the tests; nothing listed")
        return 2
    files, fns = [], []
    for rel in paths:
        try:
            text = repo.read(root, rel)
        except repo.RepoError as e:
            print(f"sizes: {e}; nothing listed")
            return 2
        tests, total = repo.test_lines(text), len(text.splitlines())
        code = total - len(tests & set(range(1, total + 1)))
        if code > over["file"]:
            files.append((code, total, rel))
        fns += [(end - at + 1, rel, at, name) for name, at, end in functions(text)
                if at not in tests and end - at + 1 > over["fn"]]  # fmt: skip
    print(f"sizes: over {over['fn']} lines of a fn and {over['file']} of a file ({BUDGETS}「{BUDGET}」), in the .rs "
          f"files of crates/ without the tests and the test modules")
    print(f"files over {over['file']} lines: {len(files)} of {len(paths)} (lines without the test modules, all)")
    for code, total, rel in sorted(files, key=lambda f: (-f[0], f[2])):
        print(f"  {code:6} ({total:6})  {rel}")
    print(f"fns over {over['fn']} lines: {len(fns)} (from `fn` to its closing brace)")
    for n, rel, at, name in sorted(fns, key=lambda f: (-f[0], *f[1:3])):
        print(f"  {n:6}  {rel}:{at}  {name}")
    return 0


def sizes_args(p):
    p.add_argument("--root", default=ROOT, help="the tree whose crates/ and rules/budgets.md are read (default this one)")


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "sizes": C(sizes_args, sizes, ("parent", "i", "b", "advisor"),
               "crates/ の .rs（テストのファイルとテストのモジュールを除く）で、rules/budgets.md の「リファクタリングの対象の大きさ」を超えるファイルと関数を、行の多い順に並べる（超えても終了 0。budgets の行か数が無ければ終了 2）",
               "リファクタリングの対象を選ぶときと、その前後で大きさを比べるとき。match の腕を並べる長い関数を分けるかは読み手が決める（rules/refactoring.md 8.1）",
               "refactor.py sizes"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("refactor.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
