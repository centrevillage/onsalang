#!/usr/bin/env python3
r"""Check that a split of Rust files into others only moved their lines.

Its commands are `check` and `split` (COMMANDS, rules/tools.md 9.1); `moved_only.py help` shows them.

    tools/moved_only.py check --orig REV:PATH | --orig PATH
                        [--wrapper REGEX]... [--alias OLD=NEW]... [--root DIR] [--rev REV] SEGMENT...
    tools/moved_only.py split [--root DIR] [--rev REV] TABLE.json|TABLE.toml

`check`: SEGMENT is `PATH` (the whole file) or `PATH:A-B` / `PATH:A-` (lines A to B, 1-based, inclusive),
given in the order of the original. Every line of every file named must be in exactly one segment.

`split`: the table holds `checks`, a list of {"orig": "REV:PATH", "pieces": [SEGMENT, ...], "wrapper":
[REGEX, ...], "alias": ["OLD=NEW", ...], "orig_path": PATH} (`wrapper`, `alias` and `orig_path` may be left
out; `orig_path` names the file of the tree an `orig` copied elsewhere stands for), and `renames`, a list of
[ORIG_PATH, NEW_PATH]. Each check compares its original with its pieces as `check` does, so a new file may take
pieces of several originals; every line of every new file named in the table must be in exactly one piece over
all the checks. It prints each check's result and the lines that left their file (those of a piece in another
file than the original's and not its rename, but for the lines only the new side has: blank, use, mod, moddoc),
for the stop line of a move-only unit. The files are written by hand; the table only checks them.

With `--rev REV` the new files are read at that commit (else from the tree of `--root`).

Both sides are normalized line by line: the indentation and the trailing
blanks go, and a leading `pub(super) ` or `pub(crate) ` goes. They are then
compared in order (difflib, no autojunk). A difference is allowed only if it
is one of these kinds:

  blank    an empty line
  use      a line of a `use` statement (up to its `;`)
  mod      a `mod x;` / `mod x {` line, and a `#[cfg(test)]` right before one
  wrapper  a line matching a --wrapper regex (default: `impl<'a> Parser<'a> {`)
  close    a lone `}`, at most as many per side as that side's wrapper and
           `mod x {` lines
  moddoc   a `//!` line
  doclink  a comment line replaced by one equal to it but for the writing of
           its doc links (`[`x`]`, `[`a::x`]`, `[`x`](a::x)`)
  alias    a line replaced by one equal to it after an --alias rewrite
           (`super::=crate::parser::`)
  reflow   the lines of one change that are left after the kinds above,
           when both sides, normalized, are the same code but for the blanks
           outside the string literals and a `,` before a closing bracket
           (rustfmt joining or breaking a statement whose indentation or
           visibility changed)

Anything else fails, and so does a comparison with no equal line. The output
lists every differing line with its kind, then the count per kind.
Exit 0 when only allowed kinds differ, 1 otherwise.
"""
import difflib
import json
import re
import subprocess
import sys
import tomllib
from collections import Counter
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

PREFIXES = ("pub(super) ", "pub(crate) ")
DEFAULT_WRAPPER = r"impl<'a> Parser<'a> \{"
WRITTEN = ("blank", "use", "mod", "moddoc")  # the kinds of a line only the new side has, not moved


def norm(line: str) -> str:
    s = line.strip()
    for p in PREFIXES:
        if s.startswith(p):
            s = s[len(p):]
            break
    return s


def read_lines(spec: str, root: Path, rev=None) -> list:
    """The lines of `spec` (`REV:PATH`, or a path read at `rev` or in `root`)."""
    if rev is None and (":" not in spec or (root / spec).exists()):
        if not (root / spec).is_file():
            sys.exit(f"no such file: {spec}")
        return (root / spec).read_text().splitlines()
    rev, path = (rev, spec) if rev is not None else spec.split(":", 1)
    out = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{path}"],
                         capture_output=True, text=True, timeout=60)  # fmt: skip
    if out.returncode != 0:
        sys.exit(f"cannot read {rev}:{path}: {out.stderr.strip()}")
    return out.stdout.splitlines()


def read_segments(specs: list, read, covered: dict, sizes: dict):
    """The lines of the segments in order, each with its place `path:line`; each line counted in `covered`."""
    files, lines = {}, []
    for spec in specs:
        m = re.fullmatch(r"(.+?)(?::(\d+)-(\d*))?", spec)
        path = m.group(1)
        if path not in files:
            files[path] = read(path)
            sizes[path] = len(files[path])
        text = files[path]
        a = int(m.group(2)) if m.group(2) else 1
        b = int(m.group(3)) if m.group(3) else len(text)
        if not (1 <= a <= b <= len(text)):
            sys.exit(f"bad range {spec} (the file has {len(text)} lines)")
        for k in range(a, b + 1):
            covered.setdefault(path, Counter())[k] += 1
            lines.append((text[k - 1], f"{path}:{k}"))
    return lines


def coverage(covered: dict, sizes: dict) -> list:
    return [f"{path}:{k} is in {c[k]} segments" for path, c in covered.items()
            for k in range(1, sizes[path] + 1) if c[k] != 1]  # fmt: skip


def statement_marks(normed: list) -> list:
    """For each line, 'use' / 'mod' when it belongs to such a statement."""
    marks = [None] * len(normed)
    k = 0
    while k < len(normed):
        s = normed[k]
        if s.startswith("use ") or s.startswith("pub use "):
            j = k
            while not normed[j].rstrip().endswith(";") and j + 1 < len(normed):
                j += 1
            for t in range(k, j + 1):
                marks[t] = "use"
            k = j + 1
            continue
        if re.fullmatch(r"(pub )?mod \w+(;| \{)", s):
            marks[k] = "mod"
            t = k - 1
            while t >= 0 and normed[t] == "":
                t -= 1
            if t >= 0 and normed[t] == "#[cfg(test)]":
                marks[t] = "mod"
        k += 1
    return marks


def squash(s: str) -> str:
    """The code without the blanks outside the string literals and without
    a `,` before a closing bracket."""
    out, k, n = [], 0, len(s)
    while k < n:
        c = s[k]
        m = re.match(r"'(\\.|[^\\'])'", s[k:k + 5])
        if m:
            out.append(m.group(0))
            k += m.end()
            continue
        if c == '"':
            j = k + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[k:j + 1])
            k = j + 1
            continue
        if not c.isspace():
            out.append(c)
        k += 1
    return re.sub(r",(?=[)\]}])", "", "".join(out))


def link_norm(s: str) -> str:
    s = re.sub(r"\]\([^)]*\)", "", s)
    s = s.replace("[", "").replace("]", "")
    return re.sub(r"`(?:\w+::)+", "`", s)


def compare(orig: list, new: list, wrappers: list, aliases: list):
    """(rows (kind, place, text), counts per kind, the number of equal lines) of `orig` against `new`
    ((line, place) in the order of the original)."""
    wrappers = [re.compile(w) for w in (wrappers or [DEFAULT_WRAPPER])]
    aliases = [tuple(x.split("=", 1)) for x in aliases]
    old_n = [norm(line) for line in orig]
    new_n = [norm(line) for line, _ in new]
    old_marks, new_marks = statement_marks(old_n), statement_marks(new_n)

    def kind(s: str, mark):
        if s == "":
            return "blank"
        if mark:
            return mark
        if any(w.fullmatch(s) for w in wrappers):
            return "wrapper"
        if s == "}":
            return "close"
        if s.startswith("//!"):
            return "moddoc"
        return None

    def paired(x: str, y: str):
        if x.startswith("//") and y.startswith("//") and link_norm(x) == link_norm(y):
            return "doclink"
        for old, new_ in aliases:
            if x.replace(old, new_) == y:
                return "alias"
        return None

    sm = difflib.SequenceMatcher(None, old_n, new_n, autojunk=False)
    rows, counts, equal = [], Counter(), 0
    openers = {"-": 0, "+": 0}
    closes = {"-": 0, "+": 0}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            equal += i2 - i1
            continue
        olds = list(range(i1, i2))
        news = list(range(j1, j2))
        done_old, done_new = set(), set()
        # Pair the comment lines and the aliased lines of a replacement in order.
        for i in olds:
            for j in news:
                if j in done_new:
                    continue
                k = paired(old_n[i], new_n[j])
                if k:
                    done_old.add(i)
                    done_new.add(j)
                    rows.append((k, f"- orig:{i + 1}", orig[i]))
                    rows.append((k, f"+ {new[j][1]}", new[j][0]))
                    counts[k] += 1
                    break
        left_old = [i for i in olds if i not in done_old and not kind(old_n[i], old_marks[i])]
        left_new = [j for j in news if j not in done_new and not kind(new_n[j], new_marks[j])]
        # The normalized lines, so that a `pub(super) ` put before a statement rustfmt broke is no difference.
        if left_old and left_new and squash(" ".join(old_n[i] for i in left_old)) == squash(
            " ".join(new_n[j] for j in left_new)
        ):
            for i in left_old:
                done_old.add(i)
                rows.append(("reflow", f"- orig:{i + 1}", orig[i]))
            for j in left_new:
                done_new.add(j)
                rows.append(("reflow", f"+ {new[j][1]}", new[j][0]))
            counts["reflow"] += 1
        for side, idxs, done, normed, marks in (("-", olds, done_old, old_n, old_marks),
                                                ("+", news, done_new, new_n, new_marks)):
            for i in idxs:
                if i in done:
                    continue
                k = kind(normed[i], marks[i])
                if k in ("wrapper",) or (k == "mod" and normed[i].endswith("{")):
                    openers[side] += 1
                if k == "close":
                    closes[side] += 1
                place = f"- orig:{i + 1}" if side == "-" else f"+ {new[i][1]}"
                text = orig[i] if side == "-" else new[i][0]
                rows.append((k or "NOT ALLOWED", place, text))
                counts[k or "NOT ALLOWED"] += 1

    for side in "-+":
        if closes[side] > openers[side]:
            rows.append(("NOT ALLOWED", side, f"{closes[side]} lone `}}` against {openers[side]} wrappers"))
            counts["NOT ALLOWED"] += 1
    return rows, counts, equal


def show(rows, counts, equal, n_orig, n_new) -> bool:
    """Print the rows and the counts; whether only allowed kinds differ."""
    for k, place, text in rows:
        print(f"{k:12} {place:45} {text.strip()[:100]}")
    print()
    print(f"equal lines: {equal} (original {n_orig} lines, new {n_new} lines)")
    for k, c in sorted(counts.items()):
        print(f"  {k}: {c}")
    if equal == 0:
        print("FAIL: no equal line")
        return False
    if counts["NOT ALLOWED"]:
        print("FAIL: differences of a kind that is not allowed")
        return False
    print("OK: only allowed differences")
    return True


def reader(a):
    root = Path(a.root).resolve()
    return root, lambda path: read_lines(path, root, a.rev)


def check(a) -> int:
    root, read = reader(a)
    orig = read_lines(a.orig, root)
    covered, sizes = {}, {}
    new = read_segments(a.segments, read, covered, sizes)
    if bad := coverage(covered, sizes):
        sys.exit("the segments must cover each file once:\n" + "\n".join(bad[:20]))
    return 0 if show(*compare(orig, new, a.wrapper, a.alias), len(orig), len(new)) else 1


def split(a) -> int:
    root, read = reader(a)
    text = Path(a.table).read_text()
    table = tomllib.loads(text) if a.table.endswith(".toml") else json.loads(text)
    renames = {tuple(r) for r in table.get("renames", [])}
    covered, sizes, ok, moved_total = {}, {}, True, 0
    for c in table["checks"]:
        orig_path = c.get("orig_path") or c["orig"].split(":", 1)[-1]
        orig = read_lines(c["orig"], root)
        new = read_segments(c["pieces"], read, covered, sizes)
        rows, counts, equal = compare(orig, new, c.get("wrapper"), c.get("alias", []))
        print(f"=== {c['orig']} <- {' '.join(c['pieces'])}")
        ok &= show(rows, counts, equal, len(orig), len(new))
        foreign = lambda place: (p := place.rsplit(":", 1)[0]) != orig_path and (orig_path, p) not in renames  # noqa: E731
        moved = sum(foreign(place) for _, place in new) - sum(
            k in WRITTEN and place.startswith("+ ") and foreign(place[2:]) for k, place, _ in rows)
        print(f"lines moved out of {orig_path} (written lines not counted): {moved}")
        moved_total += moved
    bad = coverage(covered, sizes)
    print("=== coverage")
    print("\n".join(bad[:20]) if bad else f"every line of the {len(covered)} new files is in one piece")
    print(f"=== lines moved to another file in all: {moved_total}")
    ok &= not bad
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


def common_args(p):
    p.add_argument("--root", default=".", help="the tree of the new files and of git (default: the current directory)")
    p.add_argument("--rev", help="read the new files at this commit instead of the tree")


def check_args(p):
    p.add_argument("--orig", required=True, help="the original, REV:PATH or PATH")
    p.add_argument("--wrapper", action="append", help=f"a regex of a wrapper line (default {DEFAULT_WRAPPER})")
    p.add_argument("--alias", action="append", default=[], help="OLD=NEW: a line equal after this rewrite")
    p.add_argument("segments", nargs="+", help="PATH, PATH:A-B or PATH:A- in the order of the original")


def split_args(p):
    p.add_argument("table", help="the table of the checks (.json, or .toml)")


C = repo.Command
COMMANDS = {
    "check": C(check_args, check, ("parent", "i", "b"),
               "一つの元のファイル（REV:PATH）と、分けた先のファイルの区間を元の順に並べたものを比べ、移しただけ（許す種類の違いだけ）かを確かめる",
               "一つのファイルを分けるだけの単位で、分けた後に（元が一つのとき。二つ以上の元を寄せるなら split）",
               "moved_only.py check --orig dev:crates/onsa_sema/src/body.rs --wrapper \"impl<'a> Checker<'a> \\{\" crates/onsa_sema/src/body.rs:1-590 crates/onsa_sema/src/bounds.rs"),
    "split": C(split_args, split, ("parent", "i", "b"),
               "元のファイルごとに移す先の区間を並べた表で、元ごとに check の比べを回し、全ての先のファイルの行がちょうど一つの区間に入るかと、別のファイルへ移した行の数（止まる線の数え方）を出す",
               "ファイルを分ける・寄せる移すだけの単位で、分けた後と親が写した後に（表は書く担当が作り、親は同じ表を --rev で回す）",
               "moved_only.py split --rev HEAD target/notes/142/w513u5a/u5a_spec.json"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("moved_only.py", __doc__.split("\n")[0], COMMANDS, argv, common_args, lambda: __doc__)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
