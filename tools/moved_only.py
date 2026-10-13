#!/usr/bin/env python3
r"""Check that a split of one Rust file into several only moved its lines.

    tools/moved_only.py --orig REV:PATH | --orig PATH
                        [--wrapper REGEX]... [--alias OLD=NEW]... [--root DIR]
                        SEGMENT...

SEGMENT is `PATH` (the whole file) or `PATH:A-B` / `PATH:A-` (lines A to B,
1-based, inclusive), given in the order of the original. Every line of every
file named must be in exactly one segment (no line goes uncompared).

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
           when both sides are the same code but for the blanks outside the
           string literals and a `,` before a closing bracket (rustfmt
           joining or breaking a statement whose indentation changed)

Anything else fails, and so does a comparison with no equal line. The output
lists every differing line with its kind, then the count per kind.
Exit 0 when only allowed kinds differ, 1 otherwise.

Used for the move-only splits (P-1 `parser.rs`, B-1 `body.rs`, E-1 `emit.rs`): split
the file, then pass the original at its commit and the new files in the order of
the original, e.g.

    tools/moved_only.py --orig 047a964:crates/onsa_sema/src/body.rs \
        --wrapper "impl<'a> Checker<'a> \{" crates/onsa_sema/src/body.rs:1-590 ...
"""
import argparse
import difflib
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

PREFIXES = ("pub(super) ", "pub(crate) ")


def norm(line: str) -> str:
    s = line.strip()
    for p in PREFIXES:
        if s.startswith(p):
            s = s[len(p):]
            break
    return s


def read_orig(spec: str, root: Path) -> list:
    if ":" in spec and not Path(spec).exists():
        rev, path = spec.split(":", 1)
        out = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{path}"],
                             capture_output=True, text=True, timeout=60)
        if out.returncode != 0:
            sys.exit(f"cannot read {spec}: {out.stderr.strip()}")
        return out.stdout.splitlines()
    return (root / spec).read_text().splitlines()


def read_segments(specs: list, root: Path):
    """The lines of the segments in order, each with its place `path:line`."""
    files, lines, covered = {}, [], {}
    for spec in specs:
        m = re.fullmatch(r"(.+?)(?::(\d+)-(\d*))?", spec)
        path = m.group(1)
        if path not in files:
            p = root / path
            if not p.exists():
                sys.exit(f"no such file: {path}")
            files[path] = p.read_text().splitlines()
            covered[path] = Counter()
        text = files[path]
        a = int(m.group(2)) if m.group(2) else 1
        b = int(m.group(3)) if m.group(3) else len(text)
        if not (1 <= a <= b <= len(text)):
            sys.exit(f"bad range {spec} (the file has {len(text)} lines)")
        for k in range(a, b + 1):
            covered[path][k] += 1
            lines.append((text[k - 1], f"{path}:{k}"))
    bad = []
    for path, c in covered.items():
        for k in range(1, len(files[path]) + 1):
            if c[k] != 1:
                bad.append(f"{path}:{k} is in {c[k]} segments")
    if bad:
        sys.exit("the segments must cover each file once:\n" + "\n".join(bad[:20]))
    return lines


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


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--orig", required=True)
    ap.add_argument("--wrapper", action="append")
    ap.add_argument("--alias", action="append", default=[])
    ap.add_argument("--root", default=".")
    ap.add_argument("segments", nargs="+")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    wrappers = [re.compile(w) for w in (a.wrapper or [r"impl<'a> Parser<'a> \{"])]
    aliases = [tuple(x.split("=", 1)) for x in a.alias]

    orig = read_orig(a.orig, root)
    new = read_segments(a.segments, root)
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
        if left_old and left_new and squash(" ".join(orig[i] for i in left_old)) == squash(
            " ".join(new[j][0] for j in left_new)
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

    for k, place, text in rows:
        print(f"{k:12} {place:45} {text.strip()[:100]}")
    print()
    print(f"equal lines: {equal} (original {len(orig)} lines, new {len(new)} lines)")
    for k, c in sorted(counts.items()):
        print(f"  {k}: {c}")
    if equal == 0:
        print("FAIL: no equal line")
        return 1
    if counts["NOT ALLOWED"]:
        print("FAIL: differences of a kind that is not allowed")
        return 1
    print("OK: only allowed differences")
    return 0


if __name__ == "__main__":
    sys.exit(main())
