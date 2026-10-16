#!/usr/bin/env python3
"""Move the items of `docs/carryovers.md` to the files they are for (X-2 step 6, MG-2: (5b), and (5c)
with more kinds in DESTS).

    python3 -B migrate_carryovers.py plan   [--root DIR] [--overrides TOML]
    python3 -B migrate_carryovers.py apply  [--root DIR] [--overrides TOML]
    python3 -B migrate_carryovers.py verify [--root DIR] --before DIR|REV

A unit is a top-level item with a bold head (`- **…**`) and the lines after it that start with a space
(its lines going on and its nested items); any other line (a blank line, a top-level line) ends it. A
top-level item with no bold head (the conventions at the top) is not a unit and stays.

- Where a unit goes: its bold head starts with a W and then `（`, `:` or its end: that W. Else it is
  listed and stays (`many-ids`: a W and `・`; `id-words`: a W and another word; `stage`: `W7 の …`;
  `other`), unless the overrides give it a destination.
- The overrides, `[to]` / `"<key of the list>" = "W4-12"` or `"keep"`: a key of the list only (the
  bold head, its `:` taken off; ` #2` on the second unit of the same head), a destination `keep` or an
  ID of a kind of DESTS whose file is there. Anything else refuses them all (exit 1).
- `plan` writes nothing: the units per destination and the list (`line<TAB>class<TAB>key`).
- `apply` puts the units of a destination, in their order and two spaces in, character for character,
  under the label of DESTS (DF-6): after the lines under `- 持ち越し:` when it is there, else a new
  `- 持ち越し:` at the end of the file. The units are taken out of the document. On an error nothing
  is left written. The IDs and sections of the moved text not found (`docs check` (b)) are printed.
- `verify --before`: the document is the one before with the moved units taken out, byte for byte;
  every changed file of DESTS' directories is the one before with lines put in at one place, under its
  label as `apply` puts them, and those lines two spaces out are moved units, each once, in their order;
  a unit whose head names its W went there.
- Exit: 0 done / the same; 1 refused / a difference; 2 an error of the tool (a document not read).
- Order: one pass over the lines of the document; `verify` reads each file of DESTS' directories once
  (the trees before and after) and matches the units by a table. Linear; no loop on a fixed point.
"""
import argparse
import re
import subprocess
import sys
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools"))
import docs  # noqa: E402
import repo  # noqa: E402

DOC = Path("docs") / "carryovers.md"
DESTS = {"W": "持ち越し"}  # the kinds a unit may go to -> the label it goes under
KEEP = "keep"
TO = "to"  # the table of the overrides
BOLD = re.compile(r"- \*\*(.+?)\*\*")
W_ID = repo.KIND["W"].pattern
W_HEAD = re.compile(rf"({W_ID})(?:[（:]|$)")
CLASSES = ((re.compile(rf"{W_ID}・"), "many-ids"), (re.compile(W_ID), "id-words"), (re.compile(r"W\d+(?![\d-])"), "stage"))
INDENT = "  "


class Refused(Exception):
    """`args[0]`: the lines that say why; nothing is written."""


@dataclass(frozen=True)
class Unit:
    at: int  # the index of its first line
    lines: tuple
    head: str  # the bold text, a `:` at its end taken off

    @property
    def to(self):
        """Its W by the head, or None."""
        m = W_HEAD.match(self.head)
        return m.group(1) if m else None


def read_units(lines):
    units, i = [], 0
    while i < len(lines):
        j = i + 1
        if m := BOLD.match(lines[i]):
            while j < len(lines) and lines[j].startswith(" "):
                j += 1
            units.append(Unit(i, tuple(lines[i:j]), m.group(1).rstrip(":：")))
        i = j
    return units


def listed(units):
    """{at: (class, key)} of the units the head does not send."""
    out, seen = {}, Counter()
    for u in units:
        if u.to is None:
            seen[u.head] += 1
            cls = next((c for p, c in CLASSES if p.match(u.head)), "other")
            out[u.at] = (cls, u.head + (f" #{seen[u.head]}" if seen[u.head] > 1 else ""))
    return out


def dest_file(root, dest):
    """(the file of a destination, None) or (None, why it is not one)."""
    kind = repo.kind_of(dest) if isinstance(dest, str) else None
    if kind is None or kind.name not in DESTS:
        return None, f"{dest!r} is not {KEEP} or an ID of {', '.join(DESTS)}"
    rel = repo.path_of(dest)
    return (rel, None) if (Path(root) / rel).is_file() else (None, f"{rel.as_posix()} is not there")


def read_overrides(path):
    if path is None:
        return {}, []
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
        raise repo.RepoError(f"{path}: {e}") from e
    why = [f"{k}: not the table `[{TO}]`" for k in data if k != TO]
    to = data.get(TO, {})
    return (to, why) if isinstance(to, dict) else ({}, why + [f"{TO}: not a table"])


def evaluate(root, path):
    """(lines, units, the list, {at: destination}, the items of the list no override fills)."""
    lines = repo.read_exact(root, DOC).split("\n")
    units = read_units(lines)
    items = listed(units)
    over, why = read_overrides(path)
    keys = {key for _, key in items.values()}
    why += [f"{k}: not in the list of the judgements" for k in over if k not in keys]
    why += [f"{k}: {bad}" for k, v in over.items() if k in keys and v != KEEP and (bad := dest_file(root, v)[1])]
    dests = {}
    for u in units:
        d = u.to or over.get(items[u.at][1], KEEP)
        if d != KEEP:
            dests[u.at] = d
            if u.to and (bad := dest_file(root, d)[1]):
                why.append(f"{DOC}:{u.at + 1}: {bad}")
    if why:
        raise Refused(why)
    return lines, units, items, dests, {at: it for at, it in items.items() if it[1] not in over}


def per_dest(units, dests):
    by = defaultdict(list)
    for u in units:
        if u.at in dests:
            by[dests[u.at]].append(u)
    return dict(sorted(by.items(), key=lambda d: docs.id_key(d[0])))


def cmd_plan(args):
    lines, units, items, dests, left = evaluate(args.root, args.overrides)
    by = per_dest(units, dests)
    print(f"{DOC}: {len(units)} units; {len(dests)} to {len(by)} files, {len(units) - len(dests)} stay ({len(left)} listed)")
    for d, us in by.items():
        print(f"{d}\t{len(us)}")
    print_list(left)
    return 0


def print_list(left):
    by = defaultdict(list)
    for at, (cls, key) in left.items():
        by[cls].append(f"{at + 1}\t{cls}\t{key}")
    for cls, rows in by.items():
        print(f"== {cls} ({len(rows)})\n" + "\n".join(rows))
    print("items: " + (", ".join(f"{c} {len(r)}" for c, r in by.items()) or "none"))


def label_re(label):
    return re.compile(rf"- {re.escape(label)}[:：]")


def put(text, label, units):
    """The text with the units' lines two spaces in at the end of its label's items, or after a new
    label at its end; None when it does not end with a line end."""
    lines = text.split("\n")
    if lines[-1] != "":
        return None
    items = [INDENT + x for u in units for x in u.lines]
    at = next((i for i, x in enumerate(lines) if label_re(label).match(x)), None)
    if at is None:
        return "\n".join(lines[:-1] + [f"- {label}:", *items, ""])
    end = at + 1
    while lines[end].startswith(" "):
        end += 1
    return "\n".join(lines[:end] + items + lines[end:])


def cmd_apply(args):
    root = Path(args.root)
    lines, units, _, dests, left = evaluate(root, args.overrides)
    texts, why = {}, []
    for d, us in per_dest(units, dests).items():
        rel = dest_file(root, d)[0]
        texts[rel] = put(repo.read_exact(root, rel), DESTS[repo.kind_of(d).name], us)
        if texts[rel] is None:
            why.append(f"{rel.as_posix()}: does not end with a line end")
    why += [f"{s}: a vim swap file" for rel in [DOC, *texts] for s in docs.swap_files_of(root / rel)]
    if why:
        raise Refused(why)
    out = {i for u in units if u.at in dests for i in range(u.at, u.at + len(u.lines))}
    texts[DOC] = "\n".join(x for i, x in enumerate(lines) if i not in out)
    old = {rel: repo.read_exact(root, rel) for rel in texts}
    try:
        for rel, text in texts.items():
            docs.write_atomic(root / rel, text)
    except BaseException:
        for rel, text in old.items():
            docs.write_atomic(root / rel, text)
        raise
    print(f"moved {len(dests)} units ({len(out)} lines) of {DOC} to {len(texts) - 1} files; {len(units) - len(dests)} stay")
    refs = list(docs.check_refs(docs.Tree(root, []), {rel for rel in texts if rel != DOC}))
    if refs:
        print(f"== body-ref ({len(refs)})\n" + "\n".join(map(str, refs)))
    print_list(left)
    return 0


def before_reader(root, before):
    """fn(rel) -> the text of the tree before (a directory, or a git revision of the root), None if absent."""
    if Path(before).is_dir():
        return lambda rel: repo.read_exact(before, rel) if (Path(before) / rel).is_file() else None

    def read(rel):
        argv = ["git", "-C", str(root), "show", f"{before}:{Path(rel).as_posix()}"]
        try:
            r = subprocess.run(argv, capture_output=True, timeout=repo.GIT_TIMEOUT)
            return r.stdout.decode("utf-8") if r.returncode == 0 else None
        except (OSError, subprocess.TimeoutExpired, UnicodeDecodeError) as e:
            raise repo.RepoError(f"`{' '.join(argv)}`: {e}") from e

    return read


def taken_out(before, after, units):
    """(the units not in `after`, why `after` is not `before` with whole units taken out, or None)."""
    starts, moved, j, i = {u.at: u for u in units}, [], 0, 0
    while i < len(before):
        u = starts.get(i)
        if u is None:
            if after[j : j + 1] != [before[i]]:
                return moved, f"{DOC}:{i + 1}: from this line, not the one before with whole units taken out (a line changed or lost)"
            i, j = i + 1, j + 1
        else:
            if after[j : j + len(u.lines)] == list(u.lines):
                j += len(u.lines)
            else:
                moved.append(u)
            i += len(u.lines)
    return moved, None if j == len(after) else f"{DOC}: {len(after) - j} line(s) more at the end"


def put_in(rel, label, before, after):
    """(the lines put in, two spaces out) or why `after` is not `before` with them put as `apply` does."""
    p = 0
    while p < min(len(before), len(after)) and before[p] == after[p]:
        p += 1
    s = 0
    while s < min(len(before), len(after)) - p and before[-1 - s] == after[-1 - s]:
        s += 1
    new = after[p : len(after) - s]
    if p + s != len(before) or not new:
        return f"{rel}: not lines put in at one place"
    has = any(label_re(label).match(x) for x in before)
    if new[0] == f"- {label}:" and not has and s == 1:
        new = new[1:]
    else:
        top = next((x for x in reversed(before[:p]) if not x.startswith(" ")), "")
        if not (has and label_re(label).match(top) and not "".join(before[p : p + 1]).startswith(" ")):
            return f"{rel}:{p + 1}: the lines put in are not at the end of `- {label}:`"
    if not new or not all(x.startswith(INDENT) for x in new):
        return f"{rel}:{p + 1}: a line put in is not {len(INDENT)} spaces in"
    return [x[len(INDENT) :] for x in new]


def cmd_verify(args):
    root, read = Path(args.root), before_reader(args.root, args.before)
    before = read(DOC)
    if before is None:
        raise repo.RepoError(f"{DOC}: not in the tree before")
    units = read_units(before.split("\n"))
    moved, why = taken_out(before.split("\n"), repo.read_exact(root, DOC).split("\n"), units)
    if why:  # the units moved are not known: the files are not compared
        print(f"{why}\nmigrate_carryovers.py verify: 1 difference(s)")
        return 1
    diffs, by_lines = [], defaultdict(list)
    for u in moved:
        by_lines[u.lines].append(u)
    found, files = {}, 0
    for name, label in DESTS.items():
        kind = repo.KIND[name]
        for p in sorted((root / kind.dir).glob("*.md")):
            rel = p.relative_to(root)
            after, was = repo.read_exact(root, rel), read(rel)
            if was == after:
                continue
            files += 1
            got = f"{rel}: not in the tree before"
            if was is not None:
                got = put_in(rel.as_posix(), label, was.split("\n"), after.split("\n"))
            if isinstance(got, str):
                diffs.append(got)
                continue
            put = read_units(got)
            if sum(len(u.lines) for u in put) != len(got) or put[0].at != 0:
                diffs.append(f"{rel}: lines put in that are not units")
                continue
            order = []
            for u in put:
                if not by_lines[u.lines]:
                    diffs.append(f"{rel}: a unit put in is not one taken out: {u.lines[0][:60]}")
                    continue
                v = by_lines[u.lines].pop(0)
                found[v.at] = p.stem
                order.append(v.at)
                if v.to is not None and v.to != p.stem:
                    diffs.append(f"{rel}: {u.lines[0][:60]} goes to {v.to}")
            if order != sorted(order):
                diffs.append(f"{rel}: the units are not in their order")
    diffs += [f"{DOC}:{u.at + 1}: taken out, not put in: {u.lines[0][:60]}" for u in moved if u.at not in found]
    kept = [u for u in units if u not in moved and u.to is not None]
    diffs += [f"{DOC}:{u.at + 1}: stays, but its head names {u.to}" for u in kept]
    diffs += [f"{DOC}: no unit moved (is `--before` the tree before `apply`?)"] * (not moved and not diffs)
    print(f"{DOC}: {len(units)} units before, {len(moved)} moved, {len(units) - len(moved)} stay; {files} files changed")
    if diffs:
        print("\n".join(diffs) + f"\nmigrate_carryovers.py verify: {len(diffs)} difference(s)")
        return 1
    print("migrate_carryovers.py verify: the same")
    return 0


COMMANDS = {"plan": cmd_plan, "apply": cmd_apply, "verify": cmd_verify}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="migrate_carryovers.py", description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in COMMANDS:
        p = sub.add_parser(name)
        p.add_argument("--root", type=Path, default=ROOT)
        if name == "verify":
            p.add_argument("--before", required=True, help="the tree before: a directory, or a git revision of the root")
        else:
            p.add_argument("--overrides", type=Path)
    args = ap.parse_args(argv)
    try:
        return COMMANDS[args.cmd](args)
    except Refused as e:
        print("\n".join(e.args[0]) + f"\nmigrate_carryovers.py {args.cmd}: refused; nothing is written")
        return 1
    except (repo.RepoError, docs.DocsError) as e:
        print(f"migrate_carryovers.py {args.cmd}: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
