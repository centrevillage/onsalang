#!/usr/bin/env python3
"""Move a table of IDs into one file per ID (X-2 step 6, MG-2). The rules of a kind are one value of
`Rule` in RULES; the frame (`plan`, `apply`, the overrides) reads only them.

    python3 -B migrate_tables.py plan  --kind S|D|K|Q|A|R|W [--root DIR] [--overrides TOML]
    python3 -B migrate_tables.py apply --kind S|D|K|Q|A|R|W [--root DIR] [--overrides TOML]
    python3 -B migrate_tables.py verify --kind S|D|K|Q|A|R|W [--root DIR] --before DIR|REV

A kind is a table (S, A, W: a row is a unit, a cell an item of the body; W has a table a stage, its
columns `作業` the title and `依存`, `規模`, `役割・印` head fields, `Rule.head`) or headings (D, K, Q,
R: a unit from its heading `### D-NN <title>` to the next heading as high or a line `---`; its text
moved byte for byte, the blank line before the heading taken out with it). The rows of a section
join the units as items after the text (`Rows`): Q's §4 (one row an ID), R's §8 (the rows of an ID
in their order, two items a row; a row of no heading makes a file of its items alone).

Exit: 0 done; 1 refused (an override not in the list, a finding of the check before writing, a
condition of `apply` not met; nothing is written); 2 an error of the tool (a document it cannot read,
a table whose header is not the rule's, an ID given twice).

- `plan` writes nothing. It prints the rows read, how many units each rule gave a value, and the list
  of the judgements, a line `ID\\tclass\\tkeys\\trule's value\\ttext` under a heading per class (the
  classes of `count_only` only as a number). With `--overrides` the items they fill are left out.
- `apply` writes the files and takes the table (its header, delimiter and rows) out of its document.
  The document is written first, so `repo.Layout` reads the kind from its directory; the files are
  then checked as `docs.py check` does ((a) and (c) through `docs.check_write`, (b) of the head
  fields) before any is written. On a finding the document is written back and nothing else is
  (exit 1). (b) of the text is only reported (class `body-ref`).
- `verify` compares the tree with the tree before (`--before`: a directory, or a git revision of the
  root read by `git show`): each file read back in the form `apply` writes, its row rebuilt and the
  rows compared as multisets after the closed list NORMALIZED (printed); ✅ against `status`, apart only
  for the IDs of the `status` items of the list made from the rows before; the title one of the
  drafts' and the extra items the rule's; the document byte for byte outside the table, the header and
  delimiter rows rebuilt from the columns; the IDs of the rows and of the files; `reverse` against the
  tree before (`tasks`: the rework; R's `fix`: the W of its rows of §8; W: none). A cell of a head
  field (`Rule.head`) of an ID the list of the rows before has an item of its key for is not compared
  (printed with the value written). Exit 1 on any difference.
- The overrides, `[S-276]` / `status = "DECIDED"`: only the (ID, key) the list of the same tree
  accepts (an item's keys for its ID and its partners), the value fitting the field table of the
  README or one of the item's choices; "" or [] is "not written". Anything else refuses them all.
  `[status_of]` / `"保留" = "OPEN"` changes the rule's table of the head words of the status (A).
- Order: each document is read once, a line at a time; each rule is linear in its row. The rules run
  twice (without and with the overrides). No loop waits on a fixed point, so it stops.
"""
import argparse
import re
import subprocess
import sys
import tomllib
from collections import Counter, defaultdict
from itertools import takewhile
from dataclasses import dataclass, replace
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools"))
import docs  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402

TEXT_MAX = 120  # the characters of the text shown in the list


class Refused(Exception):
    """A condition not met: exit 1, nothing written. `args[0]` are the lines that say why."""


@dataclass(frozen=True)
class Unit:
    id: str
    done: bool
    cells: tuple  # the cells after the ID cell, as the table has them; of a heading: (title, text)
    lines: tuple  # (line number, text) of its rows; of a heading: from it to the last line of its text
    rows: tuple = ()  # of a heading: its `Row`s of `Rule.rows`

    @property
    def text(self):
        return "\n".join(t for _, t in self.lines)


@dataclass(frozen=True)
class Row:
    line: int
    text: str
    cells: tuple  # the cells after the ID cell
    column: str  # the header's cell after `ID` (`決定`, `決定（2026-10-02）`)
    id_cell: str  # the ID cell as it is (`R-90 (i)`)


@dataclass(frozen=True)
class Rows:
    """The rows of a section that join the units of the headings."""

    start: str
    end: str  # None: to the end of the document
    column: object  # fn(header cells) -> `Row.column`; None: not a table of the rule (a row of an ID in it: an error)
    items: object  # fn(unit) -> [(label, text)], the items put after its text
    unrow: object  # fn(ID, head values, [(label, text)] read back) -> the rows rebuilt as `want_pieces`
    many: bool = False  # the rows of an ID gather (R); else one row an ID
    alone: bool = False  # a row of no heading makes a unit (R); else it stays, listed `no-heading`
    words: dict = None  # the ID cells with a word after the ID that move (R); another stays, listed `id-cell`


@dataclass(frozen=True)
class Item:
    """A line of the list of the judgements."""

    id: str
    cls: str
    keys: tuple  # the keys an override may set, for `id` and `partners`; none: only reported
    value: object  # the rule's value (None: not written)
    text: str
    partners: tuple = ()
    choices: tuple = None  # the values an override may take, when not the field table's


@dataclass(frozen=True)
class Rule:
    kind: str  # `repo.KIND`: the spelling of the IDs, the directory, the table (`old`)
    columns: tuple  # the header of the table
    labels: dict  # column -> label of the body (one to one, MG-F)
    extra: tuple  # the labels of the body that come from no column (of a heading: put after its text)
    done: str  # the `status` of a row with ✅; None: no ✅ to compare (D, K, Q, A)
    context: object  # fn(root) -> dict, the other documents read once
    fields: tuple  # (key, fn(unit, ctx, values) -> (value, items)); `values` holds the keys before
    title: object  # fn(unit, ctx) -> (title, {label: text}, items)
    notes: tuple  # fn(unit, ctx, values) -> items: judgements with no value to write
    reverse: tuple = None  # (head field, fn(read) -> {ID: values}, its source) from the tree before (`verify`)
    count_only: tuple = ()  # the classes printed only as a number
    source: tuple = None  # (document, first heading, next heading, what) when not `repo.KIND`'s `old`
    heading: str = None  # the `#`s of the heading of a unit (D, K, Q, R); None: a table
    gap: int = 1  # the blank lines between the heading and its text (another number is an error)
    rows: Rows = None
    tail: tuple = None  # the patterns of the labels of a group of the items after the text (`extra`)
    status_of: dict = None  # the head word of a cell -> `status`; changed by `[status_of]`
    head: dict = None  # a column written as a head field -> (key, fn(cell, ctx) -> the cell as the field gives it
    # back (NORMALIZED), fn(value) -> the cell) (W); the other columns are the title and the items
    titled: str = None  # the column written as the title (W)


@dataclass(frozen=True)
class Result:
    unit: Unit
    values: dict
    title: str
    extra: dict


# ---------------------------------------------------------------- the frame


def source_of(rule):
    """(document, first heading, next heading, what) of the kind's units (no heading: all of it)."""
    return rule.source or repo.KIND[rule.kind].old


def bounds(lines, start, end, doc):
    """[lo, hi) of the lines from the heading `start` up to the heading `end` (None: the whole)."""
    if start is None:
        return 0, len(lines)
    lo = next((i for i, line in enumerate(lines) if line.startswith(start)), None)
    if lo is None:
        raise repo.RepoError(f"{doc}: the section `{start}` is not found")
    return lo, next((i for i in range(lo + 1, len(lines)) if end is not None and lines[i].startswith(end)), len(lines))


def read_units(root, rule, text=None):
    """(units, [(first, last) line taken out], the lines of the document, the items of the reading)."""
    if rule.heading:
        return read_headings(root, rule, text)
    units, spans, lines = read_table(root, rule, text)
    return units, spans, lines, []


def read_table(root, rule, text=None):
    """(units, [(first, last) line of each table], the lines of its document); `text`: the document's.
    The rows next to each other are a table, each under the rule's header and a delimiter row (W: one
    a stage)."""
    kind = repo.KIND[rule.kind]
    doc, start, end, what = source_of(rule)
    lines = (repo.read_exact(root, doc) if text is None else text).split("\n")
    lo, hi = bounds(lines, start, end, doc)
    row = repo.row_re(kind.pattern)
    at = {i for i in range(lo, hi) if row.match(lines[i])}
    if not at:
        raise Refused([f"{doc} `{start or ''}`: no row of the {what}"])
    units, seen, spans = [], set(), []
    for first in sorted(i for i in at if i - 1 not in at):
        a, last = first - 2, next(i for i in range(first, hi) if i + 1 not in at)
        if a < lo or docs.table_cells(lines[a]) != list(rule.columns) or not docs.DELIMITER.fullmatch(lines[a + 1].strip()):
            raise repo.RepoError(f"{doc}:{a + 1}: no header `| {' | '.join(rule.columns)} |` and delimiter row")
        spans.append((a + 1, last + 1))
        for i in range(first, last + 1):
            m, cells = row.match(lines[i]), docs.table_cells(lines[i])
            if len(cells) != len(rule.columns) or cells[0] != m.group(1) + (m.group(2) or ""):
                raise repo.RepoError(f"{doc}:{i + 1}: not a row `| <ID>[ ✅] | … |` of {len(rule.columns)} cells")
            if m.group(1) in seen:
                raise repo.RepoError(f"{doc}:{i + 1}: {m.group(1)} is given twice")
            seen.add(m.group(1))
            units.append(Unit(m.group(1), bool(m.group(2)), tuple(cells[1:]), ((i + 1, lines[i]),)))
    return units, spans, lines


def read_headings(root, rule, text=None):
    """`read_units` of the kinds written as headings: a unit from its heading to the line before the
    next heading as high or a line `---` (of the text, not in code), less the blank lines at its end;
    the blank line just before the heading is taken out with it. The rows of `rule.rows` join the
    units of their IDs (`read_rows`)."""
    kind = repo.KIND[rule.kind]
    doc, start, end, what = source_of(rule)
    lines = (repo.read_exact(root, doc) if text is None else text).split("\n")
    kinds = docs.line_kinds(lines)[0]
    lo, hi = bounds(lines, start, end, doc)
    head = re.compile(rf"{rule.heading} ({kind.pattern})(?![0-9])(?: (.*))?")
    stop = re.compile(rf"#{{1,{len(rule.heading)}}} .*|---")
    at = [i for i in range(lo, hi) if kinds[i] == docs.TEXT and head.fullmatch(lines[i])]
    if not at:
        raise Refused([f"{doc} `{start}`: no heading `{rule.heading} <ID>` of the {what}"])
    units, ranges, by = [], [], {}
    for h in at:
        m = head.fullmatch(lines[h])
        e = next((i for i in range(h + 1, hi) if kinds[i] == docs.TEXT and stop.fullmatch(lines[i])), hi)
        b = max((i for i in range(h + 1, e) if lines[i] != ""), default=None)
        gap = next(i for i in range(h + 1, e + 1) if i == e or lines[i] != "") - h - 1
        why = ("given twice" if m.group(1) in by else "no text under the heading" if b is None
               else f"{gap} blank line(s) after the heading, the rule's {rule.gap}" if gap != rule.gap else None)  # fmt: skip
        if why:
            raise repo.RepoError(f"{doc}:{h + 1}: {m.group(1)}: {why}")
        by[m.group(1)] = len(units)
        ranges.append((h if h - 1 > lo and lines[h - 1] == "" else h + 1, b + 1))
        body = "\n".join(lines[h + 1 + gap : b + 1])
        units.append(Unit(m.group(1), False, (m.group(2) or "", body), tuple((i + 1, lines[i]) for i in range(h, b + 1))))
    items = []
    if rule.rows:
        more, items = read_rows(rule, kind, lines, kinds, doc, units, by)
        ranges += more
    return units, ranges, lines, items


def read_rows(rule, kind, lines, kinds, doc, units, by):
    """(ranges, items): the rows of `rule.rows` joined to the units of their IDs (`units` and `by`
    changed). A row of no ID, of an ID cell with a word not the rule's, or of no unit (unless `alone`)
    stays, listed. A row of an ID in a table not the rule's, or of other cells than its header, is an
    error; so is a section with no table of the rule."""
    spec, id_re = rule.rows, re.compile(rf"({kind.pattern})(?![0-9])")
    ranges, items, header, column, tables = [], [], None, None, 0
    for i in range(*bounds(lines, spec.start, spec.end, doc)):
        if kinds[i] != docs.TEXT or not lines[i].startswith("|") or docs.DELIMITER.fullmatch(lines[i].strip()):
            continue
        cells = docs.table_cells(lines[i])
        if cells[0] == "ID":
            header, column = cells, spec.column(cells)
            tables += column is not None
            continue
        if header is None:
            raise repo.RepoError(f"{doc}:{i + 1}: a row before the header of its table in `{spec.start}`")
        if (m := id_re.match(cells[0])) is None:
            items.append(Item(cells[0], "other-row", (), None, lines[i]))
            continue
        id_ = m.group(1)
        if column is None or len(cells) != len(header):
            raise repo.RepoError(f"{doc}:{i + 1}: {id_}: not a row of a table of the rule's (`| {' | '.join(header)} |`)")
        k = by.get(id_)
        if cells[0] != id_ and cells[0] not in (spec.words or {}):
            items.append(Item(id_, "id-cell", (), None, lines[i]))
            continue
        if k is None and not spec.alone:
            items.append(Item(id_, "no-heading", (), None, lines[i]))
            continue
        if k is None:
            by[id_] = k = len(units)
            units.append(Unit(id_, False, ("", ""), ()))
        elif units[k].rows and not spec.many:
            raise repo.RepoError(f"{doc}:{i + 1}: {id_} is given twice")
        units[k] = replace(units[k], rows=(*units[k].rows, Row(i + 1, lines[i], tuple(cells[1:]), column, cells[0])))
        ranges.append((i + 1, i + 1))
    if not tables:
        raise repo.RepoError(f"{doc} `{spec.start}`: no table of the rule's")
    return ranges, items


def without(lines, ranges):
    """The lines with the ranges (first, last; from 1) taken out."""
    out = {i for a, b in ranges for i in range(a - 1, b)}
    return [line for i, line in enumerate(lines) if i not in out]


def where(doc, ranges):
    if len(ranges) == 1:
        return f"{doc}:{ranges[0][0]}-{ranges[0][1]}"
    return f"{doc}: {len(ranges)} ranges"


STATUS_OF = "status_of"  # the table of the overrides that changes `Rule.status_of`


def read_overrides(path):
    """({(ID, key): value or None}, why the file is not of `[ID]` tables, {head word: status} of
    `[status_of]`)."""
    if path is None:
        return {}, [], {}
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
        raise repo.RepoError(f"{path}: {e}") from e
    out, why = {}, []
    maps = data.pop(STATUS_OF, {})
    if not isinstance(maps, dict):
        why.append(f"{STATUS_OF}: not a table `[{STATUS_OF}]`")
    for id_, keys in data.items():
        if not isinstance(keys, dict):
            why.append(f"{id_}: not a table `[{id_}]`")
            continue
        for key, v in keys.items():
            out[(id_, key)] = None if v == "" or v == [] else v
    return out, why, maps if isinstance(maps, dict) else {}


def context(rule, root, maps=None, units=()):
    """`rule.context(root)` and the IDs of the units read (`ids`), with `status_of`: the rule's table
    changed by `maps`."""
    ctx = {**rule.context(root), "ids": [u.id for u in units]}
    if rule.status_of is not None:
        ctx[STATUS_OF] = {**rule.status_of, **(maps or {})}
    return ctx


def check_overrides(overrides, items, table):
    """Why the overrides are refused: an (ID, key) no item accepts, a value that does not fit."""
    accepted = {(i, k): it for it in items for i in (it.id, *it.partners) for k in it.keys}
    why = []
    for (id_, key), v in overrides.items():
        it = accepted.get((id_, key))
        if it is None:
            why.append(f"{id_} {key}: not in the list of the judgements")
        elif v is None:
            continue
        elif it.choices is not None:
            if v not in it.choices:
                why.append(f"{id_} {key}: {v!r} is not one of {' / '.join(it.choices)}")
        elif not isinstance(table, docs.FieldTable):
            why.append(f"{id_} {key}: no field table to check the value ({table})")
        elif key not in table.fields:
            why.append(f"{id_} {key}: not a field of {table.readme.as_posix()}")
        elif bad := table.check_value(key, v):
            why.append(f"{id_} {key}: {bad}")
    return why


def run(rule, units, ctx, overrides):
    """(results, items): the rules on each unit, an override taking the place of a rule's value."""
    results, items = [], []
    for u in units:
        own = {k: v for (i, k), v in overrides.items() if i == u.id}
        values = {}
        for key, fn in rule.fields:
            v, found = fn(u, ctx, values)
            items += found
            values[key] = own[key] if key in own else v
        values.update({k: v for k, v in own.items() if k not in values and k != "title"})
        title, extra, found = rule.title(u, ctx)
        items += found
        for note in rule.notes:
            items += note(u, ctx, values)
        results.append(Result(u, values, own.get("title", title), extra))
    return results, items


def evaluate(root, rule, overrides_path, table):
    """(units, ranges, lines, results, items) with the overrides checked against the list of the tree."""
    units, ranges, lines, found = read_units(root, rule)
    overrides, why, maps = read_overrides(overrides_path)
    if maps and rule.status_of is None:
        why.append(f"{STATUS_OF}: the rules of {rule.kind} have no table of the head words")
    for word, v in maps.items():
        bad = table.check_value("status", v) if isinstance(table, docs.FieldTable) else str(table)
        if bad:
            why.append(f"{STATUS_OF} {word}: {bad}")
    ctx = context(rule, root, maps, units)
    items = found + run(rule, units, ctx, {})[1]
    why += check_overrides(overrides, items, table)
    if why:
        raise Refused(why)
    results = run(rule, units, ctx, overrides)[0]
    filled = {(i, k) for i, k in overrides}
    left = [it for it in items if not any((i, k) in filled for i in (it.id, *it.partners) for k in it.keys)]
    return units, ranges, lines, results, left


def shown(v):
    if v is None:
        return "-"
    if isinstance(v, list):
        return ", ".join(map(shown, v))
    return v.isoformat() if isinstance(v, date) else str(v)


def print_items(rule, items):
    by = defaultdict(list)
    for it in items:
        by[it.cls].append(it)
    for cls, found in by.items():
        if cls in rule.count_only:
            continue
        print(f"== {cls} ({len(found)})")
        for it in found:
            keys = ",".join(it.keys) + (f" ({', '.join(it.partners)})" if it.partners else "")
            print("\t".join([it.id, cls, keys, shown(it.value), it.text[:TEXT_MAX]]))
    print("items: " + (", ".join(f"{cls} {len(found)}" for cls, found in by.items()) or "none"))


def cmd_plan(args, rule):
    kind = repo.KIND[rule.kind]
    table = docs.field_table(docs.Tree(args.root, []), kind)
    units, ranges, _, results, items = evaluate(args.root, rule, args.overrides, table)
    alone = sum(not u.lines for u in units)  # R's units of rows alone
    what = f"{len(units) - alone} headings" + (f" and {alone} of rows alone" if alone else "") if rule.heading else f"{len(units)} rows"
    print(f"{where(source_of(rule)[0], ranges)}: {what} -> {len(units)} files in {kind.dir}/")
    counts = Counter()
    for r in results:
        counts.update(k for k, v in r.values.items() if v is not None)
        counts.update(["title"] * bool(r.title) + [k for k in r.extra] if isinstance(r.extra, dict) else [k for k, _ in r.extra])
    status = Counter(r.values.get("status") for r in results)
    print("values: " + ", ".join(f"{k} {n}" for k, n in counts.items()) + "; status " + ", ".join(f"{k} {n}" for k, n in status.items()))
    print_items(rule, items)
    return 0


def render(rule, kind, table, r):
    body = [f"# {r.unit.id}" + (f" {r.title}" if r.title else ""), ""]
    cells = dict(zip(rule.columns[1:], r.unit.cells))
    for column, label in rule.labels.items():
        text = cells[column].replace("\\|", "|")
        body.append(f"- {label}:" + (f" {text}" if text else ""))
    body += [f"- {label}: {r.extra[label]}" for label in rule.extra if r.extra.get(label)]
    return docs.fmt_text(docs.render_head(r.values, table.order) + "\n".join(body) + "\n")[0]


def render_heading(rule, kind, table, r):
    """The head fields, `# <ID>[ <title>]`, a blank line, the text under the heading as it is, and the
    extra items (their long lines broken, as `docs.fmt_text`)."""
    text = r.unit.cells[BODY]  # none: a unit of rows alone
    body = [f"# {r.unit.id}" + (f" {r.title}" if r.title else ""), "", *([text] if text else [])]
    tail = [f"- {label}: {t}" for label, t in r.extra if t]
    return docs.render_head(r.values, table.order) + "\n".join(body + [docs.fmt_text(x)[0] for x in tail]) + "\n"


def check_before(root, kind, texts):
    """(the findings that stop the writing, the findings of (b) in the text), as if `texts` were written."""
    new = [(kind.name, rel.stem, rel) for rel in texts]
    stop = [str(f) for f in docs.check_write(root, texts, new)]
    tree = docs.Tree(root, [])
    for rel, text in texts.items():
        tree._lines[rel] = text.split("\n")  # as `docs.check_write` does
    tree.index.files[kind.name].update({rel.stem: rel for rel in texts})
    refs = [f for f in docs.check_refs(tree) if f.path in texts]
    end = {rel: text.split("\n").index(docs.HEAD_LINE, 1) + 1 for rel, text in texts.items()}
    return stop + [str(f) for f in refs if f.line <= end[f.path]], [f for f in refs if f.line > end[f.path]]


def readme_labels(tree, kind):
    """The labels ``- `<label>` …`` anywhere in the README of the kind's directory, else of the one up
    (as `docs.body_labels`). The moved labels need not be under its `## 本文のラベル`, which is the
    template of `docs.py new` (the new files keep their own labels)."""
    d = Path(kind.dir)
    for rel in (d / "README.md", d.parent / "README.md"):
        if (tree.root / rel).is_file():
            lines, kinds = tree.lines(rel), tree.kinds(rel)[0]
            found = [m.group(1) for line, k in zip(lines, kinds)
                     if k == docs.TEXT and (m := docs.LABEL_ITEM.match(line))]
            if found:
                return found
    return []


def cmd_apply(args, rule):
    root, kind = Path(args.root), repo.KIND[rule.kind]
    doc = source_of(rule)[0]
    tree = docs.Tree(root, [])
    table, why = docs.field_table(tree, kind), []
    if not isinstance(table, docs.FieldTable):
        why.append(str(table))
    labels = readme_labels(tree, kind)
    # the labels of a heading's text are its own (DF-4: as they are), not checked; the items the tool writes are
    missing = [x for x in (*rule.labels.values(), *rule.extra) if x not in labels]
    if missing:
        why.append(f"{kind.dir}: the labels {', '.join(missing)} are not explained in its README (``- `<label>`: …``)")
    there = sorted(p.name for p in (root / kind.dir).glob("*.md") if re.fullmatch(kind.pattern, p.name[:-3]))
    if there:
        why.append(f"{kind.dir}/: files of IDs are there ({there[0]} …); apply to the tree before the stage")
    if not (root / kind.dir).is_dir():
        why.append(f"{kind.dir}/: not there (its README comes before the stage)")
    why += [f"{doc}: the swap file {s.name} (open in vim?)" for s in docs.swap_files_of(root / doc)]
    if why:
        raise Refused(why)
    units, ranges, lines, results, _ = evaluate(root, rule, args.overrides, table)
    write = render_heading if rule.heading else render
    texts = {Path(kind.dir) / f"{r.unit.id}.md": write(rule, kind, table, r) for r in results}
    old, written = "\n".join(lines), []
    try:
        docs.write_atomic(root / doc, "\n".join(without(lines, ranges)))
        stop, refs = check_before(root, kind, texts)
        if stop:
            raise Refused(stop)
        for rel, text in texts.items():
            docs.write_new(root / rel, text)
            written.append(rel)
    except BaseException:
        for rel in written:
            (root / rel).unlink(missing_ok=True)
        docs.write_atomic(root / doc, old)
        raise
    print(f"wrote {len(texts)} files in {kind.dir}/; took out {where(doc, ranges)} ({len(lines) - len(without(lines, ranges))} lines)")
    if refs:
        print(f"== body-ref ({len(refs)})")
        print("\n".join(map(str, refs)))
    return 0


# The closed list of what `verify` reads as the same (MG-2); any other difference fails.
NORMALIZED = (
    "the order of the rows (compared as multisets)",
    "`\\|` read as `|` on both sides",
    "a line going on with two spaces (`docs.fmt_text`) joined to the line before",
    "W's `依存`: a range `W3-03〜W3-12` opened to the IDs of the rows between them",
)
APART = "…"  # a cell of a head field the list of the rows before has an item of (`Rule.head`): not compared


def before_reader(root, before):
    """fn(rel) -> the text of a document of the tree before: a directory, or a git revision of the root."""
    if Path(before).is_dir():
        return lambda rel: repo.read_exact(before, rel)

    def read(rel):
        argv = ["git", "-C", str(root), "show", f"{before}:{Path(rel).as_posix()}"]
        try:
            r = subprocess.run(argv, capture_output=True, timeout=repo.GIT_TIMEOUT)
            if r.returncode != 0:
                raise repo.RepoError(f"`{' '.join(argv)}` failed: {r.stderr.decode(errors='replace').strip()}")
            return r.stdout.decode("utf-8")
        except (OSError, subprocess.TimeoutExpired, UnicodeDecodeError) as e:
            raise repo.RepoError(f"`{' '.join(argv)}`: {e}") from e

    return read


def split_file(rel, text):
    """(head values, the lines after the head fields, the match of `# <ID>[ <title>]`), or why the file
    is not of the form the renderers write (the head fields, the heading, a blank line, a line end at
    the end)."""
    head = docs.read_head(text)
    if head.values is None:
        return f"{rel}:{head.error_line}: {head.error}"
    if not text.endswith("\n"):
        return f"{rel}: does not end with a line end"
    lines = head.body.split("\n")[:-1]
    m = re.fullmatch(rf"# {re.escape(rel.stem)}(?: (.*))?", lines[0]) if lines else None
    if m is None or lines[1:2] != [""]:
        return f"{rel}: not `# {rel.stem}[ <title>]` and a blank line after the head fields"
    return head.values, lines, m


def read_back(rule, rel, text):
    """(head values, title, cells, {extra label: text}) of a written file, or why it is not of the form
    `render` writes (`split_file`, the items of the labels in order, the extra items)."""
    if isinstance(split := split_file(rel, text), str):
        return split
    values, raw, m = split
    lines = []
    for line in raw:
        if line.startswith("  ") and len(lines) > 2:
            lines[-1] += line[2:]
        else:
            lines.append(line)
    items, cells, extra = lines[2:], [], {}
    for label in rule.labels.values():
        line = items.pop(0) if items else ""
        if line != f"- {label}:" and not line.startswith(f"- {label}: "):
            return f"{rel}: `- {label}:` is not where it is due: {line[:60]}"
        cells.append(line[len(label) + 4 :])
    for label in rule.extra:
        if items and items[0].startswith(f"- {label}: "):
            extra[label] = items.pop(0)[len(label) + 4 :]
    if items:
        return f"{rel}: a line not of the written form: {items[0][:60]}"
    return values, m.group(1), cells, extra


def read_back_heading(rule, rel, text):
    """`read_back` of the form `render_heading` writes: the cells are the lines of the text; the extra
    items, [(label, text)], a group of the last items not going on with two spaces whose labels are
    `rule.tail` in order (as many groups as there are with `rows.many`)."""
    if isinstance(split := split_file(rel, text), str):
        return split
    values, lines, m = split
    body, extra, tail = lines[2:], [], rule.tail or tuple(map(re.escape, rule.extra))
    while tail:
        at = [i for i, x in enumerate(body) if not x.startswith("  ")][-len(tail) :]
        found = [re.match(rf"- ({t}): ", body[i]) for t, i in zip(tail, at)] if len(at) == len(tail) else [None]
        if not all(found):
            break
        ends = [*at[1:], len(body)]
        extra[:0] = [(f.group(1), body[i][f.end() :] + "".join(x[2:] for x in body[i + 1 : e])) for f, i, e in zip(found, at, ends)]
        body = body[: at[0]]
        if not rule.rows.many:
            break
    return values, m.group(1), body, extra


def table_line(cells):
    """`| a | b |`, an empty cell `| |`."""
    return "|" + "".join(f" {c} |" if c else " |" for c in cells)


def row_text(rule, id_, cell_of, apart=()):
    """`| <ID> | … |` of the cells `cell_of(column)`, a cell of `rule.head` in `apart` `…`; `\\|` as `|`."""
    head = rule.head or {}
    cells = [APART if c in head and (id_, head[c][0]) in apart else cell_of(c) for c in rule.columns[1:]]
    return table_line([id_, *cells]).replace("\\|", "|")


def want_pieces(rule, kind, u, ctx=None, apart=()):
    """The texts of the tree before that the unit's file gives back: its row (no ✅; of `rule.head`, the
    row of its cells, those of the head fields as they give them back, when the line is that row), or
    the lines of its heading and its rows of `rule.rows` (each after the column of its header and a
    tab); `\\|` read as `|` in a row."""
    if rule.heading:
        return [u.text] * bool(u.lines) + [f"{r.column}\t{r.text}".replace("\\|", "|") for r in u.rows]
    line, m = u.lines[0][1], repo.row_re(kind.pattern).match(u.lines[0][1])
    line = line[: m.start(2)] + line[m.end(2) :] if m.group(2) else line
    cells = dict(zip(rule.columns[1:], u.cells))
    if rule.head and line == table_line([u.id, *u.cells]):
        return [row_text(rule, u.id, lambda c: rule.head[c][1](cells[c], ctx) if c in rule.head else cells[c], apart)]
    return [line.replace("\\|", "|")]


def got_pieces(rule, id_, values, title, cells, extra, apart=()):
    """`want_pieces` rebuilt from a file read back (the rows by `rule.rows.unrow`)."""
    if rule.head:
        by = {**dict(zip(rule.labels, cells)), rule.titled: title or ""}
        return [row_text(rule, id_, lambda c: rule.head[c][2](values.get(rule.head[c][0])) if c in rule.head else by[c], apart)]
    if not rule.heading:
        return [table_line([id_, *cells]).replace("\\|", "|")]
    out = []
    if title is not None or cells:  # none: a unit of rows alone
        out.append("\n".join([f"{rule.heading} {id_}" + ("" if title is None else f" {title}"), *[""] * rule.gap, *cells]))
    return out + (rule.rows.unrow(id_, values, extra) if extra else [])


def cmd_verify(args, rule):
    root, kind = Path(args.root), repo.KIND[rule.kind]
    doc, read = source_of(rule)[0], before_reader(args.root, args.before)
    units, ranges, old, _ = read_units(root, rule, read(doc))
    ctx, by = context(rule, root, units=units), {u.id: u for u in units}
    listed = run(rule, units, ctx, {})[1]
    allowed = {it.id for it in listed if it.cls == "status"}
    head = {k: c for c, (k, *_) in (rule.head or {}).items()}  # key -> column
    apart = {(it.id, it.cls) for it in listed if it.cls in head}
    key, reverse_of, origin = rule.reverse or (None, lambda read: {}, None)
    reverse = reverse_of(read)
    print("normalized: " + "; ".join(NORMALIZED) + ". ✅ is compared with `status` on its own")
    files = {p.stem: p.relative_to(root) for p in sorted((root / kind.dir).glob("*.md")) if re.fullmatch(kind.pattern, p.stem)}
    bad, swapped, cut, want, got, n_read = [], [], [], Counter(), Counter(), 0
    what = "headings" if rule.heading else "rows"
    if set(files) != set(by):
        bad.append(f"IDs: {len(by)} {what}, {len(files)} files; no file: {sorted(set(by) - set(files))[:10]}, "
                   f"no unit: {sorted(set(files) - set(by))[:10]}")  # fmt: skip
    for u in units:
        want.update(want_pieces(rule, kind, u, ctx, apart))
    for id_, rel in files.items():
        back = (read_back_heading if rule.heading else read_back)(rule, rel, repo.read_exact(root, rel))
        if isinstance(back, str):
            bad.append(back)
            continue
        values, title, cells, extra = back
        got.update(got_pieces(rule, id_, values, title, cells, extra, apart))
        n_read += 1
        if (u := by.get(id_)) is None:
            continue
        cells_of = dict(zip(rule.columns[1:], u.cells))
        cut += [f"{id_}: `{head[k]}` {cells_of[head[k]]} -> {shown(values.get(k))}" for i, k in sorted(apart) if i == id_]
        if rule.done is not None and (values.get("status") == rule.done) != u.done:
            line = f"{id_}: {'✅' if u.done else 'no ✅'} -> {values.get('status')}"
            (swapped if id_ in allowed else bad).append(line + ("" if id_ in allowed else " (not a `status` item)"))
        rule_title, rule_extra, items = rule.title(u, ctx)
        if title not in {None, rule_title, *(c for it in items for c in it.choices or ())}:
            bad.append(f"{rel}: the title {title!r} is not one of the drafts'")
        if extra != ({k: v for k, v in rule_extra.items() if v} if isinstance(rule_extra, dict) else [p for p in rule_extra if p[1]]):
            bad.append(f"{rel}: the extra items {extra} are not the rule's {rule_extra}")
        if values.get(key) != (reverse.get(id_) or None):
            bad.append(f"{rel}: `{key}` is {values.get(key)}, {origin} has {reverse.get(id_)}")
    bad += [f"lost: {row[:120]}" for row in (want - got).elements()] + [f"new: {row[:120]}" for row in (got - want).elements()]
    new, kept = repo.read_exact(root, doc).split("\n"), without(old, ranges)
    if new != kept:
        at = next((i for i, (a, b) in enumerate(zip(new, kept)) if a != b), min(len(new), len(kept)))
        bad.append(f"{doc}:{at + 1}: outside the units, the document is not what it was")
    for a, _ in [] if rule.heading else ranges:
        if old[a - 1 : a + 1] != ["| " + " | ".join(rule.columns) + " |", "|" + "---|" * len(rule.columns)]:
            bad.append(f"{doc}:{a}: the header and delimiter rows are not rebuilt from the columns")
    with_key = {i for i, rel in files.items() if i in by}
    if set(reverse) - with_key:
        bad.append(f"{key}: {origin} names {sorted(set(reverse) - with_key)[:10]}, which have no file")
    print(f"round trip: {sum(want.values())} {'rows' if not rule.heading else 'headings and rows' if rule.rows else 'headings'}, {n_read} files read back; "
          f"IDs {len(files)}" + (f"; `{key}` of {len(reverse)} {rule.kind} from {origin}" if rule.reverse else "")
          + f"; ✅ and status apart (the list's): {len(swapped)}" + (f"; cells apart (the list's): {len(cut)}" if rule.head else ""))  # fmt: skip
    for line in swapped + cut + bad:
        print(line)
    print(f"migrate_tables.py verify: {len(bad)} difference(s)" if bad else "migrate_tables.py verify: the same")
    return 1 if bad else 0


# ---------------------------------------------------------------- the rules of S (MG-4 (4a))

ITEM, PROPOSAL, WHEN = 0, 1, 2  # the cells after the ID
CHANGES = (Path("docs") / "onsa-0.3-changes.md", "## 4.", "## 5.", ["ID", "内容", "仕様"])
GAPS = "docs/spec-gaps-*.md"
GAP_TITLE = re.compile(r"### (S-\d+)(?![0-9])\s*(.*)")
GAP_GROUP = re.compile(r"## 第 (\d+) 組（[^）]*）: (.*)")
GROUP_IN_TEXT = re.compile(r"第\s*(\d+)\s*組")
TASKS_COLUMN = "実現する決定"
DATE = r"\d{4}-\d{2}-\d{2}"
DATED = re.compile(rf"({DATE}) 決定")
# `docs/implementation-tasks.md` (its first paragraph): "`S` は 2026-10-02 に全て決定し", the next being S-173.
ALL_DECIDED = (172, date(2026, 10, 2))
STATUS_KEYS = ("status", "decided")
AMEND_KEYS = ("amends", "amended_by")
WHEN_W = re.compile(rf"{docs.STAGE.pattern}|{repo.KIND['W'].pattern}")


def ids_of(text, kinds):
    return [m.group(0) for m in repo.ID_RE.finditer(text) if repo.kind_of(m.group(0)).name in kinds]


def excerpt(text, at):
    return text[max(0, at - 20) :]


def to_date(s, u):
    try:
        return date.fromisoformat(s)
    except ValueError as e:
        raise repo.RepoError(f"{u.id}: {s}: {e}") from e


def s_reverse(read, kind="S"):
    """{S: [W…]} (of `kind`) from the column `実現する決定` of the rework §3, in the order of the table;
    `read(rel)` gives a document (of the tree, or of the tree before for `verify`)."""
    tasks = defaultdict(list)
    doc, start, end, _ = repo.KIND["W"].old
    col, wrow = None, repo.row_re(repo.KIND["W"].pattern)
    for line in repo.section(read(doc), start, end, doc).split("\n"):
        cells = docs.table_cells(line) if line.startswith("|") else []
        if cells[:1] == ["ID"]:
            if TASKS_COLUMN not in cells:
                raise repo.RepoError(f"{doc}: a header of `{start}` with no `{TASKS_COLUMN}`: {line}")
            col = cells.index(TASKS_COLUMN)
        elif m := wrow.match(line):
            if col is None or len(cells) <= col:
                raise repo.RepoError(f"{doc}: the row {m.group(1)} has no `{TASKS_COLUMN}`")
            for s in ids_of(cells[col], (kind,)):
                if m.group(1) not in tasks[s]:
                    tasks[s].append(m.group(1))
    return tasks


def s_context(root):
    tasks, changes = s_reverse(lambda rel: repo.read(root, rel)), defaultdict(list)
    doc, start, end, header = CHANGES
    inside = False
    for line in repo.section(repo.read(root, doc), start, end, doc).split("\n"):
        cells = docs.table_cells(line) if line.startswith("|") else None
        if cells is None or cells == header:
            inside = cells is not None
        elif inside and not docs.DELIMITER.fullmatch(line.strip()):
            if len(cells) != len(header):
                raise repo.RepoError(f"{doc}: a row of `{start}` of {len(cells)} cells: {line[:60]}")
            for s in ids_of(cells[0], ("S",)):
                changes[s].append(cells[-1])
    titles, groups = defaultdict(list), defaultdict(list)
    for p in sorted(Path(root).glob(GAPS)):
        lines = repo.read(root, p.relative_to(root)).split("\n")
        for line, k in zip(lines, docs.line_kinds(lines)[0]):
            if k != docs.TEXT:
                continue
            if m := GAP_TITLE.fullmatch(line):
                titles[m.group(1)].append((p.name, line, m.group(2).strip()))
            elif m := GAP_GROUP.fullmatch(line):
                for s in ids_of(m.group(2), ("S",)):
                    groups[s].append(int(m.group(1)))
    for name, found in (("rows of W with S", tasks), ("rows of S in the changes §4", changes), (GAPS, titles)):
        if not found:
            raise repo.RepoError(f"no {name} read; the rules would run on nothing")
    return {"tasks": tasks, "changes": changes, "titles": titles, "groups": groups, "heads": spec_heads(root)}


def spec_heads(root):
    """{"spec" / "tools": the numbers of the headings} of the spec and of the spec of the tools."""
    heads = {"spec": repo.spec_doc(root).text, "tools": repo.tools_doc(root).text}
    return {k: set(spec_blocks.headings(v)) for k, v in heads.items()}


def last_decision(text):
    """The text inside the last `決定（` up to its `）` (the full-width brackets counted; to the end
    when it does not close), or None."""
    at = text.rfind("決定（")
    if at < 0:
        return None
    depth = 0
    for j in range(at + 2, len(text)):
        depth += {"（": 1, "）": -1}.get(text[j], 0)
        if depth == 0:
            return text[at + 3 : j]
    return text[at + 3 :]


def s_status(u, ctx, values):
    proposal = u.cells[PROPOSAL]
    if proposal.startswith("取り下げ"):
        return "DROPPED", [Item(u.id, "status", STATUS_KEYS, "DROPPED", proposal)] if u.done else []
    if u.done:
        return "DECIDED", []
    at = u.text.find("決定（")
    return "OPEN", [] if at < 0 else [Item(u.id, "status", STATUS_KEYS, "OPEN", excerpt(u.text, at))]


def s_spec(u, ctx, values):
    """From the row of the changes §4 (no `§` there: not written), else from the item; `onsa-tools.md`
    read as `tools.md`. A section that is not a numbered heading is left out and listed."""
    return spec_of(u, ctx["changes"].get(u.id) or [u.cells[ITEM]], ctx)


def spec_of(u, sources, ctx):
    """(`spec`, items) of the sections in the texts `sources` (`s_spec`)."""
    found = []
    for src in sources:
        for _, num, which in docs.body_sections(src.replace("onsa-tools.md", "tools.md")):
            sec = (f"tools.md §{num}" if which == "tools" else f"§{num}", num, which)
            if which and sec not in found:
                found.append(sec)
    good = [s for s, num, which in found if num in ctx["heads"][which]] or None
    if len(good or []) == len(found):
        return good, []
    return good, [Item(u.id, "spec", ("spec",), good, "、".join(sources))]


def s_tasks(u, ctx, values):
    return list(ctx["tasks"].get(u.id, [])) or None, []


def s_before(u, ctx, values):
    when = u.cells[WHEN]
    return (when if values.get("status") == "OPEN" and re.fullmatch(repo.KIND["W"].pattern, when) else None), []


def s_group(u, ctx, values):
    """The group heading of the drafts (`## 第 N 組（…）: S-…`), else the group in the last `決定（…）`."""
    heads = list(dict.fromkeys(ctx["groups"].get(u.id, [])))
    dec = list(dict.fromkeys(int(n) for n in GROUP_IN_TEXT.findall(last_decision(u.text) or "")))
    found = heads or dec
    if not found:
        return None, []
    if len(found) == 1 and (not heads or not dec or dec == heads):
        return found[0], []
    return None, [Item(u.id, "group", ("group",), None, f"見出し {heads or '-'}、決定（…） {dec or '-'}")]


def s_decided(u, ctx, values):
    """The first date in the last `決定（…）`, else the last `YYYY-MM-DD 決定`, else 2026-10-02 for ✅ up
    to S-172; only for DECIDED."""
    if values.get("status") != "DECIDED":
        return None, []
    m = re.search(DATE, last_decision(u.text) or "")
    if m:
        return to_date(m.group(0), u), []
    dated = DATED.findall(u.text)
    if dated:
        return to_date(dated[-1], u), []
    n, day = ALL_DECIDED
    return (day if u.done and int(u.id[2:]) <= n else None), []


def s_title(u, ctx):
    found = ctx["titles"].get(u.id, [])
    extra = {"元の下書き": "、".join(f"`{name}` の「{line}」" for name, line, _ in found)} if found else {}
    if len(found) > 1:
        titles = tuple(t for *_, t in found)
        return None, extra, [Item(u.id, "title", ("title",), None, " / ".join(titles), choices=titles)]
    return (found[0][2] or None) if found else None, extra, []


def s_amends(u, ctx, values):
    """A sentence (cut at `。`) with `改め` and a decision that is not the row's."""
    hits, said = [], []
    for cell in u.cells:
        for sentence in cell.split("。"):
            new = [i for i in ids_of(sentence, docs.DECISIONS) if i != u.id and i not in hits] if "改め" in sentence else []
            if new:
                hits += new
                said.append(sentence)
    if not hits:
        return []
    partners = tuple(i for i in hits if repo.kind_of(i).name == "S")
    return [Item(u.id, "amends", AMEND_KEYS, None, f"{', '.join(hits)}: {'。'.join(said)}", partners)]


def s_nodest(u, ctx, values):
    """The time to decide is W stages or works, and no work of them has the row in `tasks`."""
    parts = [p.strip() for p in u.cells[WHEN].split("/")]
    if values.get("status") not in ("DECIDED", "OPEN") or not all(WHEN_W.fullmatch(p) for p in parts):
        return []
    tasks = ctx["tasks"].get(u.id, [])
    if any(t == p or t.startswith(p + "-") for p in parts for t in tasks):
        return []
    return [Item(u.id, "nodest" if values["status"] == "DECIDED" else "nodest-open", (), None, u.cells[WHEN])]


S_RULE = Rule(
    kind="S",
    columns=("ID", "項目", "提案", "決める時期"),
    labels={"項目": "空白", "提案": "提案", "決める時期": "時期"},
    extra=("元の下書き",),
    done="DECIDED",
    context=s_context,
    fields=(("status", s_status), ("spec", s_spec), ("tasks", s_tasks), ("before", s_before),
            ("group", s_group), ("decided", s_decided)),  # fmt: skip
    title=s_title,
    notes=(s_amends, s_nodest),
    reverse=("tasks", s_reverse, "the rework"),
    count_only=("nodest-open",),
)

# ---------------------------------------------------------------- the rules of D, K, Q and A (MG-4 (4b))

TITLE, BODY = 0, 1  # the cells of a heading
DOC_PROCESS = Path("docs") / "process-improvement-phase1.md"
# the plan §1 (its first paragraph): "全て 2026-10-01 に案の通り決定。"
D_ALL = re.compile(rf"全て ({DATE}) に案の通り決定。")
DECIDED_ON = re.compile(rf"決定（({DATE})")
DECISION_ITEM = re.compile(r"^- 決定[:（]", re.M)  # `- 決定: …` or `- 決定（2026-10-08、親）: …`
# the parent's table (to be confirmed with the user before the stage; `[status_of]` changes it)
A_STATUS = {"採用": "DECIDED", "不採用": "DECIDED", "保留": "OPEN"}
HEAD_WORD = re.compile(r"[^（(、。\s]*")
DECIDED_KEY = ("decided",)


def decisions_context(kind, decided=None):
    """fn(root) -> {"tasks": the rework's reverse of `kind`, "decided": decided(root)}."""

    def ctx(root):
        out = {"tasks": s_reverse(lambda rel: repo.read(root, rel), kind)}
        if decided:
            out["decided"] = decided(root)
        return out

    return ctx


def d_all_decided(root):
    doc, start, end, _ = D_RULE.source
    m = D_ALL.search(repo.section(repo.read(root, doc), start, end, doc))
    if m is None:
        raise repo.RepoError(f"{doc} `{start}`: no `{D_ALL.pattern}`; the date of D is not known")
    return date.fromisoformat(m.group(1))


def d_reverse(kind):
    return lambda read: s_reverse(read, kind)


def decided_status(u, ctx, values):
    return "DECIDED", []


def d_decided(u, ctx, values):
    """The date of the plan §1; a unit whose text says `決定（<another date>` is listed."""
    other = [d for d in DECIDED_ON.findall(u.cells[BODY]) if d != ctx["decided"].isoformat()]
    return ctx["decided"], [Item(u.id, "decided", DECIDED_KEY, ctx["decided"], ", ".join(other))] if other else []


def k_decided(u, ctx, values):
    """The first date of the first item `- 決定` of the text (none: not written, listed)."""
    m = DECISION_ITEM.search(u.cells[BODY])
    rest = u.cells[BODY][m.start() :].split("\n") if m else [""]
    item = "\n".join([rest[0], *takewhile(lambda x: x.startswith(" "), rest[1:])])
    if d := re.search(DATE, item):
        return to_date(d.group(0), u), []
    return None, [Item(u.id, "decided", DECIDED_KEY, None, item or "no `- 決定`")]


def q_decided(u, ctx, values):
    return (to_date(u.rows[0].cells[1], u) if u.rows else None), []


def unbar(cell):
    return cell.replace("\\|", "|")


def heading_title(rows):
    """fn(unit, ctx): the title of the heading; the extra items from the unit's rows (`Rows.items`)."""
    return lambda u, ctx: (u.cells[TITLE] or None, rows.items(u) if rows else [], [])


def q_items(u):
    return [("決定", unbar(r.cells[0])) for r in u.rows]


def q_unrow(id_, values, extra):
    return [f"決定\t| {id_} | {text} | {shown(values.get('decided'))} |" for _, text in extra]


def q_notes(u, ctx, values):
    found = [] if u.rows else [Item(u.id, "no-row", (), None, u.cells[TITLE])]
    if m := DECISION_ITEM.search(u.cells[BODY]):
        found.append(Item(u.id, "decision-in-body", (), None, u.cells[BODY][m.start() :]))
    return found


def a_status(u, ctx, values):
    """`status_of` of the head word of the cell `状態` (another word: listed)."""
    word = HEAD_WORD.match(u.cells[1]).group(0)
    status = ctx[STATUS_OF].get(word)
    return status, [] if status else [Item(u.id, "status", STATUS_KEYS, None, u.cells[1])]


def a_decided(u, ctx, values):
    """The first date of the cell `状態`, for DECIDED (none: listed)."""
    if values.get("status") != "DECIDED":
        return None, []
    if d := re.search(DATE, u.cells[1]):
        return to_date(d.group(0), u), []
    return None, [Item(u.id, "decided", DECIDED_KEY, None, u.cells[1])]


def heading_rule(kind, source, heading, gap, decided, ctx, extra=(), notes=(), rows=None):
    return Rule(kind=kind, columns=(), labels={}, extra=extra, done=None, context=ctx, title=heading_title(rows),
                fields=(("status", decided_status), ("tasks", s_tasks), ("decided", decided)), notes=notes,
                reverse=("tasks", d_reverse(kind), "the rework"), source=source, heading=heading, gap=gap, rows=rows)  # fmt: skip


D_RULE = heading_rule("D", (repo.DOC_PLAN, "## 1.", "## 2.", "D decisions"), "###", 1, d_decided,
                      decisions_context("D", d_all_decided))  # fmt: skip
K_RULE = heading_rule("K", (repo.DOC_REWORK, "## 1.", "## 2.", "K decisions"), "###", 1, k_decided, decisions_context("K"))
# Q: §2 and its decisions in the rows of §4 (`| Q-NN | 決定 | 日付 |`, put after its text as `- 決定:`)
Q_RULE = heading_rule("Q", (DOC_PROCESS, "## 2.", "## 3.", "Q decisions"), "####", 0, q_decided, decisions_context("Q"),
                      extra=("決定",), notes=(q_notes,),
                      rows=Rows("## 4.", "## 5.", lambda cells: cells[1] if cells == ["ID", "決定", "日付"] else None, q_items, q_unrow))  # fmt: skip
A_RULE = Rule(
    kind="A",
    columns=("ID", "候補", "状態", "実例・理由"),
    labels={"候補": "候補", "状態": "決定", "実例・理由": "理由"},  # DF-4
    extra=(),
    done=None,
    context=decisions_context("A"),
    fields=(("status", a_status), ("tasks", s_tasks), ("decided", a_decided)),
    title=lambda u, ctx: (None, {}, []),
    notes=(),
    reverse=("tasks", d_reverse("A"), "the rework"),
    status_of=A_STATUS,
)

# ---------------------------------------------------------------- the rules of R (MG-4 (5a))

# The ID cells of the review §8 with a word after the ID -> the word in the bracket of `判断（…）`
# (2026-10-17, the user); `r_unrow` reads it back. Another word: the row stays, listed `id-cell`.
R_WORDS = {"R-08 補足": "補足", "R-90 (i)": "i", "R-90 (ii)": "ii", "R-90 (iii)": "iii", "R-90（整合）": "整合",
           "R-96（一部）": "一部", "R-113 / Q-01〜Q-08": "Q-01〜Q-08 と共に"}  # fmt: skip
R_DECISION = re.compile(rf"決定(?:（({DATE})）)?")  # the header of a table of §8: `決定（2026-10-02）`, `決定`
R_JUDGED = re.compile(r"判断(?:（(.*)）)?")
R_ASPECT = re.compile(r"観点 (\d+(?: / \d+)*)")
PART = "｜"  # divides the first item `- 高・直す・観点 1｜場所｜§…（S-…）｜…`


def r_context(root):
    rel, start, end, _ = repo.KIND["W"].old
    table = docs.field_table(docs.Tree(root, []), repo.KIND["R"])
    if not isinstance(table, docs.FieldTable):
        raise repo.RepoError(f"the values of `severity` and `aspect` are the README's: {table}")
    done = repo.rows(repo.section(repo.read(root, rel), start, end, rel), repo.KIND["W"].pattern)
    # the S there are, as `docs.Index.ids` (whose index would read R, in both places before `apply`)
    lay, s = repo.Layout(root), repo.KIND["S"]
    known = {p.stem for p in (Path(root) / s.dir).glob("*.md") if re.fullmatch(s.pattern, p.stem)} if lay.source("S") == "new" else lay.old_rows("S")
    return {"tasks": s_reverse(lambda r: repo.read(root, r), "R"), "done": done, "heads": spec_heads(root), "table": table, "S": set(known)}


def r_column(cells):
    return cells[1] if len(cells) == 3 and cells[2] == "反映" and R_DECISION.fullmatch(cells[1]) else None


def r_items(u):
    """`- 判断（<word>、<date of the header>）: <決定>` and `- 反映: <反映>` a row."""
    out = []
    for r in u.rows:
        words = ([R_WORDS[r.id_cell]] if r.id_cell != u.id else []) + [d for d in R_DECISION.fullmatch(r.column).groups() if d]
        out += [("判断" + (f"（{'、'.join(words)}）" if words else ""), unbar(r.cells[0])), ("反映", unbar(r.cells[1]))]
    return out


def r_unrow(id_, values, extra):
    """The rows of §8 from the pairs `判断`, `反映` (a pair it cannot read gives a piece no row is)."""
    cells = {(re.match(repo.KIND["R"].pattern, c).group(0), w): c for c, w in R_WORDS.items()}
    out = []
    for i in range(0, len(extra), 2):
        pair = extra[i : i + 2]
        m = R_JUDGED.fullmatch(pair[0][0])
        words = m.group(1).split("、") if m and m.group(1) is not None else []
        day = words.pop() if words and re.fullmatch(DATE, words[-1]) else None
        cell = cells.get((id_, "、".join(words))) if words else id_
        if m is None or cell is None or [label for label, _ in pair[1:]] != ["反映"]:
            out.append(f"not a pair of a row: {pair}")
        else:
            out.append(f"決定{f'（{day}）' if day else ''}\t| {cell} | {pair[0][1]} | {pair[1][1]} |")
    return out


def r_parts(u):
    """The parts of the first item of the text (cut at `｜`), or None."""
    first = u.cells[BODY].split("\n", 1)[0]
    return first[2:].split(PART) if first.startswith("- ") else None


def r_severity(u, ctx, values):
    """The head of the first part, up to its first `・`; a value of the README, else listed."""
    parts = r_parts(u)
    v = parts[0].split("・")[0] if parts else None
    if v is not None and ctx["table"].check_value("severity", v) is None:
        return v, []
    return None, [Item(u.id, "severity", ("severity",), None, parts[0] if parts else "no first item")]


def r_aspect(u, ctx, values):
    """`観点 n` or `観点 n / m` after the last `・` of the first part, as integers (another form: listed)."""
    parts = r_parts(u)
    if parts is None:
        return None, []
    m = R_ASPECT.fullmatch(parts[0].split("・")[-1])
    v = [int(n) for n in m.group(1).split(" / ")] if m else None
    if v and ctx["table"].check_value("aspect", v) is None:
        return v, []
    return None, [Item(u.id, "aspect", ("aspect",), None, parts[0])]


def r_spec(u, ctx, values):
    """The sections of the third part, as S's `spec` (no third part: not written)."""
    parts = r_parts(u) or []
    return spec_of(u, parts[2:3], ctx) if len(parts) > 2 else (None, [])


def r_decisions(u, ctx, values):
    """The S of the third part; an S there is not (`impl-review` S-1) is left out and listed."""
    parts = r_parts(u) or []
    found = list(dict.fromkeys(ids_of(parts[2], ("S",)))) if len(parts) > 2 else []
    good = [s for s in found if s in ctx["S"]] or None
    return good, [] if len(good or []) == len(found) else [Item(u.id, "decisions", ("decisions",), good, parts[2])]


def r_fix(u, ctx, values):
    """The W of the cells `反映` of its rows, once each, in the order they come."""
    return list(dict.fromkeys(w for r in u.rows for w in ids_of(r.cells[1], ("W",)))) or None, []


def r_status(u, ctx, values):
    """DONE when every W of `fix` has ✅ in the rework §3, else OPEN; no `fix`, or a T in a cell `反映`
    with every W done: listed, no value."""
    cells = " / ".join(r.cells[1] for r in u.rows) or "no row of §8"
    fix = values.get("fix") or []
    if not fix:
        return None, [Item(u.id, "status-no-fix", ("status",), None, cells)]
    if not all(ctx["done"].get(w) for w in fix):
        return "OPEN", []
    if any(ids_of(r.cells[1], ("T",)) for r in u.rows):
        return None, [Item(u.id, "status-t", ("status",), None, cells)]
    return "DONE", []


def r_rework(u, ctx, values):
    """Only reported: the W whose `実現する決定` names the R and not in its `fix`, and the other way."""
    named, fix = ctx["tasks"].get(u.id, []), values.get("fix") or []
    found = [(cls, [w for w in a if w not in b]) for cls, a, b in (("rework-not-fix", named, fix), ("fix-not-rework", fix, named))]
    return [Item(u.id, cls, (), None, ", ".join(ws)) for cls, ws in found if ws]


def r_fix_reverse(read):
    """{R: `fix`} of the rows of §8 of the tree before."""
    units = read_headings(None, R_RULE, read(R_RULE.source[0]))[0]
    return {u.id: fix for u in units if (fix := r_fix(u, None, {})[0])}


R_ROWS = Rows("## 8.", None, r_column, r_items, r_unrow, many=True, alone=True, words=R_WORDS)
R_RULE = Rule(
    kind="R",
    columns=(),
    labels={},
    extra=("判断", "反映"),
    done=None,
    context=r_context,
    fields=(("severity", r_severity), ("aspect", r_aspect), ("spec", r_spec), ("decisions", r_decisions),
            ("fix", r_fix), ("status", r_status)),  # fmt: skip
    title=heading_title(R_ROWS),
    notes=(r_rework,),
    reverse=("fix", r_fix_reverse, "§8"),
    source=(repo.DOC_REVIEW, "## 1.", "## 8.", "R findings"),  # the headings `#### R-NN` of §1, §2, §3 and §5
    heading="####",
    gap=0,
    rows=R_ROWS,
    tail=(r"判断(?:（[^）]*）)?", "反映"),
)

# ---------------------------------------------------------------- the rules of W (MG-4 (5b))

W_COLUMNS = ("ID", "作業", "内容", "実現する決定", "依存", "規模", "役割・印")
# the spellings of the column `役割・印` -> the values of `marks` (DF-6: the brackets taken off); the
# values are checked by the README's field table
W_MARKS = {"〔危険〕": "危険", "〔メモ〕": "メモ", "基盤": "基盤", "テスト": "テスト"}
W_MARK = re.compile("|".join(map(re.escape, W_MARKS)))
W_RANGE = re.compile(r"(W\d+-)(\d+)〜\1(\d+)")  # a range of a stage in `依存`
NO_DEPENDS = "—"


def w_cell(u, column):
    return u.cells[W_COLUMNS.index(column) - 1]


def w_context(root):
    table = docs.field_table(docs.Tree(root, []), repo.KIND["W"])
    if not isinstance(table, docs.FieldTable):
        raise repo.RepoError(f"the values of `size` and `marks` are the README's: {table}")
    return {"table": table}


def w_open(cell, ids):
    """The W and the stages of a cell `依存` (cut at `、`; a stage `W3` as it is, its works all of it,
    DF-6), a range opened to the IDs `ids` between its ends in their order, once each; None when a part
    is not a W, a stage of a work of `ids`, or a range of two of `ids`."""
    out = []
    for part in cell.split("、"):
        m = W_RANGE.fullmatch(part)
        if m and {m[1] + m[2], m[1] + m[3]} <= set(ids) and int(m[2]) < int(m[3]):
            out += [i for i in ids if i.startswith(m[1]) and int(m[2]) <= int(i[len(m[1]) :]) <= int(m[3])]
        elif re.fullmatch(repo.KIND["W"].pattern, part) or (docs.STAGE.fullmatch(part) and docs._in_stage(ids, part)):
            out.append(part)
        else:
            return None
    return list(dict.fromkeys(out))


def w_status(u, ctx, values):
    return ("DONE" if u.done else "PLAN"), []


def w_size(u, ctx, values):
    v = w_cell(u, "規模")
    return (v, []) if ctx["table"].check_value("size", v) is None else (None, [Item(u.id, "size", ("size",), None, v)])


def w_depends(u, ctx, values):
    """`依存` as `w_open` reads it (`—`: not written; another form: listed)."""
    cell = w_cell(u, "依存")
    v = None if cell == NO_DEPENDS else w_open(cell, ctx["ids"])
    return v, [] if v or cell == NO_DEPENDS else [Item(u.id, "depends", ("depends",), None, cell)]


def w_marks(u, ctx, values):
    """`役割・印` as spellings of W_MARKS one after another, in their order (empty: not written; another
    form, `基盤（U3）`: listed)."""
    cell = w_cell(u, "役割・印")
    found = W_MARK.findall(cell)
    v = [W_MARKS[x] for x in found] or None
    if "".join(found) == cell and (v is None or ctx["table"].check_value("marks", v) is None):
        return v, []
    return None, [Item(u.id, "marks", ("marks",), None, cell)]


W_SPELLING = {v: k for k, v in W_MARKS.items()}
W_RULE = Rule(
    kind="W",
    columns=W_COLUMNS,
    labels={"内容": "内容", "実現する決定": "実現する決定"},  # MG-G
    extra=(),
    done="DONE",
    context=w_context,
    fields=(("status", w_status), ("size", w_size), ("depends", w_depends), ("marks", w_marks)),
    title=lambda u, ctx: (unbar(w_cell(u, "作業")) or None, {}, []),
    notes=(),
    head={"依存": ("depends", lambda c, ctx: "、".join(w_open(c, ctx["ids"]) or [c]), lambda v: "、".join(v) if v else NO_DEPENDS),
          "規模": ("size", lambda c, ctx: c, lambda v: v or ""),
          "役割・印": ("marks", lambda c, ctx: c, lambda v: "".join(W_SPELLING.get(x, x) for x in v or ()))},  # fmt: skip
    titled="作業",
)
RULES = {"S": S_RULE, "D": D_RULE, "K": K_RULE, "Q": Q_RULE, "A": A_RULE, "R": R_RULE, "W": W_RULE}
COMMANDS = {"plan": cmd_plan, "apply": cmd_apply, "verify": cmd_verify}


def main(argv=None):
    ap = argparse.ArgumentParser(prog="migrate_tables.py", description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in COMMANDS:
        p = sub.add_parser(name)
        p.add_argument("--kind", required=True, choices=sorted(RULES))
        p.add_argument("--root", type=Path, default=ROOT)
        if name == "verify":
            p.add_argument("--before", required=True, help="the tree before: a directory, or a git revision of the root")
        else:
            p.add_argument("--overrides", type=Path)
    args = ap.parse_args(argv)
    try:
        return COMMANDS[args.cmd](args, RULES[args.kind])
    except Refused as e:
        print("\n".join(e.args[0]))
        print(f"migrate_tables.py {args.cmd}: refused; nothing is written")
        return 1
    except repo.RepoError as e:
        print(f"migrate_tables.py {args.cmd}: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
