#!/usr/bin/env python3
"""Move a table of IDs into one file per ID (X-2 step 6, MG-2). The rules of a kind are one value of
`Rule` in RULES; the frame (`plan`, `apply`, the overrides) reads only them.

    python3 -B migrate_tables.py plan  --kind S [--root DIR] [--overrides TOML]
    python3 -B migrate_tables.py apply --kind S [--root DIR] [--overrides TOML]
    python3 -B migrate_tables.py verify --kind S [--root DIR] --before DIR|REV

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
  delimiter rows rebuilt from the columns; the IDs of the rows and of the files; `reverse` (`tasks`)
  against the rework before. Exit 1 on any difference.
- The overrides, `[S-276]` / `status = "DECIDED"`: only the (ID, key) the list of the same tree
  accepts (an item's keys for its ID and its partners), the value fitting the field table of the
  README or one of the item's choices; "" or [] is "not written". Anything else refuses them all.
- Order: each document is read once, a line at a time; each rule is linear in its row. The rules run
  twice (without and with the overrides). No loop waits on a fixed point, so it stops.
"""
import argparse
import re
import subprocess
import sys
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass
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
    cells: tuple  # the cells after the ID cell, as the table has them
    lines: tuple  # (line number, text) of its rows

    @property
    def text(self):
        return "\n".join(t for _, t in self.lines)


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
    extra: tuple  # the labels of the body that come from no column
    done: str  # the `status` of a row with ✅
    context: object  # fn(root) -> dict, the other documents read once
    fields: tuple  # (key, fn(unit, ctx, values) -> (value, items)); `values` holds the keys before
    title: object  # fn(unit, ctx) -> (title, {label: text}, items)
    notes: tuple  # fn(unit, ctx, values) -> items: judgements with no value to write
    reverse: tuple = None  # (head field, fn(read) -> {ID: values}) from another document (`verify`)
    count_only: tuple = ()  # the classes printed only as a number


@dataclass(frozen=True)
class Result:
    unit: Unit
    values: dict
    title: str
    extra: dict


# ---------------------------------------------------------------- the frame


def read_table(root, rule, text=None):
    """(units, (first, last) line of the table, the lines of its document); `text`: the document's."""
    kind = repo.KIND[rule.kind]
    doc, start, end, what = kind.old
    lines = (repo.read_exact(root, doc) if text is None else text).split("\n")
    lo = next((i for i, line in enumerate(lines) if line.startswith(start)), None)
    if lo is None:
        raise repo.RepoError(f"{doc}: the section `{start}` is not found")
    hi = next((i for i in range(lo + 1, len(lines)) if lines[i].startswith(end)), len(lines))
    row = repo.row_re(kind.pattern)
    at = [i for i in range(lo, hi) if row.match(lines[i])]
    if not at:
        raise Refused([f"{doc} `{start}`: no row of the {what}"])
    a = at[0] - 2
    if a < lo or docs.table_cells(lines[a]) != list(rule.columns) or not docs.DELIMITER.fullmatch(lines[a + 1].strip()):
        raise repo.RepoError(f"{doc}:{a + 1}: no header `| {' | '.join(rule.columns)} |` and delimiter row")
    units, seen = [], set()
    for i in range(at[0], at[-1] + 1):
        m, cells = row.match(lines[i]), docs.table_cells(lines[i])
        if m is None or len(cells) != len(rule.columns) or cells[0] != m.group(1) + (m.group(2) or ""):
            raise repo.RepoError(f"{doc}:{i + 1}: not a row `| <ID>[ ✅] | … |` of {len(rule.columns)} cells")
        if m.group(1) in seen:
            raise repo.RepoError(f"{doc}:{i + 1}: {m.group(1)} is given twice")
        seen.add(m.group(1))
        units.append(Unit(m.group(1), bool(m.group(2)), tuple(cells[1:]), ((i + 1, lines[i]),)))
    return units, (a + 1, at[-1] + 1), lines


def read_overrides(path):
    """{(ID, key): value or None}, and why the file is not of `[ID]` tables."""
    if path is None:
        return {}, []
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
        raise repo.RepoError(f"{path}: {e}") from e
    out, why = {}, []
    for id_, keys in data.items():
        if not isinstance(keys, dict):
            why.append(f"{id_}: not a table `[{id_}]`")
            continue
        for key, v in keys.items():
            out[(id_, key)] = None if v == "" or v == [] else v
    return out, why


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
    """(units, span, lines, results, items) with the overrides checked against the list of the tree."""
    units, span, lines = read_table(root, rule)
    ctx = rule.context(root)
    overrides, why = read_overrides(overrides_path)
    items = run(rule, units, ctx, {})[1]
    why += check_overrides(overrides, items, table)
    if why:
        raise Refused(why)
    results = run(rule, units, ctx, overrides)[0]
    filled = {(i, k) for i, k in overrides}
    left = [it for it in items if not any((i, k) in filled for i in (it.id, *it.partners) for k in it.keys)]
    return units, span, lines, results, left


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
    units, span, _, results, items = evaluate(args.root, rule, args.overrides, table)
    print(f"{kind.old[0]}:{span[0]}-{span[1]}: {len(units)} rows -> {len(units)} files in {kind.dir}/")
    counts = Counter()
    for r in results:
        counts.update(k for k, v in r.values.items() if v is not None)
        counts.update(["title"] * bool(r.title) + list(r.extra))
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
    doc = kind.old[0]
    tree = docs.Tree(root, [])
    table, why = docs.field_table(tree, kind), []
    if not isinstance(table, docs.FieldTable):
        why.append(str(table))
    labels = readme_labels(tree, kind)
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
    units, span, lines, results, _ = evaluate(root, rule, args.overrides, table)
    texts = {Path(kind.dir) / f"{r.unit.id}.md": render(rule, kind, table, r) for r in results}
    old, written = "\n".join(lines), []
    try:
        docs.write_atomic(root / doc, "\n".join(lines[: span[0] - 1] + lines[span[1] :]))
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
    print(f"wrote {len(texts)} files in {kind.dir}/; took out {doc}:{span[0]}-{span[1]} ({span[1] - span[0] + 1} lines)")
    if refs:
        print(f"== body-ref ({len(refs)})")
        print("\n".join(map(str, refs)))
    return 0


# The closed list of what `verify` reads as the same (MG-2); any other difference fails.
NORMALIZED = (
    "the order of the rows (compared as multisets)",
    "`\\|` read as `|` on both sides",
    "a line going on with two spaces (`docs.fmt_text`) joined to the line before",
)


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


def read_back(rule, rel, text):
    """(head values, title, cells, {extra label: text}) of a written file, or why it is not of the form
    `render` writes (the head fields, `# <ID>[ <title>]`, a blank line, the items of the labels in order,
    the extra items, a line end at the end)."""
    head = docs.read_head(text)
    if head.values is None:
        return f"{rel}:{head.error_line}: {head.error}"
    if not text.endswith("\n"):
        return f"{rel}: does not end with a line end"
    lines = []
    for line in head.body.split("\n")[:-1]:
        if line.startswith("  ") and len(lines) > 2:
            lines[-1] += line[2:]
        else:
            lines.append(line)
    m = re.fullmatch(rf"# {re.escape(rel.stem)}(?: (.*))?", lines[0]) if lines else None
    if m is None or lines[1:2] != [""]:
        return f"{rel}: not `# {rel.stem}[ <title>]` and a blank line after the head fields"
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
    return head.values, m.group(1), cells, extra


def cmd_verify(args, rule):
    root, kind = Path(args.root), repo.KIND[rule.kind]
    doc, read = kind.old[0], before_reader(args.root, args.before)
    units, span, old = read_table(root, rule, read(doc))
    ctx, by = rule.context(root), {u.id: u for u in units}
    allowed = {it.id for it in run(rule, units, ctx, {})[1] if it.cls == "status"}
    key, reverse_of = rule.reverse
    reverse = reverse_of(read)
    print("normalized: " + "; ".join(NORMALIZED) + ". ✅ is compared with `status` on its own")
    files = {p.stem: p.relative_to(root) for p in sorted((root / kind.dir).glob("*.md")) if re.fullmatch(kind.pattern, p.stem)}
    bad, swapped, want, got = [], [], Counter(), Counter()
    if set(files) != set(by):
        bad.append(f"IDs: {len(by)} rows, {len(files)} files; no file: {sorted(set(by) - set(files))[:10]}, "
                   f"no row: {sorted(set(files) - set(by))[:10]}")  # fmt: skip
    for u in units:
        (_, line), m = u.lines[0], repo.row_re(kind.pattern).match(u.lines[0][1])
        want[(line[: m.start(2)] + line[m.end(2) :] if m.group(2) else line).replace("\\|", "|")] += 1
    for id_, rel in files.items():
        back = read_back(rule, rel, repo.read_exact(root, rel))
        if isinstance(back, str):
            bad.append(back)
            continue
        values, title, cells, extra = back
        got[("| " + " | ".join([id_, *cells]) + " |").replace("\\|", "|")] += 1
        if (u := by.get(id_)) is None:
            continue
        if (values.get("status") == rule.done) != u.done:
            line = f"{id_}: {'✅' if u.done else 'no ✅'} -> {values.get('status')}"
            (swapped if id_ in allowed else bad).append(line + ("" if id_ in allowed else " (not a `status` item)"))
        rule_title, rule_extra, items = rule.title(u, ctx)
        if title not in {None, rule_title, *(c for it in items for c in it.choices or ())}:
            bad.append(f"{rel}: the title {title!r} is not one of the drafts'")
        if extra != {k: v for k, v in rule_extra.items() if v}:
            bad.append(f"{rel}: the extra items {extra} are not the rule's {rule_extra}")
        if values.get(key) != (reverse.get(id_) or None):
            bad.append(f"{rel}: `{key}` is {values.get(key)}, the rework has {reverse.get(id_)}")
    bad += [f"lost: {row[:120]}" for row in (want - got).elements()] + [f"new: {row[:120]}" for row in (got - want).elements()]
    new = repo.read_exact(root, doc).split("\n")
    if new != old[: span[0] - 1] + old[span[1] :]:
        at = next((i for i, (a, b) in enumerate(zip(new, old[: span[0] - 1] + old[span[1] :])) if a != b), min(len(new), len(old)))
        bad.append(f"{doc}:{at + 1}: outside the table, the document is not what it was")
    if old[span[0] - 1 : span[0] + 1] != ["| " + " | ".join(rule.columns) + " |", "|" + "---|" * len(rule.columns)]:
        bad.append(f"{doc}:{span[0]}: the header and delimiter rows are not rebuilt from the columns")
    with_key = {i for i, rel in files.items() if i in by}
    if set(reverse) - with_key:
        bad.append(f"{key}: the rework names {sorted(set(reverse) - with_key)[:10]}, which have no file")
    print(f"round trip: {sum(want.values())} rows, {sum(got.values())} files read back; IDs {len(files)}; "
          f"`{key}` of {len(reverse)} {rule.kind} from the rework; ✅ and status apart (the list's): {len(swapped)}")  # fmt: skip
    for line in swapped + bad:
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


def s_reverse(read):
    """{S: [W…]} from the column `実現する決定` of the rework §3, in the order of the table; `read(rel)`
    gives a document (of the tree, or of the tree before for `verify`)."""
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
            for s in ids_of(cells[col], ("S",)):
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
    heads = {"spec": repo.spec_doc(root).text, "tools": repo.tools_doc(root).text}
    heads = {k: set(spec_blocks.headings(v)) for k, v in heads.items()}
    return {"tasks": tasks, "changes": changes, "titles": titles, "groups": groups, "heads": heads}


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
    sources = ctx["changes"].get(u.id) or [u.cells[ITEM]]
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
    reverse=("tasks", s_reverse),
    count_only=("nodest-open",),
)
RULES = {"S": S_RULE}
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
