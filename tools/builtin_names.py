#!/usr/bin/env python3
"""Builtin names written as strings in the compiler's Rust code (Q-14, plan §8.2 5).

A decision about a builtin belongs in one place (plan §3.6); comparing a
builtin name with a string elsewhere decides it again. This check finds the
string literals of the Rust code that are builtin names, and compares their
number per file and name with the list `tools/builtin_names.toml`:

- a literal the list does not allow (a new hard-coded name) fails;
- a list entry larger than what is found fails too, so that the list only
  shrinks (C-118: the first list is every literal of today; W5-02 reduces it).
The list has two tables (`TABLES`): `allow`, the builtin names written in the
code, and `same_spelling`, literals spelled like a builtin name with another
meaning, each with a note of its meaning; they are counted together.

The builtin names are the names the spec defines and the compiler tells by
name. They come from three sources:
- the names the embedded std declares (from the compiler, `onsa_cases
  --std-names`);
- the builtin methods, associated constants and associated functions of
  sema's one table of them (`onsa_cases --builtin-members`, until W5-02 moves
  them into std);
- fixed places of the spec (`SPEC_PLACES`): the builtin types (§4.1), the
  prelude (§15.1), the operator and standard traits (§6.3), the standard
  effects (§8.1), the builtin names reserved in a flow (§2.2), the generated
  API of a flow (§11.6, and the sizes of §12.4), the attributes (§6.5), the
  clocks (§11.3), and the rate types of the 0.3 draft that E0020 detects
  (§11.3; the implementation still uses them until W3 / W7).
The keywords (§2.2) and one-letter names are not names. The keys and values
of the manifest are not here (W4-02 makes their closed table).

What counts as a use of a name, in the code outside tests:
- a string literal whose whole text is a builtin name (`"zeroed"`, in `==`,
  a `match` arm, `matches!`, a table, a lookup);
- a string argument of `starts_with`, `strip_prefix`, `trim_start_matches`
  (a prefix of a name), `ends_with`, `strip_suffix`, `trim_end_matches` (a
  suffix), `contains` (a part), also inside an array argument (`"narrow_"`);
- a format string of one placeholder joined by `_` to a fixed part that makes
  a builtin name (`"narrow_{}"`).
Escapes (`\\u{..}`) and names joined by `format!` or `concat!` are not followed.
Not counted: comments, the test code (`tests/`, `*_tests.rs`, `tests.rs`, items
under `#[cfg(test)]`), and the registry places of plan §3.6 (`REGISTRY`).

    tools/builtin_names.py [--root DIR]    check against the list
    tools/builtin_names.py --print         print what is found, in the form of the list

Exit 0 when the code matches the list, 1 otherwise, 2 on a usage error.
"""
import argparse
import re
import sys
import tomllib
from collections import Counter
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
SPEC = repo.SPEC
ALLOW = Path("tools") / "builtin_names.toml"
CRATES = "crates"
# The places of plan §3.6 that hold the builtins' table and may name them.
REGISTRY = ("crates/onsa_diag/",)
# Calls whose string argument is a part of a name: (method, how the part is matched).
AFFIX_METHODS = {
    "starts_with": "prefix",
    "strip_prefix": "prefix",
    "trim_start_matches": "prefix",
    "ends_with": "suffix",
    "strip_suffix": "suffix",
    "trim_end_matches": "suffix",
    "contains": "infix",
}

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
CODE_SPAN = re.compile(r"`([^`]+)`")

CheckError = repo.RepoError


# ---------------------------------------------------------------- the names


def _lines(spec_text, section):
    lines = spec_blocks.section_lines(spec_text, section)
    if lines is None:
        raise CheckError(f"{SPEC}: the section §{section} is not found")
    return lines


def _fences(spec_text, section):
    fences = spec_blocks.section_fences(spec_text, section)
    if not fences:
        raise CheckError(f"{SPEC} §{section}: no fenced block found")
    return fences


def span_names(text):
    return {n for span in CODE_SPAN.findall(text) for n in IDENT.findall(span)}


def first_sentence(text):
    return text.split("。", 1)[0]


def only_line(spec_text, section, what, pred):
    found = [line for line in _lines(spec_text, section) if pred(line)]
    if len(found) != 1:
        raise CheckError(f"{SPEC} §{section}: expected one line of {what}, found {len(found)}")
    return found[0]


def table_column(spec_text, section, col):
    """The cells of column `col` of the (first) table of the section."""
    rows = [line for line in _lines(spec_text, section) if line.startswith("|")]
    if len(rows) < 3:
        raise CheckError(f"{SPEC} §{section}: no table found")
    cells = []
    for row in rows[2:]:  # the header and the separator
        parts = [c.strip() for c in row.strip().strip("|").split("|")]
        if len(parts) > col:
            cells.append(parts[col])
    return cells


def builtin_types(spec_text):
    """§4.1: the type column of the table (names of two or more characters)."""
    names = {n for cell in table_column(spec_text, "4.1", 1) for n in span_names(cell) if len(n) > 1 and n[0].isupper()}
    if not names:
        raise CheckError(f"{SPEC} §4.1: no builtin type found in the table")
    return names


def prelude(spec_text):
    """§15.1: the line of the prelude."""
    return span_names(only_line(spec_text, "15.1", "the prelude", lambda s: s.startswith("- 暗黙の prelude は")))


def traits(spec_text):
    """§6.3: the lines of the operator traits and the standard traits."""
    names = set()
    for head in ("- 演算子 trait:", "- 標準 trait:"):
        names |= span_names(only_line(spec_text, "6.3", f"`{head}`", lambda s, h=head: s.startswith(h)))
    return names


def std_effects(spec_text):
    """§8.1: the standard effects, "標準の効果（`Fs` `Stdout` ...）"."""
    line = only_line(spec_text, "8.1", "the standard effects", lambda s: "標準の効果（" in s)
    return span_names(line.split("標準の効果（", 1)[1].split("）", 1)[0])


def flow_builtins(spec_text):
    """§2.2: the builtin names reserved in a flow (the first sentence of their line)."""
    line = only_line(spec_text, "2.2", "the reserved builtin names", lambda s: "予約された組込み名" in s)
    return span_names(first_sentence(line))


def generated_api(spec_text):
    """§11.6: the items of a flow's namespace and the parameter names of its
    functions (the first fenced block, `voice.State`, `cfg:`), the fixed
    argument names; §12.4: the sizes of the state (`SIZE`, `BULK_SIZE`, ...)."""
    flows = {m for line in _lines(spec_text, "11.6") for m in re.findall(r"`flow (\w+)\(", line)}
    if len(flows) != 1:
        raise CheckError(f"{SPEC} §11.6: expected one example `flow <name>(...)`, found {len(flows)}")
    ns = flows.pop()
    code = "\n".join(re.sub(r"//.*", "", line) for line in _fences(spec_text, "11.6")[0][1].split("\n"))
    names = set(re.findall(rf"\b{re.escape(ns)}\.(\w+)", code)) | set(re.findall(r"(\w+)\s*:\s", code))
    args = only_line(spec_text, "11.6", "the fixed argument names", lambda s: "引数の名前は" in s)
    names |= span_names(first_sentence(args.split("引数の名前は", 1)[1]))
    size = only_line(spec_text, "12.4", "the sizes of the state", lambda s: s.startswith("- 容量の確認:"))
    names |= span_names(first_sentence(size))
    return names


def attributes(spec_text):
    """§6.5: the attributes the first sentence of the section lists (`@repr(c)`, ...)."""
    text = next((line for line in _lines(spec_text, "6.5") if line.strip()), "")
    names = set(re.findall(r"`@(\w+)", first_sentence(text)))
    if not names:
        raise CheckError(f"{SPEC} §6.5: no attribute found in the first sentence")
    return names


def clocks(spec_text):
    """§11.3: the clocks of the table (`init`, `block`, `sample`)."""
    names = {c.strip("`") for c in table_column(spec_text, "11.3", 0) if re.fullmatch(r"`\w+`", c)}
    if not names:
        raise CheckError(f"{SPEC} §11.3: no clock found in the table")
    return names


def old_rate_types(spec_text):
    """§11.3: the rate types of the 0.3 draft that E0020 detects (`Sig`, `Ctl`, `Init`)."""
    line = only_line(spec_text, "11.3", "the old rate types", lambda s: "0.3 の草案の形" in s)
    return {s for s in CODE_SPAN.findall(line) if re.fullmatch(r"[A-Z][A-Za-z0-9]*", s)}


# The kinds of builtin names the spec gives, each read from fixed places.
SPEC_PLACES = {
    "builtin types (§4.1)": builtin_types,
    "prelude (§15.1)": prelude,
    "traits (§6.3)": traits,
    "standard effects (§8.1)": std_effects,
    "flow builtins (§2.2)": flow_builtins,
    "generated API (§11.6, §12.4)": generated_api,
    "attributes (§6.5)": attributes,
    "clocks (§11.3)": clocks,
    "old rate types (§11.3)": old_rate_types,
}


# Names each place must give (a baseline): a change of the spec that drops one
# (a removed attribute, a renamed clock) fails here instead of shrinking the
# set silently. Update a baseline together with the spec.
BASELINES = {
    "builtin types (§4.1)": {"I32", "U32", "F32", "F64", "Bool", "Str", "Buf", "Span", "Option", "Result"},
    "prelude (§15.1)": {"Option", "Result", "Some", "None", "Ok", "Err", "panic", "Alloc", "Copy", "Dup"},
    "traits (§6.3)": {"Add", "Neg", "Not", "PartialEq", "PartialOrd", "Eq", "Ord", "Hash", "Show", "Default", "Num", "Float"},
    "standard effects (§8.1)": {"Fs", "Stdout", "Random", "Log"},
    "flow builtins (§2.2)": {"prev", "delay", "vdelay", "sample_rate"},
    "generated API (§11.6, §12.4)": {
        "State", "Config", "Params", "Out", "init", "reset", "process", "process_inplace", "render",
        "params_default", "SIZE", "BULK_SIZE",
    },
    "attributes (§6.5)": {"repr", "fp", "param", "mem"},
    "clocks (§11.3)": {"init", "block", "sample"},
    "old rate types (§11.3)": {"Sig", "Ctl", "Init"},
}  # fmt: skip


def keywords(spec_text):
    """§2.2: the words of the keyword block."""
    words = set(IDENT.findall(_fences(spec_text, "2.2")[0][1]))
    if not words:
        raise CheckError(f"{SPEC} §2.2: the keyword block is empty")
    return words


def names_by_kind(spec_text, std_names, members=(), baselines=None):
    """{kind: names} of every source of builtin names, before keywords and
    one-letter names are removed. Fails when a place does not give the names
    of its baseline (`BASELINES` by default)."""
    baselines = BASELINES if baselines is None else baselines
    kinds = {kind: place(spec_text) for kind, place in SPEC_PLACES.items()}
    for kind, base in baselines.items():
        missing = sorted(set(base) - kinds[kind])
        if missing:
            raise CheckError(
                f"{SPEC}: {kind} no longer gives {', '.join(missing)}; if the spec changed them, "
                "change BASELINES in tools/builtin_names.py with it"
            )
    kinds["std declarations"] = set(std_names)
    kinds["builtin members of sema"] = set(members)
    return kinds


def builtin_names(spec_text, std_names, members=(), baselines=None):
    """The builtin names, without keywords and one-letter names."""
    every = set().union(*names_by_kind(spec_text, std_names, members, baselines).values())
    return {n for n in every if len(n) > 1} - keywords(spec_text)


# ---------------------------------------------------------------- the Rust code


RAW_START = re.compile(r'(?:b|c)?r(#*)"')


def scan_rust(src):
    """(literals, masked): the string literals of Rust source as (offset of the
    opening quote, line, text without its quotes), and the source with every
    comment and literal blanked out (newlines kept), for finding the code
    structure. Char literals and lifetimes are told apart."""
    out = []
    masked = list(src)
    n = len(src)
    i = 0
    line = 1

    def blank(a, b):
        for k in range(a, b):
            if masked[k] != "\n":
                masked[k] = " "

    def ident_before(k):
        return k > 0 and (src[k - 1].isalnum() or src[k - 1] == "_")

    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
        elif src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/*", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            line += src.count("\n", i, j)
            i = j
        elif (m := RAW_START.match(src, i)) and not ident_before(i):
            close = '"' + m.group(1)
            j = src.find(close, m.end())
            j = n if j < 0 else j
            out.append((m.end() - 1, line, src[m.end() : j]))
            blank(i, min(n, j + len(close)))
            line += src.count("\n", i, j)
            i = j + len(close)
        elif c == '"' or (src.startswith(('b"', 'c"'), i) and not ident_before(i)):
            start = i + 1 if c == '"' else i + 2
            j = start
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append((start - 1, line, src[start:j]))
            blank(i, min(n, j + 1))
            line += src.count("\n", i, j)
            i = j + 1
        elif c == "'":
            m = re.compile(r"'(?:\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^\\'\n])'").match(src, i)
            if m:
                blank(i, m.end())
                i = m.end()
            else:
                i += 1  # a lifetime
        else:
            i += 1
    return out, "".join(masked)


CFG_TEST = re.compile(r"#\[cfg\(test\)\]")


def test_ranges(masked):
    """The (start, end) offsets of the items under `#[cfg(test)]`."""
    ranges = []
    for m in CFG_TEST.finditer(masked):
        brace, semi = masked.find("{", m.end()), masked.find(";", m.end())
        if brace < 0 or (0 <= semi < brace):
            ranges.append((m.start(), semi + 1 if semi >= 0 else len(masked)))
            continue
        depth, k = 0, brace
        while k < len(masked):
            if masked[k] == "{":
                depth += 1
            elif masked[k] == "}":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        ranges.append((m.start(), k + 1))
    return ranges


def is_test_file(rel):
    parts = rel.split("/")
    return "tests" in parts[:-1] or parts[-1] == "tests.rs" or parts[-1].endswith("_tests.rs")


def _format_pattern(text):
    """The regex of a format string that makes a name of a family, or None: one
    placeholder joined to a fixed part by `_` (`"narrow_{}"`, `"{}_sat"`)."""
    m = re.fullmatch(r"([A-Za-z0-9_]*)\{[A-Za-z0-9_]*(?::[^{}]*)?\}([A-Za-z0-9_]*)", text)
    if not m or not (m.group(1).endswith("_") and len(m.group(1)) > 1 or m.group(2).startswith("_") and len(m.group(2)) > 1):
        return None
    return re.compile(re.escape(m.group(1)) + r"[A-Za-z0-9_]+" + re.escape(m.group(2)))


# `.starts_with(`, `.contains(&`, `.ends_with([` and the earlier literals of the
# array (blanked in the masked source): the call a string argument is given to.
AFFIX_CALL = re.compile(r"\.(\w+)\(\s*&?\s*(?:\[[\s,]*)?$")


def affix_call(before):
    """How the literal after `before` is matched (`AFFIX_METHODS`), or None."""
    m = AFFIX_CALL.search(before)
    return AFFIX_METHODS.get(m.group(1)) if m else None


def part_of(text, name, how):
    if text == name:
        return False
    if how == "prefix":
        return name.startswith(text)
    if how == "suffix":
        return name.endswith(text)
    return text in name


def uses_in(src, names):
    """Counter of the literals (their text) that use a builtin name, outside test items."""
    literals, masked = scan_rust(src)
    tests = test_ranges(masked)
    found = Counter()
    for off, _line, text in literals:
        if any(a <= off < b for a, b in tests):
            continue
        if text in names:
            found[text] += 1
            continue
        how = affix_call(masked[max(0, off - 160) : off])
        if how and len(text) > 1 and IDENT.fullmatch(text) and any(part_of(text, n, how) for n in names):
            found[text] += 1
            continue
        pat = _format_pattern(text)
        if pat and any(pat.fullmatch(n) for n in names):
            found[text] += 1
    return found


def scan(root, names):
    """{file: Counter(literal)} of the Rust code under `crates/`."""
    out = {}
    for p in sorted((root / CRATES).rglob("*.rs")):
        rel = p.relative_to(root).as_posix()
        if repo.is_build_output(root, rel) or is_test_file(rel) or rel.startswith(REGISTRY):
            continue
        found = uses_in(p.read_text(encoding="utf-8"), names)
        if found:
            out[rel] = found
    return out


# ---------------------------------------------------------------- the list


# The two tables of the list. `allow`: builtin names written in the code (the
# hard-coding W5-02 removes), `{file: {literal: count}}`. `same_spelling`: a
# literal spelled like a builtin name with another meaning (an `@param` key,
# a clock name, a C type name), `{file: {literal: {count, note}}}`; the note
# says the meaning. Both work the same: more literals than listed fail, fewer
# ask to lower the count.
TABLES = ("allow", "same_spelling")


def load_allow(path):
    """{table: {file: {literal: count}}} and the notes {(file, literal): note}
    of the `same_spelling` table. Raises CheckError when malformed."""
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as e:
        raise CheckError(f"{path}: {e}") from e
    extra = set(data) - set(TABLES)
    if extra:
        raise CheckError(f"{path}: only the tables {', '.join(TABLES)} are allowed (found {', '.join(sorted(extra))})")
    lists, notes = {t: {} for t in TABLES}, {}
    for f, names in data.get("allow", {}).items():
        if not isinstance(names, dict) or not all(isinstance(v, int) and v > 0 for v in names.values()):
            raise CheckError(f'{path}: [allow."{f}"] must map literals to positive counts')
        lists["allow"][f] = dict(names)
    for f, names in data.get("same_spelling", {}).items():
        ok = isinstance(names, dict) and all(
            isinstance(v, dict)
            and set(v) == {"count", "note"}
            and isinstance(v["count"], int)
            and v["count"] > 0
            and isinstance(v["note"], str)
            and v["note"].strip()
            for v in names.values()
        )
        if not ok:
            raise CheckError(f'{path}: [same_spelling."{f}"] must map literals to {{ count = <n>, note = "<meaning>" }}')
        lists["same_spelling"][f] = {t: v["count"] for t, v in names.items()}
        notes.update({(f, t): v["note"] for t, v in names.items()})
    return lists, notes


def compare(found, lists, root):
    problems = []
    files = set(found) | {f for t in TABLES for f in lists[t]}
    for f in sorted(files):
        if f not in found and not (root / f).is_file():
            problems.append(f"{ALLOW}: `{f}` is not a file; remove its tables")
            continue
        have = found.get(f, Counter())
        texts = set(have) | {x for t in TABLES for x in lists[t].get(f, {})}
        for text in sorted(texts):
            n = have.get(text, 0)
            m = sum(lists[t].get(f, {}).get(text, 0) for t in TABLES)
            if n > m:
                problems.append(
                    f'{f}: "{text}" is written {n} time(s), the list allows {m}; decide it in the place of '
                    "plan §3.6 instead of comparing the name here (or, if it only has the spelling of a builtin "
                    "name, list it in [same_spelling] with its meaning)"
                )
            elif n < m:
                problems.append(f'{f}: "{text}" is written {n} time(s), the list allows {m}; lower the count in {ALLOW}')
    return problems


def render(found, lists=None, notes=None):
    """The list for `found`: the `same_spelling` entries of `lists` are kept
    (up to what is found), the rest goes to `allow`."""
    same = (lists or {}).get("same_spelling", {})
    notes = notes or {}
    allow, kept = {}, {}
    for f, texts in found.items():
        for text, n in texts.items():
            s = min(n, same.get(f, {}).get(text, 0))
            if s:
                kept.setdefault(f, {})[text] = s
            if n - s:
                allow.setdefault(f, {})[text] = n - s
    lines = []
    for f in sorted(allow):
        lines.append(f'\n[allow."{f}"]')
        lines += [f"{spec_blocks.toml_string(t)} = {n}" for t, n in sorted(allow[f].items())]
    for f in sorted(kept):
        lines.append(f'\n[same_spelling."{f}"]')
        lines += [
            f"{spec_blocks.toml_string(t)} = {{ count = {n}, note = {spec_blocks.toml_string(notes[(f, t)])} }}"
            for t, n in sorted(kept[f].items())
        ]
    return "\n".join(lines).lstrip("\n") + "\n"


def main(argv=None, root=ROOT, cmd=repo.CASES_CMD):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=None)
    ap.add_argument("--print", action="store_true", help="print what is found, in the form of the list")
    args = ap.parse_args(argv)
    root = args.root or root
    try:
        std = repo.cases_json(root, cmd, "--std-names")
        members = repo.cases_json(root, cmd, "--builtin-members")
        names = builtin_names(repo.read(root, SPEC), std, members)
        found = scan(root, names)
        if args.print:
            lists, notes = load_allow(root / ALLOW) if (root / ALLOW).is_file() else (None, None)
            print(render(found, lists, notes), end="")
            return 0
        problems = compare(found, load_allow(root / ALLOW)[0], root)
    except (CheckError, OSError) as e:
        print(f"cannot check: {e}")
        return 1
    for p in problems:
        print(p)
    total = sum(sum(c.values()) for c in found.values())
    print(f"{len(names)} builtin names; {total} literal(s) in {len(found)} file(s) of {CRATES}/; " + (f"{len(problems)} problem(s)" if problems else "as the list allows"))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
