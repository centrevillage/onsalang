#!/usr/bin/env python3
"""The spec sections the test cases name (`[test] spec`, Q-05, plan D-16 1).

    spec_sections.py --check   fail when a case names a section the spec has no heading for, or
                               a string of the compiler (a diagnostic's message or note,
                               W3-02/b 8) names a section `§x.y` that is not a heading
    spec_sections.py --list    show the sections no case names (information; never fails on them)

The cases and their fragments come from the test runner's own reader (the
`onsa_cases` binary of `onsa_tests`), the headings from `spec_blocks.py`: each
rule is in one place. A section counts as tested when a case names it or one
of its subsections; a case with `mode = "none"` never runs and tests nothing
(`--check` still checks the sections it names).
"""
import argparse
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = repo.ROOT
SPEC = repo.SPEC


def load_cases(root=ROOT, cmd=repo.CASES_CMD):
    """The cases as `onsa_cases` lists them. Raises repo.RepoError when it fails."""
    return repo.cases_json(root, cmd, str(root))


def unknown(cases, headings):
    """(case path, section) for every named section the spec has no heading for."""
    known = set(headings)
    return [(c["path"], s) for c in cases for s in c["spec"] if s.removeprefix("§") not in known]


SECTION_REF = re.compile(r"§(\d+(?:\.\d+)*)")
# `#[cfg(test)]` and the `mod <name> {` it marks (a `mod <name>;` declaration is not cut).
TEST_MOD = re.compile(r"#\[cfg\(test\)\]\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*\{")
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


def rust_strings(text):
    """(line, content) of every string literal of Rust `text`, a string that
    goes on over lines (`\\` at the end of a line) included; raw strings too.
    Comments and char literals (`'"'`) are skipped. The line is where the
    string starts."""
    out, i, n, line = [], 0, len(text), 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            line += text.count("\n", i, j)
            i = j
        elif c == "'":
            m = CHAR_LITERAL.match(text, i)
            i = m.end() if m else i + 1  # else a lifetime
        elif c == "r" and re.match(r'r#*"', text[i:i + 8]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            hashes = len(re.match(r"r(#*)", text[i:]).group(1))
            start = i + 2 + hashes
            end = text.find('"' + "#" * hashes, start)
            end = n if end < 0 else end
            out.append((line, text[start:end]))
            line += text.count("\n", i, end)
            i = end + 1 + hashes
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append((line, text[i + 1:j]))
            line += text.count("\n", i, j)
            i = j + 1
        else:
            i += 1
    return out


def without_test_mods(text):
    """`text` with the bodies of its `#[cfg(test)] mod <name> { ... }` blanked
    (newlines kept, so lines stay): the unit tests are not messages."""
    out, pos = [], 0
    for m in TEST_MOD.finditer(text):
        if m.start() < pos:
            continue
        depth, j = 1, m.end()
        # Brace depth outside strings, chars and comments: the strings of the body are blanked first.
        body = text[m.end():]
        k = 0
        while k < len(body) and depth:
            if body.startswith("//", k):
                e = body.find("\n", k)
                k = len(body) if e < 0 else e
                continue
            ch = body[k]
            if ch == '"':
                e = k + 1
                while e < len(body) and body[e] != '"':
                    e += 2 if body[e] == "\\" else 1
                k = e + 1
                continue
            if ch == "'":
                cm = CHAR_LITERAL.match(body, k)
                k = cm.end() if cm else k + 1
                continue
            depth += {"{": 1, "}": -1}.get(ch, 0)
            k += 1
        j = m.end() + k
        out.append(text[pos:m.start()])
        out.append("\n" * text.count("\n", m.start(), j))
        pos = j
    out.append(text[pos:])
    return "".join(out)


def compiler_sources(root):
    """(path from the root, text) of the compiler's Rust sources, without the
    unit tests (a file `tests.rs` / `*_tests.rs`, and the bodies of the
    `#[cfg(test)] mod` blocks): the strings the compiler shows."""
    out = []
    for p in sorted((root / "crates").glob("*/src/**/*.rs")):
        if p.name == "tests.rs" or p.name.endswith("_tests.rs"):
            continue
        out.append((p.relative_to(root).as_posix(), without_test_mods(p.read_text(encoding="utf-8"))))
    return out


def unknown_refs(sources, headings):
    """(path:line, section) for every `§x.y` inside a string literal of `sources`
    that is not a numbered heading of the spec."""
    known = set(headings)
    bad = []
    for path, text in sources:
        for line, lit in rust_strings(text):
            for m in SECTION_REF.finditer(lit):
                if m.group(1) not in known:
                    bad.append((f"{path}:{line + lit.count(chr(10), 0, m.start())}", m.group(1)))
    return bad


def untested(cases, headings):
    """The headings no case that runs names, by itself or through a subsection."""
    named = {s.removeprefix("§") for c in cases if c.get("mode") != "none" for s in c["spec"]}
    return [h for h in headings if not any(n == h or n.startswith(h + ".") for n in named)]


def main(argv=None, root=ROOT, cmd=repo.CASES_CMD):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true")
    g.add_argument("--list", action="store_true")
    args = ap.parse_args(argv)
    try:
        cases = load_cases(root, cmd)
    except (repo.RepoError, OSError, json.JSONDecodeError) as e:
        print(f"cannot list the cases: {e}")
        return 1
    headings = spec_blocks.headings((root / SPEC).read_text(encoding="utf-8"))
    if args.check:
        bad = unknown(cases, headings)
        for path, s in bad:
            print(f"{path}: [test] spec names {s}, which is not a numbered heading of {SPEC}")
        named = sum(1 for c in cases if c["spec"])
        print(f"{len(cases)} cases, {named} name sections; " + (f"{len(bad)} unknown" if bad else "all are headings"))
        refs = unknown_refs(compiler_sources(root), headings)
        for where, s in refs:
            print(f"{where}: a string of the compiler names §{s}, which is not a numbered heading of {SPEC}")
        return 1 if bad or refs else 0
    left = untested(cases, headings)
    print(f"{len(headings) - len(left)} of {len(headings)} sections have a case; without one:")
    for h in left:
        print(f"  {'  ' * h.count('.')}§{h}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
