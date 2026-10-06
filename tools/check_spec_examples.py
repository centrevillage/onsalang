#!/usr/bin/env python3
"""Check that every ```onsa block in the spec appears verbatim in tests/spec (D-06, P9).

The match is by lines: the lines of the normalized block must appear as
consecutive lines of a normalized test file. Normalizing drops line-end
`//~ ...` markers (so negative examples from the spec can carry
expected-diagnostic markers), the indentation and trailing spaces of each
line, and the blank lines around the text.

Blocks whose copy is not updated yet are listed in `tests/pending.toml` as
`spec-example` entries (Q-08, C-63). The check fails when
  - a block is not found and is not listed,
  - a listed block is found (remove the entry),
  - an entry names no block of the spec (the block changed or was removed),
  - a fence of the spec cannot be trusted: one that is not closed, one that
    looks like onsa but is not spelled ```onsa, or an empty ```onsa block
    (the list cannot silence these).

A block is named "§<section> <hash>: <first line>" (`spec_blocks.spec_id`).
The name does not depend on line numbers; messages show the current line.

Usage: tools/check_spec_examples.py [spec.md] [tests/spec] [--pending FILE]
Exit 0 if the spec and the list agree, 1 otherwise.
"""
import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import pending  # noqa: E402
import spec_blocks  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


def contains_lines(body, block):
    """Whether the lines `block` appear as consecutive lines of `body`."""
    n = len(block)
    first = block[0]
    return any(body[i] == first and body[i : i + n] == block for i in range(len(body) - n + 1))


def check(spec_path, tests_dir, pending_path, root=ROOT):
    """Return (problems, notes). A problem fails the check."""
    spec_text = Path(spec_path).read_text(encoding="utf-8")
    corpus = {
        p: spec_blocks.normalize(p.read_text(encoding="utf-8")).split("\n")
        for p in sorted(Path(tests_dir).rglob("*.onsa"))
    }
    entries, load_errors = pending.load(pending_path)
    listed = {e.target: e for e in pending.of_kind(entries, "spec-example")}
    spec_name = Path(spec_path).name
    shown_list = pending.show_path(pending_path, root)
    problems = [f"{shown_list}: {m}" for m in load_errors]
    notes = []
    blocks, fence_errors = spec_blocks.scan(spec_text)
    problems += [f"{spec_name}:{line}  {m} (not silenced by the list)" for line, m in fence_errors]
    seen = set()
    all_ids = []
    for b in blocks:
        sid = spec_blocks.spec_id(b.section, b.code)
        all_ids.append((b.line, sid))
        where = f"{spec_name}:{b.line}"
        norm = spec_blocks.normalize(b.code)
        if not norm:
            problems.append(f"{where}  the ```onsa block is empty (not silenced by the list)")
            continue
        lines = norm.split("\n")
        found = next((p for p, body in corpus.items() if contains_lines(body, lines)), None)
        entry = listed.get(sid)
        if entry is not None:
            seen.add(sid)
            if found is not None:
                problems.append(
                    f"{where}  found verbatim in {pending.show_path(found, root)} but listed as pending "
                    f"(until {entry.until}); remove the entry from {shown_list}:\n"
                    f"      target = {spec_blocks.toml_string(sid)}"
                )
            else:
                notes.append(f"{where}  pending until {entry.until} ({', '.join(entry.reasons)})")
        elif found is None:
            problems.append(
                f"{where}  not found verbatim under {pending.show_path(tests_dir, root)} and not listed in "
                f"{shown_list}:\n"
                f"      target = {spec_blocks.toml_string(sid)}"
            )
    for sid, entry in listed.items():
        if sid in seen:
            continue
        msg = f"{entry.label()}: names no ```onsa block of {spec_name} (the block changed or was removed)"
        hints = _hints(sid, all_ids)
        if hints:
            msg += "\n" + "\n".join(f"      now {spec_name}:{line}: {cur}" for line, cur in hints)
        problems.append(msg)
    return problems, notes


def _hints(sid, all_ids):
    """Blocks that look like the one an outdated entry meant: same hash, or same section and first line."""
    old = spec_blocks.parse_id(sid)
    if old is None:
        return []  # not of the form; tools/pending.py reports it
    out = []
    for line, cur in all_ids:
        new = spec_blocks.parse_id(cur)
        if new and ((new[0], new[2]) == (old[0], old[2]) or new[1] == old[1]):
            out.append((line, cur))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description="Check the spec's ```onsa blocks against tests/spec.")
    ap.add_argument("spec", nargs="?", type=Path, default=ROOT / "onsa-lang-spec-0.3.md")
    ap.add_argument("tests", nargs="?", type=Path, default=ROOT / "tests" / "spec")
    ap.add_argument("--pending", type=Path, default=ROOT / pending.PENDING)
    args = ap.parse_args(argv)
    problems, notes = check(args.spec, args.tests, args.pending)
    for n in notes:
        print(n)
    for p in problems:
        print(p)
    if problems:
        print(f"{len(problems)} problem(s) between {args.spec.name} and {pending.show_path(args.tests, ROOT)}")
        return 1
    print(f"all spec examples are covered by {pending.show_path(args.tests, ROOT)} ({len(notes)} pending)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
