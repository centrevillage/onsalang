#!/usr/bin/env python3
"""Check that every ```onsa block in the spec appears verbatim in tests/spec (D-06, P9).

Line-end `//~ ...` markers in the test files are ignored when matching, so
negative examples from the spec can carry expected-diagnostic markers.

Usage: tools/check_spec_examples.py [spec.md] [tests/spec]
Exit 0 if every block is covered, 1 otherwise.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "onsa-lang-spec-0.3.md"
TESTS = Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "tests" / "spec"

MARKER = re.compile(r"[ \t]*//~.*$", re.M)


def blocks(spec_text):
    """Yield (start_line, code) for each ```onsa fence."""
    lines = spec_text.split("\n")
    i = 0
    while i < len(lines):
        if lines[i].strip() == "```onsa":
            start = i + 1
            j = start
            while j < len(lines) and lines[j].strip() != "```":
                j += 1
            yield start + 1, "\n".join(lines[start:j]).rstrip("\n")
            i = j
        i += 1


def normalize(text):
    text = MARKER.sub("", text)
    return "\n".join(line.strip() for line in text.split("\n")).strip("\n")


def main():
    spec_text = SPEC.read_text(encoding="utf-8")
    corpus = {p: normalize(p.read_text(encoding="utf-8")) for p in sorted(TESTS.rglob("*.onsa"))}
    missing = []
    for line, code in blocks(spec_text):
        norm = normalize(code)
        if not any(norm in body for body in corpus.values()):
            missing.append((line, code.split("\n")[0]))
    if missing:
        print(f"{len(missing)} spec example(s) not found verbatim under {TESTS.relative_to(ROOT)}:")
        for line, head in missing:
            print(f"  {SPEC.name}:{line}  {head}")
        return 1
    print(f"all spec examples are covered by {TESTS.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
