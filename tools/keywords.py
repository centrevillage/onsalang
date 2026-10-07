#!/usr/bin/env python3
"""The keywords of the lexer against the list of the spec (§2.2, W3-02/b 12).

    keywords.py [--root DIR]

The lexer's list comes from the compiler (`onsa_cases --keywords`, the one
table `onsa_syntax::token::KEYWORDS`), the spec's from the code block of §2.2
(`spec_blocks.section_fences`): this tool reads neither Rust nor the lexer.

Each word on one side only is a case of the gate item `keywords`,
`keywords/<word>`. The item applies `tests/pending.toml` itself (by case only):
a listed case that still differs is pending, a listed case that no longer
differs fails (remove the entry), and an unlisted difference fails. An entry
`keywords/<word>` of a word that is on both sides fails too.

Exit 0 when the check passes, 1 otherwise.
"""
import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import pending  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402

ITEM = "keywords"
SECTION = "2.2"


def spec_keywords(spec_text):
    """The words of the first code block of §2.2, in order."""
    fences = spec_blocks.section_fences(spec_text, SECTION)
    if not fences:
        raise repo.RepoError(f"§{SECTION} of {repo.SPEC} has no code block with the keywords")
    return fences[0][1].split()


def differences(spec, lexer):
    """{word: why} for every word on one side only."""
    out = {}
    for w in spec:
        if w not in lexer:
            out[w] = "the spec lists it (§2.2), the lexer does not"
    for w in lexer:
        if w not in spec:
            out[w] = "the lexer has it, the spec does not list it (§2.2)"
    return out


def apply_list(diffs, listed):
    """(pending lines, problem lines) for the differences and the listed words."""
    pend, problems = [], []
    for w, why in sorted(diffs.items()):
        if w in listed:
            pend.append(f"pending {ITEM}/{w}: {why} (until {listed[w].until})")
        else:
            problems.append(f"{ITEM}/{w}: {why}")
    for w, e in sorted(listed.items()):
        if w not in diffs:
            problems.append(f"{ITEM}/{w}: listed in {repo.PENDING}, but the lexer and the spec agree; remove the entry")
    return pend, problems


def main(argv=None, cmd=repo.CASES_CMD):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=repo.ROOT)
    args = ap.parse_args(argv)
    root = args.root
    try:
        lexer = repo.cases_json(root, cmd, "--keywords")
        spec = spec_keywords((root / repo.SPEC).read_text(encoding="utf-8"))
    except (repo.RepoError, OSError, ValueError) as e:
        print(f"cannot read the keywords: {e}")
        return 1
    entries, _ = pending.load(root / repo.PENDING)  # the item `pending` reports the errors
    listed = {
        e.target.split("/", 1)[1]: e
        for e in pending.of_kind(entries, "gate")
        if e.target.startswith(ITEM + "/")
    }
    pend, problems = apply_list(differences(spec, lexer), listed)
    for line in pend + problems:
        print(line)
    print(f"{len(lexer)} keywords in the lexer, {len(spec)} in §{SECTION}; {len(pend)} pending, {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
