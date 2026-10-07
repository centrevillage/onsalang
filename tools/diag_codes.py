#!/usr/bin/env python3
"""The diagnostic codes: the registry against the spec, and the negative examples.

    diag_codes.py --registry    the registry equals the codes the spec text names,
                                minus the retired codes of the plan §5 (S-109, K-12)
    diag_codes.py --negatives   every code has NEGATIVE_MIN negative examples, or a
                                `diag-code` entry in tests/pending.toml (plan §8.3 2, K-13)

The registry comes from the compiler (`onsa_cases --codes`), the runs of the
cases from the test runner (`onsa_cases --run`); this module never reads Rust.
The plan §5 is read in `repo.py`: the retired codes (its "欠番:" line) and the
codes of the second phase (the rows of its table marked "第 2 期").

A negative example is a `//~` marker that a run compared and a diagnostic
matched. Not counted: the markers of a case with `mode = "none"`, of a case
listed as a whole in tests/pending.toml (`test-case` "<path>"), and of the
directories the scan excludes (the runner never reports them). A case listed
by test (`<path>::<name>`) still compares its markers, so they count. A
marker compared once per target counts once: markers are counted by (case,
file, line, code).

The `diag-code` entries: a code short of examples must be listed; a listed
code with enough examples fails (remove the entry). `until = "P2"` (K-13
rule 3) is for the codes of the second phase only, and a code of the second
phase that is listed has `until = "P2"`.

Exit 0 when the check passes, 1 otherwise, 2 on a usage error.
"""
import argparse
import re
import sys
from collections import Counter
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT

# Negative examples each code needs (plan §8.3 2, Q-13). The one place of the number.
NEGATIVE_MIN = 3

CODE = repo.CODE
# "E0410〜E0416" names the codes in between without writing them: the check
# cannot see those, so a range in the spec fails instead of being skipped.
CODE_RANGE = re.compile(
    r"(?<![A-Za-z0-9_])E\d{4}\s*(?:〜|～|~|\.\.\.|\.\.|…|--|-|–|—|から|to(?![A-Za-z]))\s*E?\d"
)

CheckError = repo.RepoError


def spec_codes(text):
    """The codes the spec names. Raises CheckError on a range of codes."""
    ranges = [m.group(0) for m in CODE_RANGE.finditer(text)]
    if ranges:
        raise CheckError(
            f"{repo.SPEC} writes a range of codes ({', '.join(ranges)}); write every code, "
            "so that the registry can be checked against it"
        )
    return set(CODE.findall(text))


def registry_codes(root, cmd):
    return {c["code"] for c in repo.cases_json(root, cmd, "--codes")}


def check_registry(registry, spec, retired):
    """Problems of `registry == spec - retired`."""
    problems = []
    expected = spec - retired
    for c in sorted(expected - registry):
        problems.append(f"{c}: the spec names it, but the registry (crates/onsa_diag/src/codes.rs) does not have it")
    for c in sorted(registry - expected):
        if c in retired:
            problems.append(f"{c}: a retired code (plan §5), but the registry still has it")
        else:
            problems.append(f"{c}: in the registry, but the spec does not name it")
    return problems


def count_negatives(runs, entries):
    """{code: negative examples} of the runs (see the module doc)."""
    whole = {e.target for e in pending.of_kind(entries, "test-case") if "::" not in e.target}
    seen = set()
    for case in runs["cases"]:
        if case["mode"] == "none" or case["path"] in whole:
            continue
        for m in case["markers"]:
            if m["matched"]:
                seen.add((case["path"], m["file"], m["line"], m["code"]))
    return Counter(code for _, _, _, code in seen)


def check_negatives(counts, registry, entries, phase2):
    """Problems of the `diag-code` entries against the counts and the codes of
    the second phase."""
    problems = []
    listed = {e.target: e for e in pending.of_kind(entries, "diag-code")}
    for code in sorted(registry):
        n = counts.get(code, 0)
        e = listed.get(code)
        if n < NEGATIVE_MIN and e is None:
            problems.append(
                f"{code}: {n} negative example(s), fewer than {NEGATIVE_MIN}, and not listed; add examples, or add "
                f'a "diag-code" entry to {repo.PENDING} whose until is the work that adds them (K-13)'
            )
        elif n >= NEGATIVE_MIN and e is not None:
            problems.append(f"{code}: {n} negative examples, but {e.label()} still lists it (until {e.until}); remove the entry")
        elif e is not None and code in phase2 and e.until != pending.PHASE2:
            problems.append(
                f'{e.label()}: a code of the second phase (plan §5), so its until is "{pending.PHASE2}", not {e.until}'
            )
    for target, e in sorted(listed.items()):
        if target not in registry:
            problems.append(f"{e.label()}: not a code of the registry")
        elif e.until == pending.PHASE2 and target not in phase2:
            problems.append(
                f'{e.label()}: until "{pending.PHASE2}", but the plan §5 does not put it in the second phase; '
                "name the work of the first phase that adds its examples"
            )
    for code in sorted(set(counts) - registry):
        problems.append(f"{code}: markers name it, but it is not a code of the registry")
    return problems


def main(argv=None, root=ROOT, cmd=repo.CASES_CMD):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--registry", action="store_true")
    g.add_argument("--negatives", action="store_true")
    args = ap.parse_args(argv)
    try:
        registry = registry_codes(root, cmd)
        plan = repo.read(root, repo.DOC_PLAN)
        if args.registry:
            spec = spec_codes(repo.read(root, repo.SPEC))
            retired = repo.retired_codes(plan)
            problems = check_registry(registry, spec, retired)
            summary = (
                f"{len(registry)} codes in the registry; the spec names {len(spec)}, "
                f"{len(retired)} retired ({', '.join(sorted(retired))})"
            )
        else:
            phase2 = repo.phase2_codes(plan)
            entries, load_errors = pending.load(root / repo.PENDING)
            if load_errors:
                raise CheckError("\n".join(load_errors))
            runs = repo.cases_json(root, cmd, "--run", str(root))
            problems = [f"cannot scan the cases: {e}" for e in runs["errors"]]
            counts = count_negatives(runs, entries)
            problems += check_negatives(counts, registry, entries, phase2)
            short = sorted(c for c in registry if counts.get(c, 0) < NEGATIVE_MIN)
            summary = (
                f"{len(registry)} codes ({len(phase2)} of the second phase); {len(registry) - len(short)} have "
                f"{NEGATIVE_MIN} or more negative examples, {len(short)} fewer: "
                + (", ".join(f"{c} {counts.get(c, 0)}" for c in short) or "none")
            )
    except (CheckError, OSError) as e:
        print(f"cannot check: {e}")
        return 1
    for p in problems:
        print(p)
    print(summary)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
