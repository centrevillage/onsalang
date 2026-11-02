#!/usr/bin/env python3
"""The tables and the rows that a tool reads from another part of the repository, against that part (the
`cross-check` gate item, W4-18 U10b): what the self-tests checked of the repository itself, which they no
longer read (tools/selftest.py, `REAL_READS`).

- `c-items`: the C items of `gate_steps.STEPS`, one per row of `onsa_tests::c::ITEMS` in its order and named
  as the row (`onsa_cases --c-items`, W1-06), each pendable;
- `budgets`: the rows of rules/budgets.md that tools/refactor.py and tools/work.py read are there and say
  what they read;
- `doc-fields`: the keys of `docs.RESTS_ON` are the ID fields of the field tables of the READMEs, each with
  its direction (`docs.undirected`), and the labels of the body of a work (tasks/W/README.md) hold one
  持ち越し, the label `docs.py ticket` reads (`docs.CARRIED`).

A new check is one row of CHECKS: (name, a function of the root and the onsa_cases command to its problems).

    python3 -B tools/crosscheck.py [--root DIR]

Exit 0 when every check finds nothing, 1 otherwise.
"""
import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs  # noqa: E402
import gate_steps  # noqa: E402
import refactor  # noqa: E402
import repo  # noqa: E402
import work  # noqa: E402


def c_items(root, cmd, steps=None):
    rows = repo.cases_json(root, cmd, "--c-items")
    prefix = gate_steps.C_CHECK
    have = [s for s in (gate_steps.STEPS if steps is None else steps) if s.argv[: len(prefix)] == prefix]
    problems = [] if rows else ["onsa_cases --c-items gives no item"]
    if [(s.name, s.argv[len(prefix):]) for s in have] != [(n, (n,)) for n in rows]:
        problems.append(f"the C items of tools/gate_steps.py ({', '.join(s.name for s in have) or 'none'}) are not "
                        f"the rows of onsa_tests::c::ITEMS in their order ({', '.join(rows) or 'none'})")
    problems += [f"the C item {s.name} is not pendable" for s in have if not s.pendable or s.info]
    return problems


def budgets(root, cmd=None):
    return [why for why in (refactor.limits(root), work.refactor_size(root)) if isinstance(why, str)]


def doc_fields(root, cmd=None):
    tree = docs.Tree(root, [])
    tables = [tree.index.table(n) for n in tree.index.files]
    fields = {k for t in tables if isinstance(t, docs.FieldTable) for k, f in t.fields.items() if f.base == "ID"}
    problems = [f"a README of {n} has no field table" for n, t in zip(tree.index.files, tables)
                if not isinstance(t, docs.FieldTable)]  # fmt: skip
    problems += [f"docs.RESTS_ON has `{k}`, an ID field of no README" for k in sorted(set(docs.RESTS_ON) - fields)]
    problems += [f"{r.as_posix()}: the ID field `{k}` has no direction in docs.RESTS_ON"
                 for r, _, k in docs.undirected(tree)]  # fmt: skip
    labels = docs.body_labels(tree, repo.KIND["W"])
    if len([x for x in labels if docs.CARRIED.fullmatch(f"- {x}:")]) != 1:
        problems.append(f"the labels of the body of a work need one 持ち越し (`docs.py ticket`): "
                        f"{', '.join(labels) or 'none'}")
    return problems


CHECKS = (("c-items", c_items), ("budgets", budgets), ("doc-fields", doc_fields))


def main(argv=None, root=repo.ROOT, cmd=repo.CASES_CMD, checks=CHECKS):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=None)
    root = ap.parse_args(argv).root or root
    failed = 0
    for name, check in checks:
        try:
            problems = check(root, cmd)
        except repo.RepoError as e:
            problems = [f"cannot check: {e}"]
        failed += bool(problems)
        print("\n".join([f"{name}: ok"] if not problems else [f"{name}: {p}" for p in problems]))
    print(f"cross-check: {len(checks)} check(s), {failed} with problems" if checks else "cross-check: no check")
    return 1 if failed or not checks else 0


if __name__ == "__main__":
    sys.exit(main())
