#!/usr/bin/env python3
"""Every cargo command resolves the features of the libraries as the workspace does (X-22).

Cargo resolves the features of a library over the packages a command selects:
a member selected alone (`cargo test -p onsa_sema`, `cargo run -p onsa_tests`)
may give a library fewer features than the whole workspace, and then that
library and every crate above it are built once more (twice the compiling and
the writes to the disk). The crate `onsa_workspace_hack` names the features of
the workspace, and every member depends on it, so any selection resolves them.

This check fails when a member does not depend on that crate, and when a member
selected alone resolves a package with other features than the workspace, in a
build (the normal and the build dependencies) or in the tests (also the dev
dependencies). A finding names the features to add to the crate. It also fails
when it reads no member, and when cargo fails (`--locked`: a `Cargo.lock` that
is not up to date is a failure, not rewritten).

Usage: tools/cargo_features.py
Exit 0 if every selection resolves as the workspace, 1 otherwise.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

HACK = "onsa_workspace_hack"
HACK_TOML = f"crates/{HACK}/Cargo.toml"
# (the form, the dependency kinds of `cargo tree -e`)
FORMS = (("build", "normal,build"), ("test", "normal,build,dev"))


def cargo(root, *args):
    r = subprocess.run(["cargo", *args, "--locked"], cwd=root, capture_output=True, text=True)
    if r.returncode != 0:
        lines = r.stderr.strip().splitlines()
        raise repo.RepoError(f"`cargo {' '.join(args)} --locked` failed: {lines[-1] if lines else r.returncode}")
    return r.stdout


def members(root):
    """{member: the names of its dependencies}."""
    meta = json.loads(cargo(root, "metadata", "--format-version", "1", "--no-deps"))
    return {p["name"]: {d["name"] for d in p["dependencies"]} for p in meta["packages"]}


def resolved(root, selection, kinds):
    """{package (`name vX.Y.Z` and its marks): the feature sets it is resolved with}; a package built for the
    host and for the target may have two."""
    out = cargo(root, "tree", "-q", *selection, "-e", kinds, "--prefix", "none", "-f", "{p}\t{f}")
    sets = {}
    for line in out.splitlines():
        if "\t" not in line:  # the heads `[build-dependencies]`, `[dev-dependencies]`
            continue
        p, f = line.removesuffix(" (*)").split("\t", 1)
        sets.setdefault(p, set()).add(frozenset(x for x in f.split(",") if x))
    return sets


def show(features):
    return "[" + ",".join(sorted(features)) + "]"


def check(root=repo.ROOT):
    """Return (problems, summary)."""
    deps = members(root)
    if not deps:
        return ["no member in the workspace; the check would pass reading nothing"], "0 members"
    problems = [
        f"{m} does not depend on {HACK}: add `{HACK}.workspace = true` to its [dependencies]"
        for m in sorted(deps)
        if m != HACK and HACK not in deps[m]
    ]
    found = {}  # (package, features, the workspace's) -> [(member, form)]
    for form, kinds in FORMS:
        whole = resolved(root, ["--workspace"], kinds)
        for m in sorted(deps):
            for p, sets in resolved(root, ["-p", m], kinds).items():
                for fs in sets - whole.get(p, set()):
                    found.setdefault((p, fs, frozenset(whole.get(p, ()))), []).append((m, form))
    for (p, fs, theirs), where in sorted(found.items(), key=lambda kv: (kv[0][0], show(kv[0][1]))):
        name = p.split(" ")[0]
        ms = sorted({m for m, _ in where})
        forms = [f for f, _ in FORMS if any(form == f for _, form in where)]
        sel = f"{len(ms)} member(s) selected alone in the {' and '.join(forms)} ({', '.join(ms)})"
        wider = [w for w in theirs if fs <= w]
        if wider:
            more = min((w - fs for w in wider), key=len)
            todo = (f"add the features {show(more)} of {name} to {HACK_TOML} ([dependencies] if the code links it, "
                    f"[build-dependencies] if it is under a proc-macro or a build script: "
                    f"`cargo tree -p {ms[0]} -e features -i {name}` shows which)")  # fmt: skip
        else:
            todo = f"the workspace resolves it with {' or '.join(map(show, theirs)) or 'nothing'}"
        problems.append(f"{p} is resolved with {show(fs)} by {sel}: {todo}")
    summary = f"{len(deps)} members, {len(FORMS)} forms (build, test)"
    return problems, summary


def main(argv=None, root=repo.ROOT):
    if argv:
        print(__doc__.split("\n\n")[-1].strip())
        return 2
    try:
        problems, summary = check(root)
    except repo.RepoError as e:
        print(e)
        return 1
    for p in problems:
        print(p)
    print(summary)
    if problems:
        print(f"{len(problems)} problem(s) with the features of the cargo commands")
        return 1
    print("every member selected alone resolves the features of the workspace")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
