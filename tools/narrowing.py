"""How the heavy gate items narrow their seeds, and the base binaries (X-1, D-15: one place).

`tools/fuzz.py` and `tools/fmt_props.py` take the same options (`add_arguments`):

    --changed-since REV|auto   the seeds the diff since REV touches (and the untracked
                               ones), and the seeds whose text holds a code (`E0013`) that
                               the code diff names (its added and removed lines outside
                               `tests/`, `tools/`, the documents), at most `--code-cap` of them: the codes
                               with the fewest seeds first, up to the one that would pass the
                               cap (the codes left out are named). `auto`: `git merge-base HEAD dev`.
    --sample F --salt ID       besides, the seeds with sha256("<ID>|<path>") below F of the
                               range, and, for a group (the first 3 parts of the directory,
                               `tests/spec/ops`) none of them falls in, the one of the group
                               with the smallest hash: the same ID picks the same seeds.
    --shard I/K                the seeds with sha256(<path>) % K == I: the K shards are the
                               whole, each seed in one (alone; no other option of these).

With none of them a run is whole. With `--changed-since` or `--sample` it is narrowed: the
caller names directories always in (`always`), and the fuzzing does not fail on a class the
base shows too (`resolve_base`). A shard is a part of the whole run and fails as it does.

The base binaries (`--base auto` of the fuzzing): `<main tree>/target/base/<the first SHORT
characters of the merge base>/{onsa,onsa_cases}`, with a file `COMMIT` that starts the full
SHA of the merge base (7 characters or more). The main tree is `repo.main_tree`; the gate
writes the base (`gate_runs.save_base`) into `base_dir`. A merge base that is HEAD, with no
change of the code (`code_changes`), is not used: the binaries would be the tree's own.
"""
import argparse
import hashlib
import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

import repo

DEV = "dev"
CODE_CAP = 200
SHORT = 7  # a fixed length, not `git rev-parse --short` (its length grows with the repository)
GROUP_PARTS = 3  # the group of the sample's minimum: the first parts of the directory
GIT_TIMEOUT = 60
EXCLUDED_FROM_CODES = ("tests/", "tools/", "rules/", "decisions/", "issues/", "tasks/", "history/")
BASE_FILES = ("onsa", "onsa_cases")  # the base binaries, in `base_dir`
# What the binaries are built from: a tracked change there makes them differ from HEAD's.
BUILT_FROM = ("crates", "tools", "std", "runtime", ":(glob)Cargo.*")
# What the heavy items read: the code and the cases (the tree a run of the main tree compares, X-1).
SWEPT = (*BUILT_FROM, "tests")


class NarrowError(Exception):
    pass


@dataclass(frozen=True)
class Selection:
    changed_since: str = None  # a commit, resolved
    code_cap: int = CODE_CAP
    sample: float = None
    salt: str = None
    shard: tuple = None  # (I, K)

    @property
    def narrowed(self):
        return self.changed_since is not None or self.sample is not None


@dataclass(frozen=True)
class Picked:
    paths: frozenset
    counts: dict = field(default_factory=dict)  # diff, codes, always, sample (an overlap counts in the first)
    note: str = ""

    def describe(self, total, what="seeds"):
        if "shard" in self.counts:
            return f"{len(self.paths)} of {total} {what} (shard {self.counts['shard']})"
        parts = ", ".join(f"{k} {v}" for k, v in self.counts.items())
        return f"{len(self.paths)} of {total} {what} ({parts}{'; ' + self.note if self.note else ''})"


@dataclass(frozen=True)
class Base:
    commit: str  # what the output shows
    onsa: tuple  # the argv of each
    onsa_cases: tuple


def git(root, *args):
    try:
        r = subprocess.run(["git", *args], cwd=root, capture_output=True, timeout=GIT_TIMEOUT)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise NarrowError(f"git {args[0]}: {e}") from None
    if r.returncode != 0:
        err = r.stderr.decode("utf-8", "replace").strip().splitlines()
        raise NarrowError(f"git {' '.join(args)}: {err[-1] if err else f'exit {r.returncode}'}")
    return r.stdout.decode("utf-8", "surrogateescape")


def merge_base(root):
    return git(root, "merge-base", "HEAD", DEV).strip()


def _untracked(root):
    return [p for p in git(root, "ls-files", "--others", "--exclude-standard", "-z").split("\0") if p]


def changed_paths(root, since):
    """The paths (from the root) the diff since `since` touches, and the untracked files."""
    changed = git(root, "diff", "--name-only", "--no-renames", "-z", since).split("\0")
    return {p for p in changed if p} | set(_untracked(root))


def diff_codes(root, since):
    """The codes on the added and removed lines of the diff since `since`, and in the
    untracked files, outside `EXCLUDED_FROM_CODES` (the self-tests of the tools write many
    codes as data: a change of a tool is not a change of those rules)."""
    excludes = [f":(exclude){d.rstrip('/')}" for d in EXCLUDED_FROM_CODES]
    text = git(root, "diff", "--unified=0", "--no-color", since, "--", ".", *excludes)
    lines = [l for l in text.split("\n") if l[:1] in "+-" and not l.startswith(("+++", "---"))]
    codes = set(repo.CODE.findall("\n".join(lines)))
    for p in _untracked(root):
        if not p.startswith(EXCLUDED_FROM_CODES):
            try:
                codes |= set(repo.CODE.findall((Path(root) / p).read_text(encoding="utf-8")))
            except (OSError, UnicodeDecodeError):
                continue  # not text: no code to find
    return codes


def _hash(text):
    return int(hashlib.sha256(text.encode("utf-8", "surrogateescape")).hexdigest()[:16], 16)


def under(path, places):
    """`path` is one of `places` (paths from the root) or inside one of them."""
    return any(path == d.rstrip("/") or path.startswith(d.rstrip("/") + "/") for d in places)


def in_shard(path, shard):
    i, k = shard
    return _hash(path) % k == i


def group(path):
    return "/".join(Path(path).parent.parts[:GROUP_PARTS])


def sampled(paths, fraction, salt):
    """The sample of `paths`: a function of the paths, the fraction and the salt alone."""
    h = {p: _hash(f"{salt}|{p}") / 2**64 for p in paths}
    out = {p for p in paths if h[p] < fraction}
    groups = {}
    for p in paths:
        groups.setdefault(group(p), []).append(p)
    for members in groups.values():
        if not out.intersection(members):
            out.add(min(members, key=lambda p: (h[p], p)))
    return out


def pick(seeds, sel, root, always=()):
    """The seeds of a run that is not whole: `seeds` [(path, text)] is the whole list."""
    paths = [p for p, _ in seeds]
    if sel.shard:
        return Picked(frozenset(p for p in paths if in_shard(p, sel.shard)),
                      {"shard": f"{sel.shard[0]}/{sel.shard[1]}"})
    taken, counts, notes = set(), {}, []

    def add(name, found):
        counts[name] = len(found - taken)
        taken.update(found)

    if sel.changed_since is not None:
        add("diff", set(paths) & changed_paths(root, sel.changed_since))
        codes = diff_codes(root, sel.changed_since)
        by_code = {c: set() for c in codes}
        for p, text in seeds:
            if p not in taken:
                for c in codes.intersection(repo.CODE.findall(text)):
                    by_code[c].add(p)
        found, left_out = set(), []
        for c in sorted(by_code, key=lambda c: (len(by_code[c]), c)):
            if left_out or len(found | by_code[c]) > sel.code_cap:
                left_out.append(c)
            else:
                found |= by_code[c]
        add("codes", found)
        if left_out:
            notes.append(f"codes over the cap {sel.code_cap} left to the sample: {' '.join(sorted(left_out))}")
    if always:
        add("always", {p for p in paths if under(p, always)})
    if sel.sample is not None:
        add("sample", sampled(paths, sel.sample, sel.salt))
    return Picked(frozenset(taken), counts, "; ".join(notes))


def resolve_base(root, spec):
    """The base binaries: a `Base`, the reason they are unknown (a str), or None for `none`."""
    if spec == "none":
        return None
    if spec != "auto":
        d = Path(spec)
        commit_file = d / "COMMIT"
        name = commit_file.read_text(encoding="utf-8").strip() if commit_file.is_file() else d.name
        return _base_in(d, name[:SHORT] or d.name)
    try:
        full = merge_base(root)
    except NarrowError as e:
        return f"no merge base of HEAD and {DEV} ({e})"
    main = repo.main_tree(root)
    if main is None:
        return f"{root} is not the top of a git work tree"
    d = base_dir(main, full)
    try:
        commit = (d / "COMMIT").read_text(encoding="utf-8").strip()
    except OSError:
        return f"no {d / 'COMMIT'}"
    if len(commit) < SHORT or not full.startswith(commit):
        return f"{d / 'COMMIT'} names {commit!r}, not the merge base {full}"
    try:
        same = full == git(root, "rev-parse", "HEAD").strip() and not code_changes(root)
    except NarrowError as e:
        return f"cannot compare the base with HEAD ({e})"
    if same:  # the binaries of the tree itself: they would show every class, the new ones too
        return f"same as HEAD ({full[:SHORT]}, no change of the code): nothing to tell apart"
    return _base_in(d, full[:SHORT])


def code_changes(root):
    """The tracked files of `BUILT_FROM` with changes not committed (from the root)."""
    return [p for p in git(root, "diff", "HEAD", "--name-only", "-z", "--", *BUILT_FROM).split("\0") if p]


def base_dir(main, full):
    """Where the base binaries of the commit `full` (a full SHA) live in the main tree."""
    return Path(main) / "target" / "base" / full[:SHORT]


def _base_in(d, commit):
    tools = [d / f for f in BASE_FILES]
    for t in tools:
        if not (t.is_file() and os.access(t, os.X_OK)):
            return f"no {t}"
    return Base(commit, (str(tools[0]),), (str(tools[1]),))


def add_arguments(ap, base=False):
    g = ap.add_argument_group("narrowing (X-1)")
    g.add_argument("--changed-since", metavar="REV|auto",
                   help=f"the seeds the diff touches and the seeds of its codes (auto: git merge-base HEAD {DEV})")
    g.add_argument("--code-cap", type=int, help=f"at most this many seeds of the codes (default {CODE_CAP})")
    g.add_argument("--sample", type=float, metavar="F", help="also a sample of this fraction of the seeds")
    g.add_argument("--salt", help="the salt of the sample (the ID of the work)")
    g.add_argument("--shard", metavar="I/K", help="the I-th of K shards of the whole")
    if base:
        g.add_argument("--base", default="auto", metavar="auto|none|DIR",
                       help="the base binaries that tell a class from before (default auto)")


def selection(ap, args, root):
    """The `Selection` of the options (None: a whole run); a usage error calls `ap.error`.
    Raises NarrowError when `--changed-since` cannot be resolved."""
    if args.code_cap is not None and (args.code_cap < 0 or args.changed_since is None):
        ap.error("--code-cap must be 0 or more, and goes with --changed-since")
    if (args.sample is None) != (args.salt is None) or (args.sample is not None and not 0 < args.sample <= 1):
        ap.error("--sample (more than 0, at most 1) and --salt go together")
    if args.shard is not None:
        m = re.fullmatch(r"(\d+)/(\d+)", args.shard)
        if not m or not int(m.group(1)) < int(m.group(2)):
            ap.error("--shard is I/K with 0 <= I < K")
        if args.changed_since is not None or args.sample is not None:
            ap.error("--shard goes alone (not with --changed-since, --sample)")
        return Selection(shard=(int(m.group(1)), int(m.group(2))))
    if args.changed_since is None and args.sample is None:
        return None
    since = args.changed_since
    if since == "auto":
        since = merge_base(root)
    elif since is not None:
        since = git(root, "rev-parse", "--verify", "--quiet", f"{since}^{{commit}}").strip()
    cap = CODE_CAP if args.code_cap is None else args.code_cap
    return Selection(since, cap, args.sample, args.salt)


def parse(ap, argv, root_of=lambda a: a.root):
    """`ap.parse_args(argv)` and the selection: (args, Selection or None). Exits 2 when the
    selection cannot be resolved (git)."""
    args = ap.parse_args(argv)
    try:
        return args, selection(ap, args, root_of(args))
    except NarrowError as e:
        ap.exit(2, f"{ap.prog}: cannot narrow the seeds: {e}\n")
