"""What the gate's tools share about the repository (D-15: each in one place).

- the paths of the spec and of the documents with tables;
- reading a document, a section of it, and the IDs of its table rows;
- running `onsa_cases` (the test runner's and the compiler's lists) and
  reading its JSON;
- reading the plan §5: the retired codes and the codes of the second phase;
- the git directories of a root: the main tree or a worktree (`git_dirs`, `tree_kind`).
"""
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = Path("onsa-lang-spec-0.3.md")
DOC_REWORK = Path("docs") / "rework-phase1.md"
DOC_PLAN = Path("docs") / "implementation-tasks.md"
DOC_REVIEW = Path("docs") / "review-impl-phase1.md"
DOC_API = Path("docs") / "api-candidates.md"
PENDING = Path("tests") / "pending.toml"
# The saved fuzz inputs (tools/fuzz.py, W1-04); `onsa_tests::case::EXCLUDED` keeps them out of the cases.
FUZZ_DIR = Path("tests") / "fuzz"
CASES_CMD = ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--")

CODE = re.compile(r"(?<![A-Za-z0-9_])E\d{4}(?![0-9])")


class RepoError(Exception):
    pass


def read(root, rel):
    try:
        return (Path(root) / rel).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise RepoError(f"{rel}: {e}") from e


def rows(text, id_pattern):
    """{id: done} of the table rows whose first cell is an ID (`| S-45 |`, `| W1-01 ✅ |`)."""
    out = {}
    for m in re.finditer(rf"^\| ({id_pattern})( ✅)?[ |]", text, re.M):
        out[m.group(1)] = bool(m.group(2))
    return out


def section(text, start, end, doc):
    """The text from the heading line `start` up to the heading line `end`."""
    out, inside = [], False
    for line in text.split("\n"):
        if line.startswith(start):
            inside = True
        elif inside and line.startswith(end):
            break
        if inside:
            out.append(line)
    if not out:
        raise RepoError(f"{doc}: the section `{start}` is not found")
    return "\n".join(out)


def cases_json(root, cmd, *args):
    """The JSON `onsa_cases <args>` prints. Raises RepoError when it fails."""
    argv = [*cmd, *args]
    try:
        out = subprocess.run(argv, cwd=root, capture_output=True, text=True)
    except OSError as e:
        raise RepoError(f"cannot run `{' '.join(argv)}`: {e}") from e
    if out.returncode != 0:
        raise RepoError(f"`{' '.join(argv)}` failed (exit {out.returncode}):\n{out.stderr.rstrip()}")
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError as e:
        raise RepoError(f"`{' '.join(argv)}` printed no JSON: {e}") from e


# ---------------------------------------------------------------- plan §5

RETIRED_HEAD = "欠番:"
PHASE2_CELL = "第 2 期"
# "E0612〜E0614": every code from the first to the last.
CODE_RANGE_CELL = re.compile(r"E(\d{4})\s*〜\s*E(\d{4})")


def _plan_section5(plan_text):
    return section(plan_text, "## 5.", "## 6.", DOC_PLAN)


def retired_codes(plan_text):
    """The retired codes: the line of §5 that starts with "欠番:". Codes in
    parentheses and after its first sentence are not retired."""
    lines = [line for line in _plan_section5(plan_text).split("\n") if line.startswith(RETIRED_HEAD)]
    if len(lines) != 1:
        raise RepoError(f"{DOC_PLAN} §5: expected one line starting with `{RETIRED_HEAD}`, found {len(lines)}")
    body = re.sub(r"（[^）]*）|\([^)]*\)", "", lines[0][len(RETIRED_HEAD) :]).split("。", 1)[0]
    codes = set(CODE.findall(body))
    if not codes:
        raise RepoError(f"{DOC_PLAN} §5: the `{RETIRED_HEAD}` line names no code")
    return codes


def phase2_codes(plan_text):
    """The codes of the rows of the §5 table whose last cell is "第 2 期".
    Ranges in the first cell (`E0612〜E0614`) are expanded."""
    codes = set()
    for line in _plan_section5(plan_text).split("\n"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2 or cells[-1] != PHASE2_CELL:
            continue
        first = cells[0]
        for m in CODE_RANGE_CELL.finditer(first):
            lo, hi = int(m.group(1)), int(m.group(2))
            if hi < lo:
                raise RepoError(f"{DOC_PLAN} §5: the range `{m.group(0)}` goes down")
            codes |= {f"E{n:04d}" for n in range(lo, hi + 1)}
        codes |= set(CODE.findall(CODE_RANGE_CELL.sub("", first)))
    if not codes:
        raise RepoError(f"{DOC_PLAN} §5: no row of the table is `{PHASE2_CELL}`")
    return codes


# ---------------------------------------------------------------- build outputs

BUILD_MANIFESTS = ("onsa.toml", "Cargo.toml")


def is_build_output(root, rel):
    """`rel` (relative to the root, `/`-separated) is inside a build output
    directory: `target/` at the root, or a `target/` next to an `onsa.toml` or a
    `Cargo.toml` (spec §15.1; cargo). A `target` anywhere else is an ordinary name."""
    parts = [p for p in rel.split("/") if p]
    for i, p in enumerate(parts):
        if p == "target":
            parent = Path(root).joinpath(*parts[:i])
            if i == 0 or any((parent / m).is_file() for m in BUILD_MANIFESTS):
                return True
    return False


# ---------------------------------------------------------------- git trees

GIT_TIMEOUT = 60


def git_dirs(root):
    """(git directory, common git directory), absolute, when `root` is the top of a git work
    tree; None otherwise (not git, git missing, a directory inside a tree: the self-tests'
    made-up roots)."""
    try:
        r = subprocess.run(
            ["git", "rev-parse", "--path-format=absolute", "--show-toplevel", "--git-dir", "--git-common-dir"],
            cwd=root, capture_output=True, text=True, timeout=GIT_TIMEOUT,
        )  # fmt: skip
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = r.stdout.splitlines()
    if r.returncode != 0 or len(lines) != 3 or Path(lines[0]).resolve() != Path(root).resolve():
        return None
    return Path(lines[1]), Path(lines[2])


def main_tree(root):
    """The main tree of the repository of `root` (the parent of the common git directory), or None."""
    dirs = git_dirs(root)
    return dirs[1].parent if dirs else None


def tree_kind(root):
    """`"main"` (the main tree), `"worktree"` (a git worktree of it), or None (not the top of a git tree)."""
    dirs = git_dirs(root)
    if dirs is None:
        return None
    return "main" if dirs[0].resolve() == dirs[1].resolve() else "worktree"
