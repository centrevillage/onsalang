"""What the gate's tools share about the repository (D-15: each in one place).

- the paths of the spec and of the documents with tables;
- reading a document, a section of it, and the IDs of its table rows;
- running `onsa_cases` (the test runner's and the compiler's lists) and
  reading its JSON;
- reading the plan §5 (`tasks/diag-codes.md`): the retired codes and the codes of the second phase;
- the Markdown documents the document tools read (`doc_files`, X-2 DT-7);
- the kinds of the IDs and their paths (`KINDS`, X-2 DT-1), where each kind and the spec are read
  from (`Layout`: the new layout or the current tables, X-2 DT-7), and the spec as one text
  (`spec_doc`, `tools_doc`);
- the git directories of a root: the main tree or a worktree (`git_dirs`, `tree_kind`).
"""
import json
import re
import subprocess
from dataclasses import dataclass
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


def read_exact(root, rel):
    """The text of a file with its line ends as they are (no newline translation)."""
    try:
        return (Path(root) / rel).read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise RepoError(f"{rel}: {e}") from e


def row_re(id_pattern):
    """A table row whose first cell is an ID (`| S-45 |`, `| W1-01 ✅ |`): the ID, the mark of done."""
    return re.compile(rf"^\| ({id_pattern})( ✅)?[ |]", re.M)


def rows(text, id_pattern):
    """{id: done} of the table rows whose first cell is an ID."""
    return {m.group(1): bool(m.group(2)) for m in row_re(id_pattern).finditer(text)}


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


def _codes_table(text, doc):
    """(the text of the table of the codes, its name in messages): the plan §5, or the whole
    `tasks/diag-codes.md` (X-2 DF-6)."""
    if Path(doc) == DOC_PLAN:
        return section(text, "## 5.", "## 6.", DOC_PLAN), f"{DOC_PLAN} §5"
    return text, str(doc)


def diag_text(root):
    """(the text, the document) of the table of the codes, as `Layout` reads it."""
    doc = DIAG_CODES if Layout(root).source("diag") == "new" else DOC_PLAN
    return read(root, doc), doc


def retired_codes(text, doc=DOC_PLAN):
    """The retired codes: the line of §5 that starts with "欠番:". Codes in
    parentheses and after its first sentence are not retired."""
    body, name = _codes_table(text, doc)
    lines = [line for line in body.split("\n") if line.startswith(RETIRED_HEAD)]
    if len(lines) != 1:
        raise RepoError(f"{name}: expected one line starting with `{RETIRED_HEAD}`, found {len(lines)}")
    body = re.sub(r"（[^）]*）|\([^)]*\)", "", lines[0][len(RETIRED_HEAD) :]).split("。", 1)[0]
    codes = set(CODE.findall(body))
    if not codes:
        raise RepoError(f"{name}: the `{RETIRED_HEAD}` line names no code")
    return codes


def phase2_codes(text, doc=DOC_PLAN):
    """The codes of the rows of the §5 table whose last cell is "第 2 期".
    Ranges in the first cell (`E0612〜E0614`) are expanded."""
    codes = set()
    body, name = _codes_table(text, doc)
    for line in body.split("\n"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2 or cells[-1] != PHASE2_CELL:
            continue
        first = cells[0]
        for m in CODE_RANGE_CELL.finditer(first):
            lo, hi = int(m.group(1)), int(m.group(2))
            if hi < lo:
                raise RepoError(f"{name}: the range `{m.group(0)}` goes down")
            codes |= {f"E{n:04d}" for n in range(lo, hi + 1)}
        codes |= set(CODE.findall(CODE_RANGE_CELL.sub("", first)))
    if not codes:
        raise RepoError(f"{name}: no row of the table is `{PHASE2_CELL}`")
    return codes


# ---------------------------------------------------------------- the documents (X-2 DT-7)

# The directories of the new layout (X-2 DS-1). `history/` is never read.
DOC_DIRS = ("decisions", "issues", "tasks", "spec", "rules")
SPEC_DIR = "spec"
DOC_TOOLS = Path("docs") / "onsa-tools.md"  # the spec of the tools (`spec/tools.md` after the migration)
ROOT_DOCS = (Path("README.md"), Path("CLAUDE.md"))


def doc_files(root, spec=True):
    """The Markdown documents the document tools read (`tools/docs.py`), relative to the root and
    sorted: the files under the directories of the new layout, the current `docs/*.md`, and the
    root's README.md and CLAUDE.md. Each is read where it is, so the union becomes the new layout
    alone as the migration moves the current files (DS-5 keeps no copy); the older specs at the root
    go to `history/` as they are and are not read. The spec (`spec/`, the spec file, the spec of the
    tools) only with `spec`."""
    root = Path(root)
    found = [p.relative_to(root) for d in DOC_DIRS for p in (root / d).rglob("*.md") if p.is_file()]
    found += [p.relative_to(root) for p in (root / "docs").glob("*.md") if p.is_file()]
    found += [p for p in (*ROOT_DOCS, SPEC) if (root / p).is_file()]
    return sorted({p for p in found if spec or not is_spec_doc(p)})


def is_spec_doc(rel):
    """`rel` (relative to the root) is the spec: a file of `spec/`, the spec file, the spec of the tools."""
    rel = Path(rel)
    return rel.parts[:1] == (SPEC_DIR,) or rel in (SPEC, DOC_TOOLS)



# ---------------------------------------------------------------- the IDs and their paths (X-2 DT-1, DS-1)


@dataclass(frozen=True)
class Kind:
    name: str
    pattern: str  # the spelling of an ID: the file name and the bare ID in the text
    dir: str = None  # the directory of the new layout; None: no file to check (the history, P2)
    draft: bool = False  # has drafts `S-xxx.draft.md`
    old: tuple = None  # the current table: (document, first heading, next heading, what); None: no reader
    bare: bool = True  # looked for as a bare ID in the text


KINDS = (
    Kind("S", r"S-\d+", "decisions/S", True, (DOC_PLAN, "## 2.", "## 3.", "S numbers")),
    Kind("D", r"D-\d+", "decisions/D"),
    Kind("K", r"K-\d+", "decisions/K"),
    Kind("Q", r"Q-\d+", "decisions/Q"),
    Kind("A", r"A-\d+", "decisions/A", old=(DOC_API, None, None, "A numbers")),
    Kind("R", r"R-\d+", "issues/R", old=(DOC_REVIEW, None, None, "R numbers")),
    Kind("RF", r"RF-\d+", "issues/RF"),
    Kind("X", r"X-\d+", "issues/X"),
    Kind("W", r"W\d+-\d+", "tasks/W", old=(DOC_REWORK, "## 3.", "## 4.", "W works")),
    # the kinds whose files are in the history: their IDs are not checked (X-2 DF-6 `refs`)
    Kind("C", r"C-\d+"),
    Kind("T", r"T\d+-\d+", old=(DOC_PLAN, "## 4.", "## 5.", "T works")),  # read while the plan §4 is there
    Kind("P2", r"P2", bare=False),  # the second phase in `tasks` (X-2 DF-4); not an ID in the text
)
KIND = {k.name: k for k in KINDS}
# A bare ID: not after a letter, a digit, `_` or `-`, not before a digit (no `F-8` in `UTF-8`).
ID_RE = re.compile(
    r"(?<![A-Za-z0-9_-])(?:"
    + "|".join(k.pattern for k in sorted(KINDS, key=lambda k: -len(k.name)) if k.bare)
    + r")(?![0-9])"
)
SECTION_RE = re.compile(r"(?:(?P<tools>tools\.md) )?§(?P<num>\d+(?:\.\d+)*)")


def kind_of(id_):
    """The Kind whose spelling is the whole of `id_`, or None."""
    return next((k for k in KINDS if re.fullmatch(k.pattern, id_)), None)


def path_of(id_, draft=False):
    """`S-537` -> `decisions/S/S-537.md` (`.draft.md` with `draft`)."""
    kind = kind_of(id_)
    if kind is None or kind.dir is None or (draft and not kind.draft):
        raise RepoError(f"{id_}: no {'draft' if draft else 'file'} of the new layout for it")
    return Path(kind.dir) / f"{id_}{'.draft' if draft else ''}.md"


def section_path(root, sec):
    """`§6.1` -> `spec/06-<name>.md` (the chapter), `§0` and `§1` -> `spec/README.md`,
    `tools.md §3.2` -> `spec/tools.md`. Only in the new layout."""
    m = SECTION_RE.fullmatch(sec)
    if m is None:
        raise RepoError(f"{sec}: not a section (`§6.1` or `tools.md §3.2`)")
    if not (Path(root) / SPEC_README).is_file():
        raise RepoError(f"{sec}: the spec is not split into {SPEC_DIR}/ (no {SPEC_README})")
    if m.group("tools"):
        return SPEC_TOOLS
    n = int(m.group("num").split(".")[0])
    path = SPEC_README if n <= 1 else chapters(root).get(n)
    if path is None:
        raise RepoError(f"{sec}: no chapter file {SPEC_DIR}/{n:02d}-*.md")
    return path


# ---------------------------------------------------------------- where each kind is read from (X-2 DT-7)

SPEC_README = Path(SPEC_DIR) / "README.md"
SPEC_TOOLS = Path(SPEC_DIR) / "tools.md"
DIAG_CODES = Path("tasks") / "diag-codes.md"
# the documents that are not kinds of IDs: (the new file, the current file; None: the plan §5)
FILES = {"spec": (SPEC_README, SPEC), "tools": (SPEC_TOOLS, DOC_TOOLS), "diag": (DIAG_CODES, None)}


class Layout:
    """Where each kind of ID, the spec, the spec of the tools and the table of the codes are read
    from: the new layout when its directory (file) is there, else the current table (DT-C). Both
    are an error (the migration keeps no copy, DS-5); the current table is looked at for that only
    when the new one is there. Nothing is read before it is asked; each document is read once."""

    def __init__(self, root):
        self.root, self._texts, self._source = Path(root), {}, {}

    def text(self, rel):
        if rel not in self._texts:
            self._texts[rel] = read(self.root, rel)
        return self._texts[rel]

    def source(self, name):
        """"new", "old", or None (no reader of the current documents: D, K, Q, RF, X, C, P2)."""
        if name not in self._source:
            if name in FILES:
                new, has_old = (self.root / FILES[name][0]).is_file(), True
            else:
                kind = KIND[name]
                new, has_old = kind.dir is not None and (self.root / kind.dir).is_dir(), kind.old is not None
            if new and self._old_there(name):
                where = FILES[name][0] if name in FILES else f"{KIND[name].dir}/"
                raise RepoError(f"{name} is in both {where} and {self.old_name(name)}; "
                                "the migration keeps no copy of what it moved (DS-5)")  # fmt: skip
            self._source[name] = "new" if new else "old" if has_old else None
        return self._source[name]

    def old_name(self, name):
        """The current table of a kind (or document), for messages."""
        if name == "diag":
            return f"{DOC_PLAN} §5"
        if name in FILES:
            return str(FILES[name][1])
        doc, start, _, what = KIND[name].old
        return f"the {what} of {doc}" + (f" `{start}`" if start else "")

    def _old_there(self, name):
        if name == "diag":
            return (self.root / DOC_PLAN).is_file() and any(
                line.startswith("## 5.") for line in self.text(DOC_PLAN).split("\n")
            )  # fmt: skip
        if name in FILES:
            return (self.root / FILES[name][1]).is_file()
        return bool(KIND[name].old and self.peek_rows(name))

    def old_rows(self, name):
        """{id: done} of the current table; RepoError when it is not found (as the tools always said)."""
        doc, start, end, what = KIND[name].old
        text = self.text(doc)
        found = rows(section(text, start, end, doc) if start else text, KIND[name].pattern)
        if not found:
            raise RepoError(f"{doc}: no table rows of {what} found" + (f" in `{start}`" if start else ""))
        return found

    def peek_rows(self, name):
        """{id: done} of the current table, or {} when its document or its section is not there."""
        doc, start, end, _ = KIND[name].old
        if not (self.root / doc).is_file():
            return {}
        text = self.text(doc)
        if start and not any(line.startswith(start) for line in text.split("\n")):
            return {}
        return rows(section(text, start, end, doc) if start else text, KIND[name].pattern)

    def old_lines(self, name):
        """{id: line} of the rows of the current table (an ID's first row), or {} when its document or
        its section is not there (as `peek_rows`; the lines of `section`)."""
        doc, start, end, _ = KIND[name].old
        if not (self.root / doc).is_file():
            return {}
        lines = self.text(doc).split("\n")
        lo, hi = 0, len(lines)
        if start:
            lo = next((i for i, line in enumerate(lines) if line.startswith(start)), None)
            if lo is None:
                return {}
            hi = next((i for i in range(lo + 1, len(lines)) if lines[i].startswith(end)), hi)
        row, out = row_re(KIND[name].pattern), {}
        for i in range(lo, hi):
            if m := row.match(lines[i]):
                out.setdefault(m.group(1), i + 1)
        return out


# ---------------------------------------------------------------- the spec as one text (X-2 DS-4, DF-2)

# The heading of `spec/README.md` that starts its list of the chapters: what is before it is the head
# of the spec (its H1 to the end of §1); it and what follows are not part of the spec's text.
SPEC_INDEX_HEAD = "## 章の一覧"
CHAPTER_FILE = re.compile(r"(\d{2})-[a-z0-9-]+\.md")


@dataclass(frozen=True)
class Joined:
    """A text joined from files: `parts` are (file, the line of the text where it starts)."""

    text: str
    parts: tuple

    def locate(self, line):
        """(file, line in it) of a line (from 1) of the text."""
        rel, start = next(p for p in reversed(self.parts) if p[1] <= line)
        return rel, line - start + 1

    def where(self, line):
        rel, n = self.locate(line)
        return f"{Path(rel).as_posix()}:{n}"


def chapters(root):
    """{number: path} of the chapter files of `spec/`. Raises RepoError on another file or a number
    given twice (a file put in the wrong place is never skipped)."""
    out = {}
    for p in sorted((Path(root) / SPEC_DIR).glob("*.md")):
        if p.name in (SPEC_README.name, SPEC_TOOLS.name):
            continue
        m = CHAPTER_FILE.fullmatch(p.name)
        if m is None:
            raise RepoError(f"{SPEC_DIR}/{p.name}: not a chapter file (`NN-<name>.md`), the README or tools.md")
        n = int(m.group(1))
        if n in out:
            raise RepoError(f"{SPEC_DIR}/{p.name}: the chapter {n} is also {out[n].as_posix()}")
        out[n] = Path(SPEC_DIR) / p.name
    return out


def spec_doc(root, layout=None):
    """The spec as one text: the head of `spec/README.md` (before SPEC_INDEX_HEAD) and the chapters in
    the order of their numbers, joined as they are (each chapter keeps the `---` that ends it); or
    the current spec file."""
    if (layout or Layout(root)).source("spec") == "old":
        return Joined(read_exact(root, SPEC), ((SPEC, 1),))
    lines = read_exact(root, SPEC_README).split("\n")
    at = [i for i, line in enumerate(lines) if line == SPEC_INDEX_HEAD]
    if len(at) != 1:
        raise RepoError(f"{SPEC_README}: expected one line `{SPEC_INDEX_HEAD}`, found {len(at)}")
    parts, texts, line = [(SPEC_README, 1)], ["\n".join(lines[: at[0]]) + "\n"], at[0] + 1
    found = chapters(root)
    if not found:
        raise RepoError(f"{SPEC_DIR}/: no chapter file (`NN-<name>.md`)")
    for n, rel in sorted(found.items()):
        text = read_exact(root, rel)
        if not text.startswith(f"## {n}. "):
            raise RepoError(f"{rel.as_posix()}:1: a chapter file starts with its heading `## {n}. `")
        if not texts[-1].endswith("\n"):
            raise RepoError(f"{Path(parts[-1][0]).as_posix()}: does not end with a line end")
        parts.append((rel, line))
        texts.append(text)
        line += text.count("\n")
    return Joined("".join(texts), tuple(parts))


def spec_text(root):
    return spec_doc(root).text


def tools_doc(root):
    """The spec of the tools: `spec/tools.md` or the current `docs/onsa-tools.md`."""
    rel = SPEC_TOOLS if Layout(root).source("tools") == "new" else DOC_TOOLS
    return Joined(read_exact(root, rel), ((rel, 1),))


def tools_text(root):
    return tools_doc(root).text


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
