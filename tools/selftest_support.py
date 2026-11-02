"""Helpers shared by the self-tests of the tools (tools/test_*.py, tools/*/test_*.py): small made-up
inputs (a spec, a `tests/spec`, a pending list and the files of the IDs) in a temporary directory.
"""
import datetime
import io
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

# the self-tests put tools/ on sys.path before they import this module
import check_spec_examples as cse
import docs as docs_tool
import pending
import repo
import spec_blocks


# A stand-in for `onsa_cases --serve` (W4-18 U10c; tools/test_fuzz.py, tools/test_fmt_props.py): each
# request runs the fakes (the compiler is `fake_onsa.py` beside it, or $FAKE_SERVE_ONSA; words starting
# with `--`, this script) on its files in a directory of its own; a fake ended by a signal ends the server
# with SIGKILL, as a stack overflow aborts the real one.
FAKE_SERVE = r"""
import sys
if sys.argv[1:] == ["--serve"]:
    import os, subprocess, tempfile  # here alone: the fakes it runs start sooner
    here = os.path.dirname(os.path.abspath(__file__))
    onsa = os.environ.get("FAKE_SERVE_ONSA", os.path.join(here, "fake_onsa.py"))
    inp, out = sys.stdin.buffer, sys.stdout.buffer
    while line := inp.readline():
        words, n = line.decode().rstrip("\n").rsplit("\t", 1)
        with tempfile.TemporaryDirectory() as d:
            names = []
            for _ in range(int(n)):
                name, size = inp.readline().decode().rstrip("\n").rsplit("\t", 1)
                path = os.path.join(d, name)
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "wb") as f:
                    f.write(inp.read(int(size)))
                names.append(name)
            script = os.path.abspath(__file__) if words.startswith("--") else onsa
            r = subprocess.run([sys.executable, "-B", script, *words.split(" "), *names], cwd=d, capture_output=True)
        if r.returncode < 0:
            os.kill(os.getpid(), 9)
        out.write(f"{r.returncode}\t{len(r.stdout)}\t{len(r.stderr)}\n".encode() + r.stdout + r.stderr)
        out.flush()
    sys.exit(0)
"""


# The IDs of the made-up repository (`Repo`): {ID: (status, title)}. Only `status` and the heading are
# written: `pending.load_docs` reads no field table.
REPO_IDS = {
    "W1-01": ("DONE", "gate"), "W3-07": ("PLAN", "式と演算子"), "W3-08": ("PLAN", "宣言と属性"), "W5-07": ("PLAN", "sum"),
    "S-34": ("DECIDED", "derive"), "S-45": ("DECIDED", "群"), "S-15": ("DROPPED", "取り下げ"),
    "R-23": ("OPEN", "sum"), "R-113": ("OPEN", "基盤"),
    "A-01": ("OPEN", "is_some"),
}

# the table of the codes (`tasks/diag-codes.md`)
CODES = """\
# 診断コード

| コード | 内容 | 段 | M |
|---|---|---|---|
| E0601 | 効果 | 効果 | M3 |
| E0612〜E0614, E0620 | handler・ポリシー | — | 第 2 期 |
| E0904 / E0905 | rt と blocking | — | 第 2 期 |

欠番: E0611（S-77 で E0601 にまとめた）、E0814（S-147 で E0815 にまとめた）。照合は E0999 を除かない。
"""

# the table of the stages (X-2 U6): the stages and their order; the last ends the first phase
STAGES = """\
# 段

| 段 | 名前 | 主な決定 | 前提 |
|---|---|---|---|
| W1 | 基盤 | — | なし |
| W3 | 構文 | — | W1 |
| W5 | 型 | — | W3 |
| M5 | std | — | — |
| M9 | 締め | — | — |

W5 の後は M5〜M9。
"""

SPEC = """\
# Spec

## 3. 演算子

### 3.1 群

```onsa
let a = x + y - z
let b = x + y * z
```

```c
#ifndef H
#define H
#endif
```

```onsa
use std.fs.{Fs}
fn first() {}
```

## 17. 例

### 17.4 声

```onsa
use std.fs.{Fs}
fn second() {}
```
"""

COPY_FIRST = """\
//! mode: check
pub fn wrap(x: F32, y: F32, z: F32) {
    let a = x + y - z   //~ E0010
    let b = x + y * z
}
"""


def entry(kind, target, reasons=("S-45",), until="W3-07", note="n"):
    rs = ", ".join(f'"{r}"' for r in reasons)
    t = spec_blocks.toml_string(target)
    return f'[[pending]]\nkind = "{kind}"\ntarget = {t}\nreasons = [{rs}]\nuntil = "{until}"\nnote = "{note}"\n\n'


def quiet(fn, *args, **kw):
    old = sys.stdout, sys.stderr
    sys.stdout, sys.stderr = io.StringIO(), io.StringIO()
    try:
        return fn(*args, **kw)
    finally:
        sys.stdout, sys.stderr = old


def handback_line(text, kind="assistant"):
    """A line of an agent's record with a SubagentHandback of `text`, made now (its `timestamp`, as Claude Code's);
    `kind` "api-request-blob" is Claude Code's copy of an earlier one in a later call, with no timestamp (X-11)."""
    use = {"type": "tool_use", "name": "SubagentHandback", "input": {"message": text}}
    now = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")
    line = {"type": kind, "message": {"role": "assistant", "content": [use]}}
    return json.dumps({**line, "timestamp": now} if kind == "assistant" else line, ensure_ascii=False) + "\n"


def quiet_out(fn, *args, **kw):
    """(what `fn` returns, the lines it printed to stdout and stderr)."""
    out = io.StringIO()
    with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
        code = fn(*args, **kw)
    return code, out.getvalue().splitlines()


class Repo:
    """A made-up repository root."""

    def __init__(self, tmp):
        self.root = Path(tmp)
        for id_, (status, title) in REPO_IDS.items():
            self.write_id(id_, status, title)
        for rel, text in {
            str(repo.DIAG_CODES): CODES,
            "tasks/stages.md": STAGES,
            "spec.md": SPEC,
            "tests/spec/ops/groups.onsa": COPY_FIRST,
            "tests/pending.toml": "",
        }.items():
            self.write(rel, text)
        self.write_spec(SPEC)

    def write_id(self, id_, status, title=""):
        """The file of an ID with its `status` and its heading."""
        return self.write(repo.path_of(id_), f'+++\nstatus = "{status}"\n+++\n# {id_}{" " + title if title else ""}\n')

    def write_spec(self, text):
        """The spec in `spec/` (`split_spec`, in place of the one there); a text with no chapter heading is
        the text of a chapter `## 2. x`."""
        for p in (self.root / repo.SPEC_DIR).glob("*.md"):
            if p.name != repo.SPEC_TOOLS.name:
                p.unlink()
        if not re.search(r"^## ([2-9]|\d\d+)\. ", text, re.M):
            text = f"## 2. x\n\n{text}"
        split_spec(text, self.root)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    @property
    def spec(self):
        return self.root / "spec.md"

    @property
    def tests(self):
        return self.root / "tests" / "spec"

    @property
    def pending(self):
        return self.root / "tests" / "pending.toml"

    def ids(self):
        blocks, errors = spec_blocks.scan(self.spec.read_text(encoding="utf-8"))
        assert not errors, errors
        return [spec_blocks.spec_id(b.section, b.code) for b in blocks]

    def check_spec(self):
        return cse.check(self.spec, self.tests, self.pending, self.root)

    def validate(self, pendable=("c-header",)):
        entries, errors = pending.load(self.pending)
        return errors + pending.validate(entries, pending.load_docs(self.root), self.root, list(pendable))


class TempRepo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Repo(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()


def json_cmd(outputs):
    """A stand-in for `onsa_cases`: prints `outputs[<first argument>]` as JSON."""
    script = "import json, sys; o = json.loads(sys.argv[1]); print(json.dumps(o[sys.argv[2]]))"
    return (sys.executable, "-B", "-c", script, json.dumps(outputs))


def git_in(tree, *args):
    return subprocess.run(["git", "-C", str(tree), "-c", "user.name=t", "-c", "user.email=t@t",
                           "-c", "commit.gpgsign=false", *args], capture_output=True, text=True, check=True).stdout


NOTHING = "auto sweep: nothing (the commit touches neither the code nor the cases)"  # `on_commit`


FIELDS_HEADER = "| キー | 形 | 値 | 要る | 意味 |\n|---|---|---|---|---|\n"
# A made-up repository in the new layout (X-2 DS-1): it passes `docs check`.
NEW_LAYOUT = {
    "decisions/README.md": "# 決定\n\n## 頭の欄\n\n" + FIELDS_HEADER + """\
| `status` | 閉じた値 | `OPEN` / `DECIDED` / `DROPPED` | はい | 状態 |
| `spec` | 節の並び | — | いいえ | 仕様の節 |
| `tasks` | ID の並び（W、T、PH2） | — | いいえ | 担う作業 |
| `found_by` | 文字列 | — | いいえ | 見つけた票 |
| `before` | ID（W、段、PH2） | — | いいえ | 期限の作業 |
| `group` | 整数 | — | いいえ | 組 |
| `decided` | 日付 | — | いいえ | 決めた日 |
""",
    "decisions/S/S-1.md": """\
+++
status = "DECIDED"
spec = ["§2.1"]
tasks = ["W1-01"]
decided = 2026-10-15
+++
# S-1 字句

- 決定: W1-02 で §3 と §2 を見る（計画 §8.6・§9、`docs/x.md` §5、`tools.md §1`）。
- 経緯: C-40 と T5-8 と D-15 は確かめない。`decisions/S/S-2.md` も指す。

```onsa
S-77 §7
```
""",
    "decisions/S/S-2.md": """\
+++
status = "OPEN"
tasks = ["W1-02", "PH2"]
found_by = "W1-01/t"
+++
# S-2
- 空白: R-1 と A-1。
""",
    "decisions/S/S-2.draft.md": "+++\ngroup = \n+++\n# S-3 S-999 §99\n",  # a draft is not checked
    "decisions/A/A-1.md": '+++\nstatus = "DECIDED"\n+++\n# A-1 is_some\n',
    "tasks/W/README.md": "# 作業\n\n## 頭の欄\n\n" + FIELDS_HEADER + """\
| `status` | 閉じた値 | `PLAN` / `PENDING` / `DOING` / `DONE` | はい | 状態 |
| `size` | 閉じた値 | `S` / `M` / `L` | いいえ | 大きさ |
| `depends` | ID の並び（W、段） | — | いいえ | 依存 |
| `marks` | 閉じた値の並び | `基盤` / `メモ` | いいえ | 印 |
| `doing` | 文字列の並び | — | いいえ | 出ている票 |
| `commit` | 文字列 | — | いいえ | コミット |
""",
    "tasks/W/W1-01.md": '+++\nstatus = "DONE"\ncommit = "abc"\n+++\n# W1-01 gate\n',
    "tasks/W/W1-02.md": """\
+++
status = "DOING"
size = "M"
depends = ["W1-01"]
marks = ["基盤"]
doing = ["U2/i"]
+++
# W1-02 式
""",
    "tasks/stages.md": "# 段\n\n| 段 | 名前 |\n|---|---|\n| W1 | 基盤 |\n| W2 | 直し |\n| M5 | std |\n| M9 | 締め |\n",
    "tasks/diag-codes.md": "# 診断コード\n\n| コード | 内容 | 段 | M |\n|---|---|---|---|\n"
                           "| E0612〜E0613 | x | — | 第 2 期 |\n\n欠番: E0611（S-1 でまとめた）。\n",
    "issues/R/README.md": "# 問題\n\n## 頭の欄\n\n" + FIELDS_HEADER + """\
| `status` | 閉じた値 | `OPEN` / `WONTFIX` / `DONE` | はい | 状態 |
| `severity` | 閉じた値 | 高 / 中 / 低 | いいえ | 重さ |
| `aspect` | 閉じた値 | 1 / 2 / 3 | いいえ | 観点 |
| `spec` | 節の並び | — | いいえ | 仕様の節 |
| `decisions` | ID の並び（S） | — | いいえ | 決定 |
| `fix` | ID の並び（W） | — | いいえ | 直す作業 |
| `found_by` | 文字列 | — | いいえ | 見つけた票 |
""",
    "issues/R/R-1.md": """\
+++
status = "OPEN"
severity = "中"
aspect = 1
decisions = ["S-2"]
fix = ["W1-02"]
found_by = "W1-02/b"
+++
# R-1 候補
""",
    "spec/README.md": "# Spec\n\n## 0. 目的\n\n### 0.1 原則\n\n---\n\n## 1. 全体\n\n---\n\n## 章の一覧\n\n"
                      "| § | ファイル |\n|---|---|\n| 2 | [字句](02-a.md) |\n| 3 | [演算子](03-b.md) |\n",
    "spec/02-a.md": "## 2. 字句\n\n### 2.1 文字\n\n```\n## 9. not a heading\n```\n\n### 2.2 キーワード\n\n```\nfn let\n```\n\n---\n\n",
    "spec/03-b.md": "## 3. 演算子\n\n### 3.1 群\n\n```onsa\nlet a = x + y - z\n```\n",
    "spec/tools.md": "# tools\n\n## 1. graph\n\n```onsa\nprev~(x)\n```\n",
    "rules/README.md": "# 規則\n\n- [共通](common.md)\n- [`x`](../README.md)\n",
    "rules/common.md": "# 共通\n",
    "README.md": '# Onsa\n\n[仕様](spec/README.md)、[決定](decisions/ "題")、[外](https://example.com/x)、[節](#a)、`[コード](none.md)`\n',
    "tests/pending.toml": "",
}


def split_spec(text, root):
    """Cut a spec of one file into `spec/` as the migration does: the README is the text before
    `## 2.` and the list of the chapters, a chapter starts at its `## N.` (not in a code block)."""
    lines = text.split("\n")
    kinds = docs_tool.line_kinds(lines)[0]
    starts = [i for i, line in enumerate(lines) if kinds[i] == docs_tool.TEXT and re.match(r"## ([2-9]|\d\d+)\. ", line)]
    root = Path(root)
    (root / "spec").mkdir(parents=True, exist_ok=True)
    head = "\n".join(lines[: starts[0]]) + "\n"
    for sec, rel in repo.SPEC_PARTS.items():  # a part of the README: its heading to the next one after it
        found = spec_blocks.heading_lines(head)
        at = [i for i, (_, s) in enumerate(found) if s == sec or s.startswith(sec + ".")]
        if at:
            h = head.split("\n")
            a, b = found[at[0]][0] - 1, (found[at[-1] + 1][0] - 1 if at[-1] + 1 < len(found) else len(h) - 1)
            (root / rel).write_bytes("".join(x + "\n" for x in h[a:b]).encode())
            head = "".join(x + "\n" for x in h[:a]) + "\n".join(h[b:])
    (root / repo.SPEC_README).write_bytes((head + repo.SPEC_INDEX_HEAD + "\n\n| § | ファイル |\n").encode())
    for a, b in zip(starts, [*starts[1:], len(lines)]):
        n = int(re.match(r"## (\d+)", lines[a]).group(1))
        part = "\n".join(lines[a:b]) + ("\n" if b < len(lines) else "")
        (root / "spec" / f"{n:02d}-c.md").write_bytes(part.encode())
