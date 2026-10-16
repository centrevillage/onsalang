#!/usr/bin/env python3
"""Self-tests of the gate's own checks (the `gate-selftest` item of tools/gate_steps.py).

Small made-up inputs: a spec, a `tests/spec`, a pending list and the document
tables, in a temporary directory. The gate's wiring is tested with made-up
items that stand in for cargo.

    python3 -B tools/test_gate.py
"""
import argparse
import datetime
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
import types
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import builtin_names  # noqa: E402
import check_spec_examples as cse  # noqa: E402
import default_inits  # noqa: E402
import diag_codes  # noqa: E402
import docs as docs_tool  # noqa: E402
import fmt_props  # noqa: E402
import fuzz  # noqa: E402
import gap_marks  # noqa: E402
import gate  # noqa: E402
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import ignored_files  # noqa: E402
import keywords  # noqa: E402
import narrowing  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402
import spec_sections  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent / "vectors"))
from test_vectors import VectorsTools  # noqa: E402,F401  (the tests of the `vectors` item run here)

REWORK = """\
# rework
## 3. 段ごとの作業
| ID | 作業 |
|---|---|
| W1-01 ✅ | gate |
| W3-07 | 式と演算子 |
| W3-08 | 宣言と属性 |
| W5-07 | sum |
## 4. 第 1 期の残り
| W9-99 | not a work (outside §3) |
"""

PLAN = """\
# plan
## 2. 仕様の空白（S）
| ID | 項目 |
|---|---|
| S-34 ✅ | derive |
| S-45 ✅ | 群 |
| S-15 | 取り下げ |
## 3. 共通の設計
| S-99 ✅ | not an S row (outside §2) |
## 4. 作業
| T1-1 ✅ | 字句解析器 |
| T5-8 | 生成 |
| T9-2 | 締め |
## 5. 診断コード
| コード | 内容 | 段 | M |
|---|---|---|---|
| E0601 | 効果 | 効果 | M3 |
| E0612〜E0614, E0620 | handler・ポリシー | — | 第 2 期 |
| E0904 / E0905 | rt と blocking | — | 第 2 期 |

欠番: E0611（S-77 で E0601 にまとめた）、E0814（S-147 で E0815 にまとめた）。照合は E0999 を除かない。
## 6. 仕様の例
"""

API = """\
# api
| ID | 候補 |
|---|---|
| A-01 | is_some |
"""

REVIEW = """\
# review
## 8. 決定の記録
| R-23 | sum |
| R-113 / Q-01〜Q-08 | 基盤 |
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


def allowed(cls, inp, reasons=("S-45",), note="n", left="m"):
    """An entry of `tests/fuzz/allowed.toml` (R-207)."""
    rs = ", ".join(f'"{r}"' for r in reasons)
    return (f"[[allowed]]\nclass = {spec_blocks.toml_string(cls)}\nleft = {spec_blocks.toml_string(left)}\n"
            f"input = {spec_blocks.toml_string(inp)}\nreasons = [{rs}]\nnote = \"{note}\"\n\n")


def quiet(fn, *args, **kw):
    old = sys.stdout, sys.stderr
    sys.stdout, sys.stderr = io.StringIO(), io.StringIO()
    try:
        return fn(*args, **kw)
    finally:
        sys.stdout, sys.stderr = old


class Repo:
    """A made-up repository root."""

    def __init__(self, tmp):
        self.root = Path(tmp)
        for rel, text in {
            "docs/rework-phase1.md": REWORK,
            "docs/implementation-tasks.md": PLAN,
            "docs/review-impl-phase1.md": REVIEW,
            "docs/api-candidates.md": API,
            "spec.md": SPEC,
            str(repo.SPEC): SPEC,
            "tests/spec/ops/groups.onsa": COPY_FIRST,
            "tests/pending.toml": "",
        }.items():
            self.write(rel, text)

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


class SpecExamples(TempRepo):
    def setUp(self):
        super().setUp()
        self.first, self.fs_a, self.fs_b = self.repo.ids()

    def list_(self, *targets):
        self.repo.write("tests/pending.toml", "".join(entry("spec-example", t) for t in targets))

    def test_ids(self):
        self.assertRegex(self.first, r"^§3\.1 [0-9a-f]{8}: let a = x \+ y - z$")
        # the `#ifndef` inside the C fence is not a heading
        self.assertTrue(self.fs_a.startswith("§3.1 "), self.fs_a)
        self.assertTrue(self.fs_b.startswith("§17.4 "), self.fs_b)
        for sid in (self.first, self.fs_a, self.fs_b):
            self.assertIsNotNone(spec_blocks.parse_id(sid))
            self.assertRegex(sid, pending.TARGET_FORMS["spec-example"])

    def test_same_first_line_is_two_names(self):
        self.assertNotEqual(self.fs_a, self.fs_b)
        self.assertEqual(self.fs_a.split(": ", 1)[1], self.fs_b.split(": ", 1)[1])
        self.list_(self.fs_a)
        problems, notes = self.repo.check_spec()
        self.assertEqual(len(notes), 1)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("spec.md:28", problems[0])  # the current line of the second block
        self.assertIn(self.fs_b, problems[0])

    def test_unlisted_mismatch_fails(self):
        self.list_(self.fs_a)
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("not found verbatim", problems[0])
        self.assertIn(f'target = "{self.fs_b}"', problems[0])

    def test_listed_mismatches_pass(self):
        self.list_(self.fs_a, self.fs_b)
        problems, notes = self.repo.check_spec()
        self.assertEqual(problems, [])
        self.assertEqual(len(notes), 2)
        self.assertIn("spec.md:19", notes[0])

    def test_listed_but_found_fails(self):
        self.list_(self.first, self.fs_a, self.fs_b)
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("remove the entry", problems[0])
        self.assertIn("ops/groups.onsa", problems[0])

    def test_changed_block_fails(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("fn second() {}", "fn second() { }"))
        problems, _ = self.repo.check_spec()
        stale = [p for p in problems if "names no ```onsa block" in p]
        self.assertEqual(len(stale), 1, problems)
        self.assertIn(self.fs_b.split(" ")[0], stale[0])
        self.assertIn("now spec.md:28", stale[0])  # the hint: same section and first line
        # the changed block is unlisted now, so it fails too
        self.assertTrue(any("not found verbatim" in p for p in problems), problems)

    def test_removed_block_fails(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.split("## 17.")[0])
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("names no ```onsa block", problems[0])

    def test_renumbered_section_fails_with_hint(self):
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("### 17.4 声", "### 17.5 声"))
        problems, _ = self.repo.check_spec()
        stale = [p for p in problems if "names no ```onsa block" in p]
        self.assertEqual(len(stale), 1, problems)
        self.assertIn("§17.5", stale[0])  # the hint: same hash

    def test_malformed_target_is_stale(self):
        self.list_(self.fs_a, self.fs_b, "not an id")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"not an id": names no ```onsa block', problems[0])

    def test_names_do_not_depend_on_lines_or_indentation(self):
        moved = SPEC.replace("# Spec\n", "# Spec\n\nmore text\n\nand more\n").replace("fn second() {}", "    fn second() {}")
        self.repo.write("spec.md", moved)
        self.assertEqual(self.repo.ids(), [self.first, self.fs_a, self.fs_b])

    def test_markers_and_indentation_of_the_copy_are_ignored(self):
        self.list_(self.fs_a, self.fs_b)
        problems, _ = self.repo.check_spec()
        self.assertEqual(problems, [])  # COPY_FIRST carries `//~` and indentation

    def test_match_is_by_whole_lines(self):
        # `let a = 1` is not in `let a = 10`, nor a line in the middle of another
        self.repo.write("spec.md", "## 1. x\n\n```onsa\nlet a = 1\n```\n\n```onsa\nb = 2\n```\n")
        self.repo.write("tests/spec/ops/groups.onsa", "let a = 10\nlet b = 2\n")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 2, problems)
        self.repo.write("tests/spec/ops/groups.onsa", "fn f() {\n  let a = 1\n}\nb = 2\n")
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_lines_must_be_consecutive(self):
        self.repo.write("spec.md", "## 1. x\n\n```onsa\nlet a = 1\nlet b = 2\n```\n")
        self.repo.write("tests/spec/ops/groups.onsa", "let a = 1\nlet c = 3\nlet b = 2\n")
        self.assertEqual(len(self.repo.check_spec()[0]), 1)

    def test_empty_block_fails(self):
        self.repo.write("spec.md", "## 1. x\n\n```onsa\n\n```\n")
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("empty", problems[0])

    def test_unclosed_fence_fails(self):
        # a `c` fence left open would swallow the onsa block after it
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC.replace("#endif\n```\n", "#endif\n"))
        problems, _ = self.repo.check_spec()
        self.assertTrue(any("is not closed" in p for p in problems), problems)
        self.repo.write("spec.md", SPEC + "\n```onsa\nlet z = 1\n")
        problems, _ = self.repo.check_spec()
        self.assertTrue(any('"' + "`" * 3 + 'onsa" is not closed' in p for p in problems), problems)

    def test_onsa_like_fences_fail(self):
        self.list_(self.fs_a, self.fs_b)
        for opener, closer in [
            ("```onsa,x", "```"),
            ("````onsa", "````"),
            ("~~~onsa", "~~~"),
            ("```Onsa", "```"),
            ("``` onsa", "```"),
        ]:
            with self.subTest(opener=opener):
                self.repo.write("spec.md", SPEC + f"\n{opener}\nlet hidden = 1\n{closer}\n")
                problems, _ = self.repo.check_spec()
                self.assertEqual(len(problems), 1, problems)
                self.assertIn("looks like onsa", problems[0])
                self.assertIn("not silenced by the list", problems[0])

    def test_other_fences_are_fine(self):
        extra = "\n```toml\n[a]\n```\n\n```\nplain\n```\n\n~~~text\n```onsa\n~~~\n\n````md\n```onsa\nx\n```\n````\n"
        self.list_(self.fs_a, self.fs_b)
        self.repo.write("spec.md", SPEC + extra)
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_suggested_target_is_toml(self):
        self.repo.write("spec.md", '## 1. x\n\n```onsa\nlet s = "a\\\\b"  // é\n```\n')
        problems, _ = self.repo.check_spec()
        self.assertEqual(len(problems), 1, problems)
        line = problems[0].split("\n")[1].strip()
        parsed = tomllib.loads(line)["target"]
        self.assertEqual(parsed, self.repo.ids()[0])
        self.assertIn("é", line)  # non-ASCII is kept
        # pasted back into the list, the block is pending
        self.repo.write("tests/pending.toml", entry("spec-example", parsed))
        self.assertEqual(self.repo.check_spec()[0], [])

    def test_cli(self):
        self.list_(self.fs_a)
        args = [str(self.repo.spec), str(self.repo.tests), "--pending", str(self.repo.pending)]
        self.assertEqual(quiet(cse.main, args), 1)
        self.list_(self.fs_a, self.fs_b)
        self.assertEqual(quiet(cse.main, args), 0)


class PendingList(TempRepo):
    def setUp(self):
        super().setUp()
        self.sid = self.repo.ids()[1]

    def errors_of(self, text, **kw):
        self.repo.write("tests/pending.toml", text)
        return self.repo.validate(**kw)

    def assertOneError(self, text, needle):
        errors = self.errors_of(text)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(needle, errors[0])

    def test_valid(self):
        text = (
            entry("spec-example", self.sid)
            + entry("diag-code", "E0812", ("R-23",), "W5-07")
            + entry("gate", "c-x", ("S-34",), "T5-8")
            + entry("gate", "c-header/span_const", ("S-34",), "T5-8")
            + entry("test-case", "tests/spec/ops/groups.onsa::a test", ("S-45",), "W3-08")
            + entry("fuzz-input", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
            + entry("fix-contract", "tests/spec/ops/groups.onsa:12:3 E0010 fix2", ("S-45",), "W3-08")
        )
        self.assertEqual(self.errors_of(text, pendable=("c-header", "c-x")), [])

    def test_empty_list_is_valid(self):
        self.assertEqual(self.errors_of(""), [])

    def test_missing_field(self):
        text = entry("spec-example", self.sid).replace('until = "W3-07"\n', "")
        self.assertOneError(text, "missing field `until`")

    def test_unknown_field(self):
        text = entry("spec-example", self.sid).replace('note = "n"\n', 'note = "n"\nline = 3\n')
        self.assertOneError(text, "unknown field `line`")

    def test_expect_internal(self):
        # only on a whole test case (W1-04), and only "internal"
        whole = entry("test-case", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
        self.assertEqual(self.errors_of(whole.replace('note = "n"\n', 'note = "n"\nexpect = "internal"\n')), [])
        self.assertOneError(whole.replace('note = "n"\n', 'note = "n"\nexpect = "panic"\n'), "`expect` must be one of")
        one_test = entry("test-case", "tests/spec/ops/groups.onsa::a test", ("S-45",), "W3-08")
        self.assertOneError(
            one_test.replace('note = "n"\n', 'note = "n"\nexpect = "internal"\n'), "only for a `test-case` entry"
        )
        fuzz = entry("fuzz-input", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
        self.assertOneError(fuzz.replace('note = "n"\n', 'note = "n"\nexpect = "internal"\n'), "only for a `test-case`")

    def test_no_reason(self):
        self.assertOneError(entry("spec-example", self.sid, reasons=()), "at least one S / R number")

    def test_bad_reason(self):
        self.assertOneError(entry("spec-example", self.sid, reasons=("Q-08",)), "is not an S / R number")

    def test_reason_not_in_tables(self):
        self.assertOneError(entry("spec-example", self.sid, reasons=("S-99",)), "not in the tables")

    def test_work_not_in_tables(self):
        self.assertOneError(entry("spec-example", self.sid, until="W9-99"), "until `W9-99` is not in the tables")

    def test_done_work_fails(self):
        self.assertOneError(entry("spec-example", self.sid, until="T1-1"), "marked done")
        self.assertOneError(entry("spec-example", self.sid, until="W1-01"), "marked done")

    def test_bad_work(self):
        self.assertOneError(entry("spec-example", self.sid, until="M3"), "is not a work ID")

    def test_duplicate(self):
        self.assertOneError(entry("spec-example", self.sid) * 2, "the same target as pending[0]")

    def test_unknown_kind(self):
        self.assertOneError(entry("spec", self.sid), "unknown kind `spec`")

    def test_bad_spec_example_form(self):
        self.assertOneError(entry("spec-example", "ops/groups.onsa:196"), "not of the spec-example form")

    def test_unknown_gate_item(self):
        self.assertOneError(entry("gate", "c-headers/x"), "`c-headers` is not a gate item that may be listed")

    def test_gate_items_that_cannot_be_listed(self):
        # the real items keep the gate complete (or only show something): only the pendable ones may be listed
        for step in gate_steps.STEPS:
            if step.pendable and not step.info:
                continue
            with self.subTest(step=step.name):
                self.repo.write("tests/pending.toml", entry("gate", step.name))
                entries, errors = pending.load(self.repo.pending)
                errors += pending.validate(entries, pending.load_docs(self.repo.root), self.repo.root)
                if step.pendable and not step.info and step.by_case_only:
                    self.assertEqual(len(errors), 1, errors)
                    self.assertIn("may be listed only by case", errors[0])
                    continue
                if step.pendable and not step.info:
                    self.assertEqual(errors, [])
                    continue
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("may be listed", errors[0])

    def test_gate_items_that_may_be_listed(self):
        # the C checks (W1-06): as a whole, or by the cases the item reports
        for target in ("c-gcc", "c-gcc/tests/conformance/voice.onsa[host]", "c-header/tests/x.onsa[t]/c++11-g++-15"):
            with self.subTest(target=target):
                self.repo.write("tests/pending.toml", entry("gate", target))
                entries, errors = pending.load(self.repo.pending)
                errors += pending.validate(entries, pending.load_docs(self.repo.root), self.repo.root)
                self.assertEqual(errors, [])

    def test_vectors_are_listed_by_case_only(self):
        # W2-02: a whole entry of the vectors' items would hide every new failure
        for target in ("vectors-interp/u64.mul", "vectors-c/u32.mul[c-gcc]"):
            with self.subTest(target=target):
                text = entry("gate", target).replace('note = "n"\n', 'note = "n"\nrows = 1\ndigest = "0123456789abcdef"\n')
                self.assertEqual(self.errors_of(text, pendable=gate_steps.pendable()), [])
        for item in ("vectors-interp", "vectors-c"):
            with self.subTest(item=item):
                errors = self.errors_of(entry("gate", item), pendable=gate_steps.pendable())
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("may be listed only by case", errors[0])
        self.assertEqual(gate_steps.by_case_only(), ["vectors-interp", "keywords", "vectors-c"])

    def test_rows_of_the_vectors(self):
        # W2-02/b: a case entry of an item that counts rows says how many (`rows`) and which (`digest`);
        # no other entry has them
        pend = gate_steps.pendable()

        def held(t, rows="1", digest='"0123456789abcdef"'):
            fields = (f"rows = {rows}\n" if rows is not None else "") + (f"digest = {digest}\n" if digest is not None else "")
            return entry("gate", t).replace('note = "n"\n', 'note = "n"\n' + fields)

        self.assertEqual(self.errors_of(held("vectors-c/u32.mul[c-gcc]", "10"), pendable=pend), [])
        self.assertEqual(self.errors_of(held("vectors-interp/u64.mul"), pendable=pend), [])
        for field, text in (("rows", held("vectors-c/u32.mul[c-gcc]", rows=None)),
                            ("digest", held("vectors-c/u32.mul[c-gcc]", digest=None))):  # fmt: skip
            with self.subTest(missing=field):
                errors = self.errors_of(text, pendable=pend)
                self.assertEqual(len(errors), 1, errors)
                self.assertIn(f"`{field}` is required", errors[0])
        for bad in ("0", "-1", "true", '"3"', "1.5"):
            with self.subTest(rows=bad):
                errors = self.errors_of(held("vectors-c/u32.mul[c-gcc]", bad), pendable=pend)
                self.assertTrue(any("`rows` must be a positive integer" in e for e in errors), errors)
        for bad in ('"0123456789ABCDEF"', '"0123456789abcde"', '"0123456789abcdef0"', "12", '"zz23456789abcdef"'):
            with self.subTest(digest=bad):
                errors = self.errors_of(held("vectors-c/u32.mul[c-gcc]", digest=bad), pendable=pend)
                self.assertTrue(any("`digest` must be 16 lowercase hex digits" in e for e in errors), errors)
        for target in ("c-gcc/tests/x.onsa[t]", "c-gcc"):
            with self.subTest(target=target):
                errors = self.errors_of(held(target), pendable=pend)
                self.assertEqual(len(errors), 2, errors)
                self.assertTrue(all("is only for a case entry" in e for e in errors), errors)
        errors = self.errors_of(
            entry("test-case", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08").replace('note = "n"\n', 'note = "n"\nrows = 1\n')
        )
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("`rows` is only for a case entry", errors[0])
        self.assertEqual(gate_steps.counts_rows(), ["vectors-interp", "vectors-c"])

    def test_expect_internal_on_the_vectors_of_the_interpreter(self):
        # only the case entries of an item with expect_internal (vectors-interp, W2-02)
        internal = 'note = "n"\nexpect = "internal"\n'
        ok = entry("gate", "vectors-interp/u64.mul").replace('note = "n"\n', internal + 'rows = 10\ndigest = "0123456789abcdef"\n')
        self.assertEqual(self.errors_of(ok, pendable=gate_steps.pendable()), [])
        for target in ("vectors-c/u64.mul[c-clang]", "c-gcc/tests/x.onsa[t]"):
            with self.subTest(target=target):
                rows = 'rows = 1\ndigest = "0123456789abcdef"\n' if target.startswith("vectors") else ""
                bad = entry("gate", target).replace('note = "n"\n', internal + rows)
                errors = self.errors_of(bad, pendable=gate_steps.pendable())
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("only for a `test-case` entry", errors[0])
        whole = entry("gate", "vectors-interp").replace('note = "n"\n', internal)
        errors = self.errors_of(whole, pendable=gate_steps.pendable())
        self.assertTrue(any("only for a `test-case` entry" in e for e in errors), errors)
        self.assertEqual(gate_steps.expect_internal(), ["vectors-interp"])

    def test_gate_item_whole_and_by_case(self):
        text = entry("gate", "c-header") + entry("gate", "c-header/a[t]/c99-clang") + entry("gate", "c-x/b")
        errors = self.errors_of(text, pendable=("c-header", "c-x"))
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("`c-header` is also listed as a whole", errors[0])

    def test_missing_path(self):
        self.assertOneError(entry("test-case", "tests/spec/nope.onsa"), "does not exist")
        self.assertOneError(entry("fix-contract", "tests/spec/nope.onsa:1:1 E0010 fix1"), "does not exist")

    def test_foreign_form(self):
        # a row of docs/foreign-forms.toml by its id (S-250, W3-15)
        self.assertOneError(entry("foreign-form", "semicolon"), "`docs/foreign-forms.toml` does not exist")
        self.repo.write("docs/foreign-forms.toml", '[[form]]\nid = "semicolon"\n\n[[form]]\nid = "let_mut"\n')
        self.assertEqual(self.errors_of(entry("foreign-form", "semicolon") + entry("foreign-form", "let_mut")), [])
        self.assertOneError(entry("foreign-form", "loop"), "is not the `id` of a row of `docs/foreign-forms.toml`")
        for bad in ("Semicolon", "semi colon", "semi-colon", "_semicolon", "semicolon_", "semi__colon", "1st"):
            with self.subTest(target=bad):
                self.assertOneError(entry("foreign-form", bad), "not of the foreign-form form")
        self.repo.write("docs/foreign-forms.toml", "[[form]\n")
        self.assertOneError(entry("foreign-form", "semicolon"), "is not TOML")

    def test_fix_contract_form(self):
        # one candidate: "<file>:<line>:<col> <code> fix<K>" (W3-17)
        for bad in (
            "tests/spec/ops/groups.onsa:3:5 E0010",
            "tests/spec/ops/groups.onsa:3:5 E0010 fix0",
            "tests/spec/ops/groups.onsa:0:5 E0010 fix1",
            "tests/spec/ops/groups.onsa:3 E0010 fix1",
            "tests/spec/ops/groups.onsa:3:5 e0010 fix1",
            "tests/spec/ops/groups.onsa:3:5  E0010 fix1",
            "tests/spec/ops/groups.onsa:3:5 E0010 fix1 x",
            "tests/spec/ops/groups.onsa",
        ):
            with self.subTest(target=bad):
                self.assertOneError(entry("fix-contract", bad), "not of the fix-contract form")
        self.assertOneError(entry("fix-contract", "./tests/spec/ops/groups.onsa:3:5 E0010 fix1"), "canonical")

    def test_path_outside(self):
        self.assertOneError(entry("fuzz-input", "../x.onsa"), "canonical")
        self.assertOneError(entry("fuzz-input", "/tmp/x.onsa"), "relative to the repository root")

    def test_paths_must_be_canonical(self):
        for bad in (
            "./tests/spec/ops/groups.onsa",
            "tests//spec/ops/groups.onsa",
            "tests/spec/ops/",
            "tests/spec/./ops/groups.onsa",
            "tests/spec/x/../ops/groups.onsa",
            "tests\\spec\\ops\\groups.onsa",
        ):
            with self.subTest(path=bad):
                errors = self.errors_of(entry("test-case", bad))
                self.assertEqual(len(errors), 1, errors)
                self.assertNotIn("does not exist", errors[0])
        self.assertEqual(self.errors_of(entry("test-case", "tests/spec/ops")), [])

    def test_toml_error(self):
        self.assertOneError("[[pending]\n", "pending.toml")

    def test_docs_tables_missing(self):
        self.repo.write("docs/rework-phase1.md", "# rework\nno tables\n")
        with self.assertRaisesRegex(pending.DocsError, "## 3."):
            pending.load_docs(self.repo.root)
        self.repo.write("docs/rework-phase1.md", "## 3. works\nno rows\n## 4. rest\n")
        with self.assertRaisesRegex(pending.DocsError, "no table rows of W works"):
            pending.load_docs(self.repo.root)
        self.assertEqual(quiet(pending.main, ["--root", str(self.repo.root)]), 1)

    def test_stages(self):
        text = entry("spec-example", self.sid) + entry("diag-code", "E0812", until="W5-07") + entry("gate", "c-header", until="T5-8")
        self.repo.write("tests/pending.toml", text)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        self.assertEqual(pending.stage_counts(entries), {"W3": 1, "W5": 1, "M5": 1})
        self.assertEqual(pending.stages_line(entries), "pending by stage: W3 1, W5 1, M5 1 (total 3)")
        self.assertEqual(len(pending.stage_end_errors(entries, "W3")), 1)
        self.assertEqual(pending.stage_end_errors(entries, "W1"), [])

    def test_stage_end_cli(self):
        self.repo.write("tests/pending.toml", entry("spec-example", self.sid))
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W1"]), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W3"]), 1)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W4"]), 2)  # no such stage in the tables
        self.assertEqual(quiet(pending.main, base + ["--stage-end", ""]), 2)

    def test_gate_steps_cli(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-header", until="T5-8"))
        base = ["--root", str(self.repo.root)]
        self.assertEqual(quiet(pending.main, base + ["--gate-steps", "c-header"]), 0)
        self.assertEqual(quiet(pending.main, base + ["--gate-steps", ""]), 1)

    def test_phase2(self):
        # K-13 rule 3: a code of the second phase waits for no work
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", until="P2")), [])
        self.assertOneError(entry("spec-example", self.sid, until="P2"), "only for diag-code")
        self.assertOneError(entry("test-case", "tests/spec/ops/groups.onsa", until="P2"), "only for diag-code")
        self.assertOneError(entry("diag-code", "E0612", until="P3"), "is not a work ID")
        self.assertOneError(entry("diag-code", "E0612", until="p2"), "is not a work ID")

    def test_phase2_spec_sections(self):
        # a P2 entry may give a numbered heading of the spec as a reason
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", reasons=("§17.4", "S-45"), until="P2")), [])
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", reasons=("§3",), until="P2")), [])
        self.assertOneError(entry("diag-code", "E0612", reasons=("§9.9",), until="P2"), "not a numbered heading")
        self.assertOneError(entry("diag-code", "E0612", reasons=("§3.",), until="P2"), "not an S / R number")
        self.assertOneError(entry("diag-code", "E0612", reasons=("§3.1",)), 'only of `until = "P2"`')
        self.assertOneError(entry("spec-example", self.sid, reasons=("§3.1",)), 'only of `until = "P2"`')
        (self.repo.root / repo.SPEC).unlink()
        with self.assertRaisesRegex(pending.DocsError, "onsa-lang-spec"):
            pending.load_docs(self.repo.root)

    def test_phase2_stages(self):
        text = entry("diag-code", "E0612", until="P2") + entry("diag-code", "E0001", until="T9-2") + entry("spec-example", self.sid)
        self.repo.write("tests/pending.toml", text)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        self.assertEqual(pending.stage_of("P2"), "P2")
        # the second phase comes after every stage of the first
        self.assertEqual(pending.stages_line(entries), "pending by stage: W3 1, M9 1, P2 1 (total 3)")
        # the end of the first phase leaves only P2
        left = pending.stage_end_errors(entries, "M9")
        self.assertEqual(len(left), 2, left)
        self.assertFalse(any("E0612" in m for m in left), left)
        self.assertEqual(len(pending.stage_end_errors(entries, "W3")), 1)
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "P2"]), 2)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 1)
        self.repo.write("tests/pending.toml", entry("diag-code", "E0612", until="P2"))
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 0)
        self.assertIn("P2", gate.summary([], pending.load(self.repo.pending)[0], [])[2])


def fake(name, code=0, **kw):
    """A gate item that records its argv in `<cwd>/argv-<name>` and exits with `code`."""
    script = (
        "import sys, pathlib; "
        f"pathlib.Path('argv-{name}').write_text('\\n'.join(sys.argv[1:])); "
        f"sys.exit({code})"
    )
    return gate_steps.Step(name, (sys.executable, "-B", "-c", script), **kw)


class GateRun(TempRepo):
    """Runs `gate.main` on the made-up root."""

    def run_main(self, argv, steps, env=None):
        out = io.StringIO()
        with mock.patch.dict(os.environ, env or {}, clear=False):
            if env is None:
                os.environ.pop("UPDATE_GOLDEN", None)
            old_err, sys.stderr = sys.stderr, io.StringIO()
            try:
                code = gate.main(argv, steps=steps, root=self.repo.root, out=out)
            finally:
                sys.stderr = old_err
        return code, out.getvalue()

    def argv_of(self, name):
        return (self.repo.root / f"argv-{name}").read_text().split("\n")


class GateWiring(GateRun):

    def test_exit_codes(self):
        self.assertEqual(self.run_main([], [fake("a"), fake("b")])[0], 0)
        self.assertEqual(self.run_main([], [fake("a"), fake("b", 1)])[0], 1)
        self.assertEqual(self.run_main(["--stage-end", "W4"], [fake("a")])[0], 2)
        self.assertEqual(self.run_main(["--stage-end", ""], [fake("a")])[0], 2)

    def test_runs_every_item_after_a_failure(self):
        code, out = self.run_main([], [fake("a", 1), fake("b")])
        self.assertEqual(code, 1)
        self.assertTrue((self.repo.root / "argv-b").exists())
        self.assertIn("gate: FAIL (a)", out)

    def test_stage_end_and_gate_steps_are_passed(self):
        steps = [fake("p", stage_args=True, gate_steps=True), fake("q"), fake("c-x", 0, pendable=True)]
        self.assertEqual(self.run_main(["--stage-end", "W3"], steps)[0], 0)
        self.assertEqual(self.argv_of("p"), ["--gate-steps", "c-x", "--stage-end", "W3"])
        self.assertEqual(self.argv_of("q"), [""])
        self.run_main([], steps)
        self.assertEqual(self.argv_of("p"), ["--gate-steps", "c-x"])

    def test_pending_items(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-x", until="T5-8") + entry("gate", "fmt", until="T5-8"))
        code, out = self.run_main(["--work", "T5-8"], [fake("c-x", 1, pendable=True), fake("fmt", 1)])
        self.assertEqual(code, 1)  # `fmt` is not pendable: listing it does not hide its failure
        self.assertIn("PENDING c-x", out)
        self.assertIn("FAIL    fmt", out)
        code, out = self.run_main(["--work", "T5-8"], [fake("c-x", 0, pendable=True)])
        self.assertEqual(code, 1)
        self.assertIn("remove the entry", out)
        # an item that cannot run (exit 2) is not pending (W1-06)
        code, out = self.run_main(["--work", "T5-8"], [fake("c-x", 2, pendable=True)])
        self.assertEqual(code, 1)
        self.assertIn("FAIL    c-x", out)
        self.assertIn("the item cannot run", out)

    def test_items_listed_whole_run_for_their_work_or_a_stage_end(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-x", until="W3-07"))
        steps = [fake("c-x", 0, pendable=True), fake("c-y", 1, pendable=True)]
        ran = self.repo.root / "argv-c-x"
        code, out = self.run_main([], steps)
        self.assertEqual(code, 1)  # an item not listed runs and fails as it is
        self.assertFalse(ran.exists())
        self.assertIn("SKIPPED c-x", out)
        self.assertIn("listed until W3-07: runs with --work W3-07 or --stage-end", out)
        self.run_main(["--work", "W3-08"], steps)
        self.assertFalse(ran.exists())
        code, out = self.run_main(["--work", "W3-08", "--work", "W3-07"], steps)
        self.assertTrue(ran.exists())
        self.assertIn("remove the entry", out)  # it passes: the work fixed it
        ran.unlink()
        self.run_main(["--stage-end", "W3"], steps)
        self.assertTrue(ran.exists())
        # an entry of one case does not skip the item
        self.repo.write("tests/pending.toml", entry("gate", "c-x/a", until="W3-07"))
        ran.unlink()
        self.run_main([], steps)
        self.assertTrue(ran.exists())

    def test_unknown_work_is_a_usage_error(self):
        code, _ = self.run_main(["--work", "W9-99"], [fake("a")])
        self.assertEqual(code, 2)
        self.assertFalse((self.repo.root / "argv-a").exists())

    def test_stage_end_only(self):
        steps = [fake("a"), fake("deep", 0, stage_end_only=True)]
        code, out = self.run_main([], steps)
        self.assertEqual(code, 0)
        self.assertFalse((self.repo.root / "argv-deep").exists())
        self.assertIn("runs only with --stage-end", out)
        self.run_main(["--work", "W3-07"], steps)
        self.assertFalse((self.repo.root / "argv-deep").exists())
        self.run_main(["--stage-end", "W3"], steps)
        self.assertTrue((self.repo.root / "argv-deep").exists())

    def test_quick(self):
        steps = [fake("a"), fake("slow", 1, slow=True)]
        code, out = self.run_main(["--quick"], steps)
        self.assertEqual(code, 0)
        self.assertFalse((self.repo.root / "argv-slow").exists())
        self.assertIn("SKIPPED slow", out)
        self.assertIn("left out by --quick", out)
        self.assertEqual(out.splitlines()[-1], "gate (quick): PASS")  # not the verdict `gate: PASS`
        code, out = self.run_main([], steps)
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines()[-1], "gate: FAIL (slow)")
        steps = [fake("bad", 1), fake("slow", 0, slow=True)]
        self.assertEqual(self.run_main(["--quick"], steps)[1].splitlines()[-1], "gate (quick): FAIL (bad)")
        # it leaves items out, so it does not decide a work or a stage
        self.assertEqual(self.run_main(["--quick", "--stage-end", "W3"], steps)[0], 2)
        self.assertEqual(self.run_main(["--quick", "--work", "W3-07"], steps)[0], 2)

    def test_one_gate_at_a_time(self):
        # a gate that finds the lock taken says so and waits for it
        path = gate.lock_path(self.repo.root)
        self.assertEqual(path, self.repo.root / ".onsa-gate.lock")  # not a git repository
        out = io.StringIO()
        result = {}
        with open(path, "a+") as held:
            gate.fcntl.flock(held, gate.fcntl.LOCK_EX)
            held.write("pid 1 in elsewhere since 00:00:00\n")
            held.flush()
            other = threading.Thread(
                target=lambda: result.setdefault("code", gate.main([], steps=[fake("a")], root=self.repo.root, out=out))
            )
            other.start()
            deadline = time.monotonic() + 10
            while "waiting" not in out.getvalue() and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertIn("another gate runs (pid 1 in elsewhere since 00:00:00); waiting", out.getvalue())
            self.assertFalse((self.repo.root / "argv-a").exists())
        other.join(10)
        self.assertFalse(other.is_alive())
        self.assertEqual(result["code"], 0)
        self.assertTrue((self.repo.root / "argv-a").exists())
        self.assertIn(f"pid {os.getpid()} in ", path.read_text())

    def test_the_lock_is_shared_with_the_worktrees(self):
        root = self.repo.root
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        common = root / ".git"
        self.assertEqual(gate.lock_path(root).resolve(), (common / gate.LOCK).resolve())
        # a directory inside the tree is not its top: a made-up root there keeps its own lock
        self.assertEqual(gate.lock_path(root / "tests"), root / "tests" / ".onsa-gate.lock")
        git = ["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run([*git, "commit", "-q", "--allow-empty", "-m", "a"], cwd=root, check=True)
        tree = Path(self.tmp.name + "-wt")
        subprocess.run(["git", "worktree", "add", "-q", str(tree)], cwd=root, check=True)
        try:
            self.assertEqual(gate.lock_path(tree).resolve(), (common / gate.LOCK).resolve())
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", str(tree)], cwd=root, check=True)

    def test_update_golden_is_refused(self):
        code, _ = self.run_main([], [fake("a")], env={"UPDATE_GOLDEN": "1"})
        self.assertEqual(code, 2)
        self.assertFalse((self.repo.root / "argv-a").exists())

    def test_golden_listing_failure_fails(self):
        # the made-up root is not a git repository
        golden = gate_steps.Step("golden", (sys.executable, "-B", str(gate.TOOLS / "gate.py"), "--golden"), info=True)
        code, out = self.run_main([], [fake("a"), golden])
        self.assertEqual(code, 1)
        self.assertIn("gate: FAIL (golden)", out)
        self.assertIn("golden: cannot list", out)

    def test_results(self):
        listed = {
            "pend-fail": pending.Entry(0, "gate", "pend-fail", ("S-45",), "W3-07", "n"),
            "pend-pass": pending.Entry(1, "gate", "pend-pass", ("S-45",), "W3-07", "n"),
            "not-pendable": pending.Entry(2, "gate", "not-pendable", ("S-45",), "W3-07", "n"),
        }
        steps = [
            fake("ok", 0),
            fake("bad", 1),
            fake("pend-fail", 1, pendable=True),
            fake("pend-pass", 0, pendable=True),
            fake("not-pendable", 1),
            fake("show", 0, info=True),
            fake("show-broken", 1, info=True),
        ]
        results = gate.run_steps(steps, listed, cwd=self.repo.root, out=io.StringIO(), works=("W3-07",))
        self.assertEqual(
            {r.step.name: r.status for r in results},
            {
                "ok": "PASS",
                "bad": "FAIL",
                "pend-fail": "PENDING",
                "pend-pass": "FAIL",
                "not-pendable": "FAIL",
                "show": "INFO",
                "show-broken": "FAIL",
            },
        )
        # without their work, the items listed whole do not run
        results = gate.run_steps(steps, listed, cwd=self.repo.root, out=io.StringIO())
        statuses = {r.step.name: r.status for r in results}
        self.assertEqual((statuses["pend-fail"], statuses["pend-pass"]), ("SKIPPED", "SKIPPED"))
        self.assertEqual(statuses["not-pendable"], "FAIL")
        self.assertFalse(any(r.failed for r in results if r.status == "SKIPPED"))

    def test_summary(self):
        results = gate.run_steps([fake("ok"), fake("bad", 2)], {}, cwd=self.repo.root, out=io.StringIO())
        lines = gate.summary(results, [], ["M tests/golden/c/a.c"])
        self.assertEqual(lines[-1], "gate: FAIL (bad)")
        self.assertIn("    M tests/golden/c/a.c", lines)
        self.assertIn("  pending: none", lines)


def sleeper(name, seconds, **kw):
    """A gate item that sleeps for `seconds` and passes."""
    return gate_steps.Step(name, (sys.executable, "-B", "-c", f"import time; time.sleep({seconds})"), **kw)


class GateForms(GateRun):
    """The forms of a run (X-1 U2): the work check, `--only`, the sweep, the history, the warning."""

    def setUp(self):
        super().setUp()
        self.root = self.repo.root.resolve()  # git names /private/var
        self.repo.root = self.root
        self.repo.write(".gitignore", "target/\nargv-*\n")
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")

    def ran(self, name):
        return (self.root / f"argv-{name}").exists()

    def forget(self):
        for p in self.root.glob("argv-*"):
            p.unlink()

    def history(self, root=None):
        return gate_runs.read_history(root or self.root)[0]

    def elsewhere(self):
        """A directory outside the made-up root, removed after the test."""
        other = tempfile.TemporaryDirectory()
        self.addCleanup(other.cleanup)
        return Path(other.name).resolve()

    def worktree(self):
        wt = self.elsewhere() / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        return wt

    def test_the_work_check_narrows_the_heavy_items(self):
        steps = [fake("fz", narrows=("tools/fuzz.py", "tools/narrowing.py")), fake("st", touches=("tools/",)),
                 fake("plain")]  # fmt: skip
        self.repo.write("crates/x.rs", "fn x() {}\n")
        code, out = self.run_main(["--work", "W3-07", "--work", "W3-08"], steps)
        self.assertEqual(code, 0)
        self.assertEqual(self.argv_of("fz"), ["--changed-since", "auto", "--sample", "0.1", "--salt", "W3-07"])
        self.assertIn("narrowed (sample 0.1, salt W3-07)", out)
        self.assertFalse(self.ran("st"))
        self.assertIn("SKIPPED st", out)
        self.assertIn("the diff does not touch tools/", out)
        self.assertTrue(self.ran("plain"))
        # a diff on the tool of an item runs it whole; any diff in tools/ runs the self-test
        self.forget()
        self.repo.write("tools/narrowing.py", "x = 1\n")
        code, out = self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz"), [""])
        self.assertIn("whole: the diff touches tools/narrowing.py", out)
        self.assertTrue(self.ran("st"))
        (self.root / "tools/narrowing.py").unlink()
        self.repo.write("tools/other.py", "x = 1\n")
        self.forget()
        self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz")[:2], ["--changed-since", "auto"])
        self.assertTrue(self.ran("st"))
        # the whole and the stage end: as before
        (self.root / "tools/other.py").unlink()
        for argv in ([], ["--stage-end", "W3"], ["--stage-end", "W3", "--work", "W3-07"]):
            with self.subTest(argv=argv):
                self.forget()
                self.assertEqual(self.run_main(argv, steps)[0], 0)
                self.assertEqual(self.argv_of("fz"), [""])
                self.assertTrue(self.ran("st"))

    def test_a_diff_that_cannot_be_read_runs_whole(self):
        git_in(self.root, "branch", "-D", "dev")
        steps = [fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",))]
        code, out = self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(code, 0)
        self.assertEqual(self.argv_of("fz"), [""])
        self.assertIn("whole: the diff is not known", out)
        self.assertTrue(self.ran("st"))
        self.assertIn("diff: cannot read it (git merge-base HEAD dev", out)
        self.assertEqual(out.splitlines()[-1], "gate: PASS")

    def test_only(self):
        steps = [fake("a"), fake("b", static=True), fake("c", static=True), fake("bad", 1),
                 fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",)),
                 fake("sv", sweep=True, sweep_only=True)]  # fmt: skip
        code, out = self.run_main(["--only", "a"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate (only): PASS"))
        self.assertEqual([p.name for p in self.root.glob("argv-*")], ["argv-a"])
        self.assertNotIn(" b ", out)
        self.forget()
        code, out = self.run_main(["--only", "static,bad"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (1, "gate (only): FAIL (bad)"))
        self.assertEqual(sorted(p.name for p in self.root.glob("argv-*")), ["argv-b", "argv-bad", "argv-c"])
        # in the form of the other options; an item named runs whatever the diff touches
        self.forget()
        self.run_main(["--only", "fz,st", "--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz")[:2], ["--changed-since", "auto"])
        self.assertTrue(self.ran("st"))
        self.forget()
        self.run_main(["--only", "fz"], steps)
        self.assertEqual(self.argv_of("fz"), [""])
        for argv in (["--only", "sv"], ["--only", "nope"], ["--only", ""], ["--only", "a", "--quick"]):
            with self.subTest(argv=argv):
                self.forget()
                self.assertEqual(self.run_main(argv, steps)[0], 2)
                self.assertEqual(list(self.root.glob("argv-*")), [])

    def test_the_sweep(self):
        steps = [fake("sv", sweep=True, sweep_only=True), fake("plain"), fake("b", static=True),
                 fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",), sweep=True)]  # fmt: skip
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        code, out = self.run_main(["--sweep"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate (sweep 0/2): PASS"))
        self.assertEqual(sorted(p.name for p in self.root.glob("argv-*")), ["argv-b", "argv-fz", "argv-st", "argv-sv"])
        self.assertLess(out.index("=== sv"), out.index("=== b"))
        self.assertEqual(self.argv_of("fz"), ["--shard", "0/2"])
        self.assertNotIn("plain", out)
        self.assertIn(f"sweep: next 1/2 (0/2 last at {head[:7]}, 0 commits ago; 1/2 never)", out)
        self.assertEqual(self.history()[-1]["form"], "sweep 0/2")
        self.run_main(["--sweep"], steps)
        self.assertEqual(self.argv_of("fz"), ["--shard", "1/2"])
        git_in(self.root, "commit", "-q", "--allow-empty", "-m", "next")
        with open(self.root / gate_runs.HISTORY, "a") as f:
            f.write("not json\n")
        code, out = self.run_main(["--sweep"], [fake("fz", 1, narrows=("tools/fuzz.py",))])
        self.assertEqual((code, out.splitlines()[-1]), (1, "gate (sweep 0/2): FAIL (fz)"))
        self.assertIn(f"sweep: next 1/2 (0/2 last at", out)
        self.assertIn(f"1/2 last at {head[:7]}, 1 commit ago); 1 unreadable line", out)
        self.run_main(["--sweep"], steps)  # a failed sweep counts: the next shard
        self.assertEqual(self.argv_of("fz"), ["--shard", "1/2"])
        # another K starts again
        with mock.patch.object(gate_steps, "SHARDS", 3):
            self.run_main(["--sweep"], steps)
            self.assertEqual(self.argv_of("fz"), ["--shard", "0/3"])
        # alone, and in the main tree only
        for argv in (["--sweep", "--work", "W3-07"], ["--sweep", "--quick"], ["--sweep", "--only", "b"]):
            self.assertEqual(self.run_main(argv, steps)[0], 2)
        wt = self.worktree()
        out = io.StringIO()
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=wt, out=out), 2)
        self.assertIn("a worktree", err.getvalue())
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=self.root / "tests", out=out), 2)
        self.assertIn("not a git work tree", err.getvalue())

    def test_the_history(self):
        steps = [fake("a"), fake("p", gate_steps.PARENT, parent=True)]
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        for argv, form in ((["--work", "W3-07"], "work W3-07"), ([], "whole"), (["--stage-end", "W3"], "stage-end W3"),
                           (["--only", "a"], "only a"), (["--quick"], None), (["--work", "W9-99"], None)):  # fmt: skip
            with self.subTest(argv=argv):
                before = len(self.history())
                self.run_main(argv, steps)
                rows = self.history()
                if form is None:
                    self.assertEqual(len(rows), before)
                    continue
                self.assertEqual(len(rows), before + 1)
                row = rows[-1]
                self.assertEqual((row["form"], row["commit"], row["dirty"], row["verdict"]), (form, head, False, "PASS"))
                self.assertEqual(row["items"]["a"][0], "PASS")
                self.assertEqual(row["works"], ["W3-07"] if "--work" in argv else [])
        self.assertEqual(self.history()[0]["items"]["p"][0], "PARENT")
        self.repo.write("crates/x.rs", "x\n")  # untracked: dirty
        self.run_main([], steps)
        self.assertTrue(self.history()[-1]["dirty"])
        # a worktree keeps none
        wt = self.worktree()
        before = len(self.history())
        quiet(gate.main, [], steps=steps, root=wt, out=io.StringIO())
        self.assertEqual(len(self.history()), before)
        self.assertFalse((wt / gate_runs.HISTORY).exists())
        # a history that cannot be written does not fail the gate
        (self.root / gate_runs.HISTORY).unlink()
        (self.root / gate_runs.HISTORY).mkdir()
        code, out = self.run_main([], steps)
        self.assertEqual(code, 0)
        self.assertIn("  history: cannot write it (", out)
        self.assertIn("  history: cannot read it (", out)
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=self.root, out=io.StringIO()), 2)
        self.assertIn("cannot read the history", err.getvalue())

    def test_the_warning_of_the_time(self):
        steps = [sleeper("s3", 0.3), sleeper("s2", 0.2), sleeper("s1", 0.1), fake("s0")]
        with mock.patch.object(gate_steps, "BUDGET_WORK", 0.4):
            code, out = self.run_main(["--work", "W3-07"], steps)
            lines = out.splitlines()
            self.assertEqual((code, lines[-1]), (0, "gate: PASS"))
            self.assertRegex(lines[-2], r"^warning: the work check took \d+s, \d+s over its 0.4s; "
                                        r"the longest: s3 0\.\ds, s2 0\.\ds, s1 0\.\ds$")  # fmt: skip
            for argv in ([], ["--only", "s3,s2,s1", "--work", "W3-07"]):
                self.assertNotIn("warning", self.run_main(argv, steps)[1])
        with mock.patch.object(gate_steps, "BUDGET_SWEEP", 0):
            out = self.run_main(["--sweep"], [fake("b", static=True)])[1]
            self.assertTrue(out.splitlines()[-2].startswith("warning: the sweep took"))
        # the wait for the lock does not count
        with mock.patch.object(gate_steps, "BUDGET_WORK", 0.5), open(gate.lock_path(self.root), "a+") as held:
            gate.fcntl.flock(held, gate.fcntl.LOCK_EX)
            out = io.StringIO()
            other = threading.Thread(target=lambda: gate.main(["--work", "W3-07"], steps=[fake("a")], root=self.root,
                                                              out=out))  # fmt: skip
            other.start()
            time.sleep(1.0)
            gate.fcntl.flock(held, gate.fcntl.LOCK_UN)
            other.join(10)
        self.assertIn("waited", out.getvalue())
        self.assertNotIn("warning", out.getvalue())

    def test_parent(self):
        results = gate.run_steps([fake("gm", gate_steps.PARENT, parent=True), fake("x", gate_steps.PARENT)], {},
                                 cwd=self.root, out=io.StringIO())  # fmt: skip
        self.assertEqual([r.status for r in results], ["PARENT", "FAIL"])
        self.assertIn("waits for the parent", results[0].describe())
        code, out = self.run_main([], [fake("gm", gate_steps.PARENT, parent=True)])
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate: PASS"))
        self.assertIn("PARENT  gm", out)

    def test_gap_marks_in_the_three_trees(self):
        def run(root):
            out = io.StringIO()
            with mock.patch.object(sys, "stdout", out):
                return gap_marks.main(["--root", str(root)]), out.getvalue()

        wt = self.worktree()
        for text, main_code, wt_code in (("// SPEC-GAP(S-45): x\n", 0, 0), ("// SPEC-GAP(NEW): x\n", 1, gate_steps.PARENT),
                                         ("// SPEC-GAP(S-99): x\n", 1, gate_steps.PARENT),
                                         ("// SPEC-GAP(NEW): x\n// SPEC-GAP: y\n", 1, 1),
                                         ("// SPEC-GAP(Q-10): x\n", 1, 1)):  # fmt: skip
            with self.subTest(text=text):
                for root in (self.root, wt):
                    (root / "crates/a/src").mkdir(parents=True, exist_ok=True)
                    (root / "crates/a/src/lib.rs").write_text(text)
                code, out = run(self.root)
                self.assertEqual(code, main_code, out)
                self.assertNotIn("parent:", out)
                code, out = run(wt)
                self.assertEqual(code, wt_code, out)
                if wt_code == gate_steps.PARENT:
                    self.assertIn("parent: crates/a/src/lib.rs:1:", out)
                    self.assertIn("1 for the parent to register", out)
        # not a git root (the made-up roots): fails as in the main tree
        plain = Repo(self.elsewhere())
        plain.write("crates/a/src/lib.rs", "// SPEC-GAP(NEW): x\n")
        self.assertEqual(run(plain.root)[0], 1)


class SaveBase(unittest.TestCase):
    """`tools/gate.sh --save-base` (X-1 U2, M-3): the binaries of HEAD for `narrowing.resolve_base`."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve() / "main"
        self.target = Path(self.tmp.name).resolve() / "cargo-target"
        for rel, text in {".gitignore": "target/\n", "crates/c.rs": "fn c() {}\n", "docs/d.md": "d\n",
                          "Cargo.toml": "[workspace]\n"}.items():  # fmt: skip
            self.write(rel, text)
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        self.built = []

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def build(self, root, cases=False):
        self.built.append(cases)
        name = "onsa_cases" if cases else "onsa"
        (self.target / "debug").mkdir(parents=True, exist_ok=True)
        (self.target / "debug" / name).write_text(f"#!/bin/sh\necho {name} {len(self.built)}\n")
        (self.target / "debug" / name).chmod(0o755)
        return True

    def save(self, root=None, keep=2, build=None):
        lines = []
        code = gate_runs.save_base(root or self.root, keep, out=lines.append, build=build or self.build,
                                   target_directory=lambda r: self.target)  # fmt: skip
        return code, "\n".join(lines)

    def head(self):
        return git_in(self.root, "rev-parse", "HEAD").strip()

    def test_warns_of_a_big_debug_directory(self):
        (self.target / "debug" / "deps").mkdir(parents=True)
        (self.target / "debug" / "deps" / "x.o").write_bytes(b"\0" * 65536)
        self.assertIsNone(gate_runs.debug_dir_warning(self.target, 2**30))
        warning = gate_runs.debug_dir_warning(self.target, 1024)
        self.assertTrue(warning.startswith("warning: ") and "cargo clean --profile dev" in warning, warning)
        lines = []
        code = gate_runs.save_base(self.root, 2, out=lines.append, build=self.build,
                                   target_directory=lambda r: self.target, debug_limit=1024)  # fmt: skip
        self.assertEqual((code, lines[-1]), (0, gate_runs.debug_dir_warning(self.target, 1024)))
        self.assertTrue(lines[-2].startswith("save-base: "), lines)
        self.assertNotIn("warning", self.save()[1])  # no limit given, no warning

    def test_saves_what_the_reader_finds(self):
        code, out = self.save()
        self.assertEqual(code, 0, out)
        self.assertEqual(self.built, [False, True])
        d = self.root / "target" / "base" / self.head()[:7]
        self.assertEqual((d / "COMMIT").read_text(), self.head() + "\n")
        # the base of HEAD itself tells nothing apart (it would show the new classes too)
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))
        saved = narrowing.Base(self.head()[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),))
        self.write("crates/c.rs", "fn c() { 1 }\n")  # a change of the code: the base of HEAD differs
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), saved)
        self.write("crates/c.rs", "fn c() {}\n")
        self.write("docs/d.md", "changed\n")  # not the code
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))
        git_in(self.root, "commit", "-qam", "next")  # a work on top of dev
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), saved)
        git_in(self.root, "reset", "-q", "--hard", "HEAD~1")
        self.assertEqual(sorted(p.name for p in (self.root / "target" / "base").iterdir()), [self.head()[:7]])
        # again on the same commit: replaced
        self.assertEqual(self.save()[0], 0)
        self.assertIn("onsa 3", (d / "onsa").read_text())

    def test_refuses_changes_of_what_builds_them(self):
        for rel in ("crates/c.rs", "Cargo.toml"):
            with self.subTest(rel=rel):
                self.write(rel, "changed\n")
                code, out = self.save()
                self.assertEqual(code, 1)
                self.assertIn(f"refused: the tracked files have changes not committed: {rel}", out)
                git_in(self.root, "checkout", "--", rel)
        self.assertFalse((self.root / "target" / "base").exists())
        self.assertEqual(self.built, [])
        # untracked files and the documents do not refuse
        self.write("crates/new.rs", "x\n")
        self.write("docs/d.md", "changed\n")
        self.assertEqual(self.save()[0], 0)

    def test_keeps_the_last(self):
        base = self.root / "target" / "base"
        (base / "notes").mkdir(parents=True)
        (base / "abcdef0").mkdir()  # no COMMIT: not a saved base
        saved = []
        for i in range(3):
            git_in(self.root, "commit", "-q", "--allow-empty", "-m", f"c{i}")
            self.assertEqual(self.save(keep=2)[0], 0)
            saved.append(self.head()[:7])
            os.utime(base / saved[-1] / "COMMIT", (1000 + i, 1000 + i))
        self.assertEqual(self.save(keep=2)[0], 0)  # the newest again: keeps its place
        self.assertEqual(sorted(p.name for p in base.iterdir()), sorted(["notes", "abcdef0"] + saved[1:]))

    def test_main_tree_only_and_failures(self):
        wt = Path(self.tmp.name).resolve() / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        self.assertEqual(self.save(wt)[0], 2)
        self.assertEqual(self.save(Path(self.tmp.name))[0], 2)
        self.assertEqual(self.save(build=lambda root, cases=False: False)[0], 1)
        self.assertEqual(self.built, [])
        self.assertFalse((self.root / "target" / "base").exists() and any((self.root / "target" / "base").iterdir()))
        # alone
        with mock.patch.object(sys, "stderr", io.StringIO()):
            self.assertEqual(gate.main(["--save-base", "--work", "W3-07"], root=self.root, out=io.StringIO()), 2)


class RealSteps(unittest.TestCase):
    _c_items = None

    @classmethod
    def c_items(cls):
        """The items of the C checks, from their table (`onsa_cases --c-items`, onsa_tests::c::ITEMS)."""
        if cls._c_items is None:
            cls._c_items = repo.cases_json(repo.ROOT, repo.CASES_CMD, "--c-items")
        return cls._c_items

    def test_c_items_match_the_table(self):
        # one step per row of onsa_tests::c::ITEMS, in its order, named as the row (W1-06)
        prefix = gate_steps.C_CHECK
        steps = [s for s in gate_steps.STEPS if s.argv[: len(prefix)] == prefix]
        self.assertEqual([s.argv[len(prefix) :] for s in steps], [(n,) for n in self.c_items()])
        self.assertEqual([s.name for s in steps], self.c_items())
        self.assertTrue(all(s.pendable and not s.info for s in steps))

    def test_required_items(self):
        names = [s.name for s in gate_steps.STEPS]
        self.assertEqual(len(names), len(set(names)))
        required = (
            "fmt", "clippy", "test", "spec-examples", "spec-sections", "pending", "gate-selftest", "golden",
            "diag-registry", "diag-negatives", "gap-marks", "builtin-names", "ignored-files", "fuzz",
            "fmt-props", "vectors", "ignores", "default-inits", "docs", "docs-fmt",
        )  # fmt: skip
        for r in required + ("spec-coverage",):
            self.assertIn(r, names)
        by_name = {s.name: s for s in gate_steps.STEPS}
        self.assertTrue(by_name["golden"].info)
        self.assertTrue(by_name["spec-coverage"].info)
        # the convergence of the fix candidates shows its cycles and divergences, never listed (W3-22)
        self.assertTrue(by_name["fix-loop"].info and not by_name["fix-loop"].pendable)
        self.assertFalse(by_name["spec-sections"].info)
        # the documents (X-2 DT-5): the checks fail the gate; the lines `fmt` would break are only shown (DT-4, DF-8)
        self.assertTrue(by_name["docs"].static and not by_name["docs"].info)
        self.assertEqual(by_name["docs"].argv[-2:], (str(gate_steps.TOOLS / "docs.py"), "check"))
        self.assertTrue(by_name["docs-fmt"].info and by_name["docs-fmt"].static and not by_name["docs-fmt"].pendable)
        self.assertEqual(by_name["docs-fmt"].argv[-3:], (str(gate_steps.TOOLS / "docs.py"), "fmt", "--list"))
        self.assertTrue(by_name["pending"].stage_args and by_name["pending"].gate_steps)
        # the ignores of the Rust tests: light, so also in `--quick`, and failing at a stage end like the list (R-224)
        self.assertTrue(by_name["ignores"].stage_args and not by_name["ignores"].pendable)
        self.assertFalse(by_name["fmt-props"].pendable)
        # `--quick` leaves out the fuzzing, the self-test, the C and the fmt properties (2026-10-08)
        slow = ["save-base", "fuzz", "fuzz-deep", "fix-loop", "gate-selftest"] + self.c_items() + ["vectors-c", "fmt-props", "fmt-comments", "fmt-cst"]
        self.assertEqual([s.name for s in gate_steps.STEPS if s.slow], slow)
        # the deep fuzzing runs only at a stage end (W3-03)
        self.assertEqual([s.name for s in gate_steps.STEPS if s.stage_end_only], ["fuzz-deep"])
        # the only items that may be listed: the test vectors against the interpreter and the C
        # (W2-02, by case only), the C checks (W1-06), and the fmt property that waits for W3-11 (R-70)
        self.assertEqual(
            gate_steps.pendable(), ["vectors-interp", "keywords"] + self.c_items() + ["vectors-c", "fmt-comments"]
        )
        vectors = [s for s in gate_steps.STEPS if s.argv[: len(gate_steps.VECTORS)] == gate_steps.VECTORS]
        self.assertEqual([(s.name, s.argv[len(gate_steps.VECTORS) :]) for s in vectors],
                         [("vectors-interp", ("interp",)), ("vectors-c", ("c",))])  # fmt: skip
        self.assertTrue(all(s.by_case_only for s in vectors))
        for n in names:
            self.assertRegex(n, pending.TARGET_FORMS["gate"])
            self.assertNotIn("/", n)

    def test_the_forms_of_the_items(self):
        # X-1 U2: the attributes behind the work check, the sweep and `--only`
        steps = gate_steps.STEPS
        self.assertEqual(sorted(gate_steps.static_names()), sorted(
            ["pending", "ignores", "gap-marks", "diag-registry", "diag-negatives", "builtin-names", "spec-examples",
             "spec-sections", "default-inits", "docs", "docs-fmt"]))  # fmt: skip
        self.assertEqual({s.name: s.narrows for s in steps if s.narrows},
                         {"fuzz": ("tools/fuzz.py", "tools/narrowing.py"),
                          **{n: ("tools/fmt_props.py", "tools/narrowing.py") for n in ("fmt-props", "fmt-comments", "fmt-cst")}})  # fmt: skip
        for s in steps:
            for p in s.narrows:
                self.assertTrue((gate.ROOT / p).is_file(), p)
        self.assertEqual({s.name: s.touches for s in steps if s.touches}, {"gate-selftest": ("tools/",)})
        self.assertEqual([s.name for s in steps if s.parent], ["gap-marks"])
        sweep = [s.name for s in steps if gate._in_form(s, gate.Form(sweep=(0, 2)), None)]
        self.assertEqual(sweep[0], "save-base")
        self.assertEqual(sorted(sweep), sorted(["save-base", "gate-selftest", "fuzz", "fmt-props", "fmt-comments",
                                                "fmt-cst"] + gate_steps.static_names()))  # fmt: skip
        for form in (gate.Form(), gate.Form(works=("W3-07",)), gate.Form(stage_end="W3"), gate.Form(quick=True)):
            self.assertEqual([s.name for s in steps if not gate._in_form(s, form, None)], ["save-base"])
        # the narrowed runs keep the cap of the tools: the gate holds no copy of it
        self.assertFalse(hasattr(gate_steps, "CODE_CAP"))
        self.assertEqual(gate_steps.PARENT, 3)


class SpecSections(unittest.TestCase):
    SPEC = "# 1. A\n## 1.1 B\n```onsa\n## 9.9 not a heading\n```\n### 1.1.2 C\n## 1.2 D\n# 2. E\n"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / spec_sections.SPEC).write_text(self.SPEC, encoding="utf-8")

    def tearDown(self):
        self.tmp.cleanup()

    def cases(self, *specs):
        return [{"path": f"tests/{i}.onsa", "spec": list(s)} for i, s in enumerate(specs)]

    def test_headings_skip_fences(self):
        self.assertEqual(spec_blocks.headings(self.SPEC), ["1", "1.1", "1.1.2", "1.2", "2"])

    def test_unknown_and_untested(self):
        heads = spec_blocks.headings(self.SPEC)
        cases = self.cases(["§1.1.2"], ["§9.9", "§2"])
        self.assertEqual(spec_sections.unknown(cases, heads), [("tests/1.onsa", "§9.9")])
        # a section is tested through a subsection
        self.assertEqual(spec_sections.untested(cases, heads), ["1.2"])
        # a case that does not run tests nothing, but its names are still checked
        cases = [{"path": "tests/n.onsa", "mode": "none", "spec": ["§1.2", "§9.9"]}]
        self.assertEqual(spec_sections.untested(cases, heads), heads)
        self.assertEqual(spec_sections.unknown(cases, heads), [("tests/n.onsa", "§9.9")])

    def test_sections_in_the_strings_of_the_compiler(self):
        heads = spec_blocks.headings(self.SPEC)
        src = 'let m = "a rule (§1.1, §9.9)";\n// §8.8 is a comment, not a message\nlet n = "§2";\n'
        self.assertEqual(spec_sections.unknown_refs([("a.rs", src)], heads), [("a.rs:1", "9.9")])
        (self.root / "crates" / "c" / "src").mkdir(parents=True)
        (self.root / "crates" / "c" / "src" / "lib.rs").write_text(
            'fn f() { g("§7.7") }\n#[cfg(test)]\nmod tests { const X: &str = "§6.6"; }\n', encoding="utf-8")
        (self.root / "crates" / "c" / "src" / "x_tests.rs").write_text('const Y: &str = "§5.5";\n', encoding="utf-8")
        found = spec_sections.unknown_refs(spec_sections.compiler_sources(self.root), heads)
        self.assertEqual(found, [("crates/c/src/lib.rs:1", "7.7")], "unit tests are not messages")
        # A `#[cfg(test)] mod x;` declaration early in the file cuts nothing; a
        # string that goes on over lines is read whole; a char `'"'` and a `}`
        # in a string of a test module do not throw the reading off.
        (self.root / "crates" / "c" / "src" / "lib.rs").write_text(
            "#[cfg(test)]\nmod x_tests;\n"
            "fn f() -> char { '\"' }\n"
            'fn g() { h("a long message \\\n    that names §4.4.4 here") }\n'
            '#[cfg(test)]\nmod tests {\n    const Z: &str = "} §3.3.3";\n}\n'
            'fn k() { h(r#"raw §2.2.2"#) }\n',
            encoding="utf-8",
        )
        found = spec_sections.unknown_refs(spec_sections.compiler_sources(self.root), heads)
        self.assertEqual(found, [("crates/c/src/lib.rs:5", "4.4.4"), ("crates/c/src/lib.rs:10", "2.2.2")])

    def run_main(self, flag, cases):
        script = f"import json; print(json.dumps({cases!r}))"
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = spec_sections.main([flag], root=self.root, cmd=(sys.executable, "-B", "-c", script))
        return code, out.getvalue()

    def test_check_fails_on_unknown_sections_only(self):
        code, out = self.run_main("--check", self.cases(["§1.2"]))
        self.assertEqual(code, 0, out)
        code, out = self.run_main("--check", self.cases(["§3"]))
        self.assertEqual(code, 1)
        self.assertIn("names §3", out)

    def test_list_never_fails_on_untested(self):
        code, out = self.run_main("--list", self.cases([]))
        self.assertEqual(code, 0)
        self.assertIn("0 of 5 sections have a case", out)

    def test_a_failing_lister_fails(self):
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = spec_sections.main(["--list"], root=self.root, cmd=(sys.executable, "-B", "-c", "raise SystemExit(1)"))
        self.assertEqual(code, 1)
        self.assertIn("cannot list the cases", out.getvalue())


class Golden(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def write(self, rel, text="x\n"):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def test_changes(self):
        self.git("init", "-q")
        for rel in ("tests/golden/c/a.c", "tests/golden/c/b.h", "tests/golden/core/m.core", "tests/golden/core/m.onsa", "src/x.rs"):
            self.write(rel)
        self.git("add", ".")
        self.git(
            "-c", "commit.gpgsign=false", "-c", "user.name=t", "-c", "user.email=t@t",
            "commit", "--no-verify", "-q", "-m", "init",
        )  # fmt: skip
        self.write("tests/golden/c/a.c", "changed\n")
        (self.root / "tests/golden/c/b.h").unlink()
        self.write("tests/golden/graph/new.dot")
        self.write("tests/golden/core/m.onsa", "an input changed\n")
        self.write("tests/golden/core/n.core")
        self.git("add", "tests/golden/core/n.core")  # staged counts too
        self.write("tests/golden/c/é.c")  # not quoted
        self.write("src/x.rs", "outside tests/golden\n")
        self.assertEqual(
            gate.golden_changes(self.root),
            [
                "M tests/golden/c/a.c",
                "D tests/golden/c/b.h",
                "? tests/golden/c/é.c",
                "M tests/golden/core/m.onsa",
                "A tests/golden/core/n.core",
                "? tests/golden/graph/new.dot",
            ],
        )

    def test_not_a_repository(self):
        with self.assertRaises(subprocess.CalledProcessError):
            gate.golden_changes(self.root)
        self.assertEqual(quiet(gate.golden_main, self.root), 1)


def json_cmd(outputs):
    """A stand-in for `onsa_cases`: prints `outputs[<first argument>]` as JSON."""
    script = "import json, sys; o = json.loads(sys.argv[1]); print(json.dumps(o[sys.argv[2]]))"
    return (sys.executable, "-B", "-c", script, json.dumps(outputs))


def run(path, mode="check", markers=()):
    """A case of `onsa_cases --run`; markers are (file, line, code, matched, target)."""
    return {
        "path": path,
        "mode": mode,
        "ran": mode != "none",
        "markers": [
            {"code": c, "file": f, "line": ln, "stage": "build" if t else "check", "target": t, "matched": ok}
            for f, ln, c, ok, t in markers
        ],
        "problems": [],
    }


class DiagRegistry(TempRepo):
    def test_spec_codes(self):
        text = "E0001 は（E0002）、コードはE0003。E00xx、E00123、XE0004、`E0005`"
        self.assertEqual(diag_codes.spec_codes(text), {"E0001", "E0002", "E0003", "E0005"})
        for r in (
            "E0410〜E0416", "E0410 ~ E0416", "E0410-E0416", "E0410〜0416", "E0410..E0416", "E0410...E0416",
            "E0410 … E0416", "E0410--E0416", "E0410 to E0416", "E0410 から E0416",
        ):  # fmt: skip
            with self.subTest(r=r):
                with self.assertRaisesRegex(diag_codes.CheckError, "range"):
                    diag_codes.spec_codes(f"型の誤りは {r}。")
        # a list is not a range
        for ok in ("E0410 / E0416", "E0410、E0416", "E0410 total E0416", "E0410, E0416"):
            self.assertEqual(diag_codes.spec_codes(ok), {"E0410", "E0416"}, ok)

    def test_phase2_codes(self):
        # the rows whose last cell is 第 2 期, with the ranges expanded; not the M3 row
        self.assertEqual(repo.phase2_codes(PLAN), {"E0612", "E0613", "E0614", "E0620", "E0904", "E0905"})
        with self.assertRaisesRegex(repo.RepoError, "no row"):
            repo.phase2_codes(PLAN.replace("| 第 2 期 |", "| M4 |"))
        with self.assertRaisesRegex(repo.RepoError, "goes down"):
            repo.phase2_codes(PLAN.replace("E0612〜E0614", "E0614〜E0612"))

    def test_retired_codes(self):
        # codes in parentheses and after the first sentence are not retired
        self.assertEqual(repo.retired_codes(PLAN), {"E0611", "E0814"})
        for bad, needle in (
            (PLAN.replace("欠番: ", "欠番は "), "found 0"),
            (PLAN.replace("## 6.", "欠番: E0313。\n## 6."), "found 2"),
            (PLAN.replace("欠番: E0611（S-77 で E0601 にまとめた）、E0814（S-147 で E0815 にまとめた）", "欠番: なし"), "names no code"),
            (PLAN.replace("## 5.", "## 5x"), "## 5."),
        ):
            with self.subTest(needle=needle):
                with self.assertRaisesRegex(diag_codes.CheckError, re.escape(needle)):
                    repo.retired_codes(bad)

    def test_check_registry(self):
        spec, retired = {"E0001", "E0002", "E0814"}, {"E0814", "E0611"}
        self.assertEqual(diag_codes.check_registry({"E0001", "E0002"}, spec, retired), [])
        problems = diag_codes.check_registry({"E0001", "E0814", "E0999"}, spec, retired)
        self.assertEqual(len(problems), 3, problems)
        self.assertIn("E0002: the spec names it", problems[0])
        self.assertIn("E0814: a retired code", problems[1])
        self.assertIn("E0999: in the registry, but the spec does not name it", problems[2])

    def run_main(self, flag, outputs):
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main([flag], root=self.repo.root, cmd=json_cmd(outputs))
        return code, out.getvalue()

    def test_main(self):
        self.repo.write(str(repo.SPEC), "E0001 と E0002。E0611 は欠番。")
        codes = [{"code": "E0001"}, {"code": "E0002"}]
        code, out = self.run_main("--registry", {"--codes": codes})
        self.assertEqual(code, 0, out)
        self.assertIn("2 codes in the registry", out)
        code, out = self.run_main("--registry", {"--codes": codes[:1]})
        self.assertEqual(code, 1, out)
        self.assertIn("E0002: the spec names it", out)
        # a failing lister fails the check
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--registry"], root=self.repo.root, cmd=(sys.executable, "-B", "-c", "raise SystemExit(3)"))
        self.assertEqual(code, 1)
        self.assertIn("cannot check", out.getvalue())


class DiagNegatives(TempRepo):
    def test_count(self):
        runs = {
            "cases": [
                # a marker compared once per target counts once; one not matched does not count
                run("tests/a/m.onsa", markers=[("m.onsa", 3, "E0809", True, "a"), ("m.onsa", 3, "E0809", True, "b"),
                                               ("m.onsa", 4, "E0809", False, "a")]),
                # the same file name in another case is another example
                run("tests/b/m.onsa", markers=[("m.onsa", 3, "E0809", True, None)]),
                run("tests/c.onsa", markers=[("tests/c.onsa", 1, "E0302", True, None), ("tests/c.onsa", 2, "E0302", True, None)]),
                # not counted: mode none, a case pending as a whole
                run("tests/none.onsa", mode="none", markers=[("tests/none.onsa", 1, "E0302", True, None)]),
                run("tests/whole.onsa", markers=[("tests/whole.onsa", 1, "E0302", True, None)]),
                # counted: a case with one test pending
                run("tests/one.onsa", mode="test", markers=[("tests/one.onsa", 1, "E0401", True, None)]),
            ],
            "errors": [],
        }
        listed = entry("test-case", "tests/whole.onsa", until="W3-07") + entry("test-case", "tests/one.onsa::t", until="W3-07")
        self.repo.write("tests/whole.onsa", "")
        self.repo.write("tests/one.onsa", "")
        self.repo.write("tests/pending.toml", listed)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        counts = diag_codes.count_negatives(runs, entries)
        self.assertEqual(counts, {"E0809": 2, "E0302": 2, "E0401": 1})

    def test_check(self):
        registry = {"E0001", "E0002", "E0003"}
        counts = {"E0001": 3, "E0002": 2, "E0003": 0}
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002") + entry("diag-code", "E0003"))
        entries, _ = pending.load(self.repo.pending)
        self.assertEqual(diag_codes.check_negatives(counts, registry, entries, set()), [])
        # fewer than 3 and not listed
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, set())
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("E0003: 0 negative example(s), fewer than 3, and not listed", problems[0])
        # listed but reached 3; listed but not a code
        text = entry("diag-code", "E0001") + entry("diag-code", "E0002") + entry("diag-code", "E0003") + entry("diag-code", "E0998")
        self.repo.write("tests/pending.toml", text)
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives({**counts, "E0997": 1}, registry, entries, set())
        self.assertEqual(len(problems), 3, problems)
        self.assertIn("E0001: 3 negative examples, but pending[0]", problems[0])
        self.assertIn("remove the entry", problems[0])
        self.assertIn('"E0998": not a code of the registry', problems[1])
        self.assertIn("E0997: markers name it", problems[2])

    def test_phase2(self):
        # M1: P2 only for the codes of the second phase (plan §5), and those listed have P2
        registry, counts, phase2 = {"E0001", "E0612"}, {}, {"E0612"}
        ok = entry("diag-code", "E0001", until="W3-07") + entry("diag-code", "E0612", until="P2")
        self.repo.write("tests/pending.toml", ok)
        entries, _ = pending.load(self.repo.pending)
        self.assertEqual(diag_codes.check_negatives(counts, registry, entries, phase2), [])
        # a code of the first phase put off to P2
        self.repo.write("tests/pending.toml", entry("diag-code", "E0001", until="P2") + entry("diag-code", "E0612", until="P2"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, phase2)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"E0001": until "P2", but the plan §5 does not put it in the second phase', problems[0])
        # a code of the second phase given a work of the first
        self.repo.write("tests/pending.toml", entry("diag-code", "E0001", until="W3-07") + entry("diag-code", "E0612", until="W3-07"))
        entries, _ = pending.load(self.repo.pending)
        problems = diag_codes.check_negatives(counts, registry, entries, phase2)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn('"E0612": a code of the second phase (plan §5), so its until is "P2", not W3-07', problems[0])

    def test_threshold_is_three(self):
        self.assertEqual(diag_codes.NEGATIVE_MIN, 3)

    def test_main(self):
        runs = {"cases": [run("tests/c.onsa", markers=[("tests/c.onsa", i, "E0001", True, None) for i in (1, 2, 3)])], "errors": []}
        outputs = {"--codes": [{"code": "E0001"}, {"code": "E0002"}], "--run": runs}  # plan §5: E0612... are P2
        self.repo.write("tests/pending.toml", entry("diag-code", "E0002"))
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--negatives"], root=self.repo.root, cmd=json_cmd(outputs))
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn("(6 of the second phase)", out.getvalue())
        self.assertIn("1 fewer: E0002 0", out.getvalue())
        # an error of the scan fails
        outputs["--run"] = {**runs, "errors": ["tests/locked: cannot read the directory"]}
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = diag_codes.main(["--negatives"], root=self.repo.root, cmd=json_cmd(outputs))
        self.assertEqual(code, 1)
        self.assertIn("cannot scan the cases", out.getvalue())


class SpecGap(TempRepo):
    def marks(self, files):
        for rel, text in files.items():
            self.repo.write(rel, text)
        marks = gap_marks.find_marks(self.repo.root)
        known = pending.load_docs(self.repo.root).reasons | gap_marks.api_ids(self.repo.root)
        problems, for_parent = gap_marks.check(marks, known)
        return marks, problems + for_parent

    def test_registered_marks_pass(self):
        marks, problems = self.marks(
            {
                "crates/a/src/lib.rs": "fn f() {} // SPEC-GAP(S-45): the order is not given\n    // SPEC-GAP(R-23): x\n",
                "std/x.onsa": "// SPEC-GAP(A-01): y\n",
                "runtime/c/onsa.h": "/* c */ // SPEC-GAP(S-34): z\n",
                "tools/t.py": "x = 1  # SPEC-GAP(R-23): w\n",
            }
        )
        self.assertEqual(len(marks), 5)
        self.assertEqual(problems, [])

    def test_bad_marks_fail(self):
        cases = {
            "// SPEC-GAP: no id": "malformed",
            "// SPEC-GAP(): empty": "malformed",
            "// SPEC-GAP(S-45) missing colon": "malformed",
            "// spec-gap(S-45): lower case": "malformed",
            "// SPECGAP(S-45): no hyphen": "malformed",
            "// SPEC GAP(S-45): a space": "malformed",
            "// Spec_Gap(S-45): mixed": "malformed",
            "// a spec gap, mentioned in prose": "malformed",
            "// SPEC-GAP(S-45): a note on a specgap": "malformed",
            "// SPEC-GAP(S-45):": "malformed",
            "//SPEC-GAP(S-45): no space": "malformed",
            "/// SPEC-GAP(S-45): a doc comment": "malformed",
            "// SPEC-GAP(S-45): one // SPEC-GAP(R-23): two": "malformed",
            "let s = \"SPEC-GAP\";": "malformed",
            "// SPEC-GAP(NEW): to register": "the parent registers",
            "// SPEC-GAP(Q-10): not S / R / A": "not an S / R / A number",
            "// SPEC-GAP(S-99): outside §2": "not in the tables",
            "// SPEC-GAP(A-02): no such row": "not in the tables",
        }
        for line, needle in cases.items():
            with self.subTest(line=line):
                _, problems = self.marks({"crates/a/src/lib.rs": f"fn f() {{}}\n{line}\n"})
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(needle, problems[0])
                self.assertIn("crates/a/src/lib.rs:2", problems[0])

    def test_spelling_hint(self):
        # N3: a line that only mentions a spelling of the token is told how to avoid it
        _, problems = self.marks({"crates/a/src/lib.rs": "// see spec_gap below\n"})
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("if this is not a mark, avoid spellings like `spec_gap`", problems[0])

    def test_comment_leader_follows_the_file(self):
        _, problems = self.marks({"tools/t.py": "# SPEC-GAP(S-45): ok\n// SPEC-GAP(S-45): not a Python comment\n"})
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("tools/t.py:2", problems[0])

    def test_skipped(self):
        marks, _ = self.marks(
            {
                # build outputs: `target/` next to a Cargo.toml or an onsa.toml
                "crates/a/Cargo.toml": "[package]\n",
                "crates/a/target/x.rs": "// SPEC-GAP(NEW): build output\n",
                "std/pkg/onsa.toml": "[package]\n",
                "std/pkg/target/host/x.c": "// SPEC-GAP(NEW): build output\n",
                "docs/x.md": "// SPEC-GAP(NEW): not scanned\n",
                "tools/gap_marks.py": "TOKEN = 'SPEC-GAP'\n",
            }
        )
        self.assertEqual(marks, [])
        (self.repo.root / "crates/a/b.bin").write_bytes(b"\xff\xfe SPEC-GAP")  # not text
        self.assertEqual(gap_marks.find_marks(self.repo.root), [])
        # M3: a `target` elsewhere is an ordinary directory and is scanned
        marks, problems = self.marks(
            {
                "crates/a/src/target/x.rs": "// SPEC-GAP(NEW): a module named target\n",
                "tools/target/y.py": "# SPEC-GAP(S-45): ok\n",
            }
        )
        self.assertEqual([m[0] for m in marks], ["crates/a/src/target/x.rs", "tools/target/y.py"])
        self.assertEqual(len(problems), 1, problems)

    def test_main(self):
        self.repo.write("crates/a/src/lib.rs", "// SPEC-GAP(S-45): x\n")
        self.assertEqual(quiet(gap_marks.main, ["--root", str(self.repo.root)]), 0)
        self.repo.write("crates/a/src/lib.rs", "// SPEC-GAP(NEW): x\n")
        self.assertEqual(quiet(gap_marks.main, ["--root", str(self.repo.root)]), 1)
        (self.repo.root / "docs/api-candidates.md").unlink()
        self.assertEqual(quiet(gap_marks.main, ["--root", str(self.repo.root)]), 1)


BUILTIN_BASELINES = dict(builtin_names.BASELINES)

NAMES_SPEC = """\
# Spec
## 2. 字句
### 2.2 キーワード（全て）

```
fn let match
use trait impl
```

`prev` `delay`（組込みの遅延の flow）と `sample_rate` は、flow の中で予約された組込み名（§11.4）。キーワードは `std.test` で使える。

## 4. 型
### 4.1 組込み型

| 分類 | 型 | 種 |
|---|---|---|
| 整数 | `I8 U32` | Copy |
| 標準 enum | `Option[T]`, `Result[T, E]` | 中身 |
| 関数 | `fn(A) -> R uses {E}` | Copy |

### 4.2 文字列
`Str` is not in the table.

## 6. 関数
### 6.3 trait
- 演算子 trait: `Add Neg`。
- 標準 trait: `PartialEq`, `Iter[T]`。

### 6.5 属性（全て）

`@repr(c)`、`@param(...)`（§11.7）。これ以外の属性は無い（`@deprecated` は必要になったら定義する）。

## 11. flow
### 11.3 レート

| クロック | 意味 |
|---|---|
| （定数） | `const` |
| `init` | 初期化時 |
| `sample` | サンプルごと |

- レートを型の形で書く（`x: Sig[F32]`、0.3 の草案の形）と E0020。`Sig` / `Ctl` は普通の名前で、`struct Sig[T]` を宣言してよい。

### 11.6 生成される API

`flow voice(...)` を宣言すると、コンパイラは名前空間 `voice` に次を生成する。

```onsa
voice.State        // 状態。voice.Hidden は書いていない
fn voice.init(cfg: voice.Config, sample_rate: F32) -> voice.State
```

- 引数の名前は `s`、`params` に固定する。利用者の `x` とは衝突しない。

## 12. メモリ
### 12.4 配置
- 容量の確認: ヘッダの `SIZE` / `BULK_SIZE` で分かる。`fast_budget` を書くと E0820。

## 8. 効果
### 8.1 宣言と使用
- 標準の効果（`Fs` `Random`）は std の `effect` 宣言で、`use` で取り込む。`Alloc` だけは prelude にある。

## 15. モジュール
### 15.1 モジュール
- 暗黙の prelude は、`Option Some None panic Alloc`、種の制約 `Copy` と `Dup`、組込み型だけである。
"""


class BuiltinNames(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        # NAMES_SPEC is a small spec: the baselines are for the real one (test_baselines)
        patcher = mock.patch.object(builtin_names, "BASELINES", {})
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_baselines(self):
        # N2: a place that stops giving a name of its baseline fails
        real = repo.read(repo.ROOT, repo.SPEC)
        baselines = {
            "attributes (§6.5)": {"repr", "fp", "param", "mem"},
            "clocks (§11.3)": {"init", "block", "sample"},
            "generated API (§11.6, §12.4)": {"State", "process", "SIZE"},
        }
        self.assertTrue(builtin_names.builtin_names(real, [], baselines=baselines))
        for old, new, needle in (
            ("、`@mem(...)`（§12.4）。これ以外", "。これ以外", "attributes (§6.5) no longer gives mem"),
            ("| `sample` | サンプルごとの値 |", "| `samples` | サンプルごとの値 |", "clocks (§11.3) no longer gives sample"),
            ("rt fn voice.process(inout", "rt fn voice.run(inout", "no longer gives process"),
            ("ヘッダの `SIZE` / `ALIGN`", "ヘッダの `ALIGN`", "no longer gives SIZE"),
        ):
            with self.subTest(old=old):
                self.assertIn(old, real)
                with self.assertRaisesRegex(builtin_names.CheckError, re.escape(needle)):
                    builtin_names.builtin_names(real.replace(old, new, 1), [], baselines=baselines)

    def test_real_baselines_hold(self):
        # the baselines of the module hold for the spec of the repository
        with mock.patch.object(builtin_names, "BASELINES", BUILTIN_BASELINES):
            builtin_names.builtin_names(repo.read(repo.ROOT, repo.SPEC), [])

    def test_build_outputs_only_are_skipped(self):
        # N1: a `target` directory that is not a build output is scanned
        self.write("crates/x/Cargo.toml", "")
        self.write("crates/x/src/target/mod.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        self.write("crates/x/target/debug/build.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        found = builtin_names.scan(self.root, {"zeroed"})
        self.assertEqual(found, {"crates/x/src/target/mod.rs": {"zeroed": 1}})

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def test_names_from_the_spec(self):
        names = builtin_names.builtin_names(NAMES_SPEC, ["sqrt", "std", "T"])
        expected = {
            "prev", "delay", "sample_rate",  # §2.2, first sentence only (not `std`, `test`)
            "I8", "U32", "Option", "Result",  # §4.1 type column (not `T`, `R`, `fn`)
            "Add", "Neg", "PartialEq", "Iter",  # §6.3
            "Fs", "Random",  # §8.1, inside the parentheses only (not `Alloc` of the next sentence)
            "Some", "None", "panic", "Alloc", "Copy", "Dup",  # §15.1
            "sqrt", "std",  # std
            "repr", "param",  # §6.5, the first sentence (not `deprecated`)
            "init", "sample",  # §11.3, the clocks of the table (not `const`)
            "Sig", "Ctl",  # §11.3, the old rate types (not `F32`, `x`)
            "State", "Config", "cfg", "sample_rate", "params",  # §11.6 (not the comment's `Hidden`, nor `s`, `x`)
            "SIZE", "BULK_SIZE",  # §12.4, the first sentence (not `fast_budget`)
        }  # fmt: skip
        self.assertEqual(names, expected)
        self.assertEqual(builtin_names.keywords(NAMES_SPEC), {"fn", "let", "match", "use", "trait", "impl"})

    def test_a_missing_place_fails(self):
        for old, needle in (
            ("- 暗黙の prelude は", "the prelude"),
            ("- 標準 trait:", "標準 trait"),
            ("標準の効果（", "standard effects"),
            ("予約された組込み名", "reserved builtin names"),
            ("### 4.1 組込み型", "§4.1"),
            ("0.3 の草案の形", "old rate types"),
            ("引数の名前は", "fixed argument names"),
            ("`flow voice(...)`", "example `flow"),
            ("- 容量の確認:", "sizes of the state"),
            ("`@repr(c)`、`@param(...)`", "no attribute"),
            ("| `init` | 初期化時 |\n| `sample` | サンプルごと |", "no clock"),
        ):
            with self.subTest(old=old):
                with self.assertRaisesRegex(builtin_names.CheckError, re.escape(needle)):
                    builtin_names.builtin_names(NAMES_SPEC.replace(old, "x"), [])

    def test_scan_rust(self):
        src = (
            'let a = "zeroed"; // "in a comment"\n'
            '/* "block /* nested */ comment" */ let b = r#"raw "x""#;\n'
            "let c = '\"'; let d = 'x'; fn f<'a>(x: &'a str) {}\n"
            'let e = "esc \\" quote"; let g = b"bytes";\n'
            'let h = "multi\nline"; let i = "after";\n'
        )
        literals, masked = builtin_names.scan_rust(src)
        self.assertEqual([(ln, t) for _, ln, t in literals], [
            (1, "zeroed"), (2, 'raw "x"'), (4, 'esc \\" quote'), (4, "bytes"), (5, "multi\nline"), (6, "after"),
        ])  # fmt: skip
        self.assertEqual(len(masked), len(src))
        self.assertEqual(masked.count("\n"), src.count("\n"))
        self.assertNotIn("comment", masked)

    def test_uses(self):
        names = {"zeroed", "narrow_u8", "trunc_u8_sat", "Option"}
        src = """\
fn f(n: &str) -> bool {
    if n == "zeroed" { return true }
    match n { "Option" | "other" => true, _ => false };
    n.starts_with("narrow_") || n.ends_with("_sat") || n == format!("narrow_{}", k).as_str()
        || n.starts_with("zz") || n == format!("{}f", 1) || n == "Option is a type"
}

#[cfg(test)]
mod tests {
    fn g() { let x = "zeroed"; let y = { "Option" }; }
}

fn after() { "Option"; }
"""
        found = builtin_names.uses_in(src, names)
        self.assertEqual(found, {"zeroed": 1, "Option": 2, "narrow_": 1, "_sat": 1, "narrow_{}": 1})

    def test_parts_of_names(self):
        # M2: the calls that take a part of a name, also inside an array
        names = {"narrow_u8", "trunc_u8_sat", "is_none"}
        src = """\
fn f(n: &str) -> bool {
    n.contains("none") || n.contains("narrow") || n.trim_start_matches("trunc_").is_empty()
        || n.trim_end_matches("_sat").is_empty() || n.starts_with(["narrow_", "zz"]) || n.ends_with(&["_u8_sat"])
        || n.contains("is_none") || n.contains("x") || n.contains("other") || f("narrow_")
}
"""
        found = builtin_names.uses_in(src, names)
        self.assertEqual(
            found,
            {"none": 1, "narrow": 1, "trunc_": 1, "_sat": 1, "narrow_": 1, "_u8_sat": 1, "is_none": 1},
        )

    def test_test_files(self):
        for rel, is_test in (
            ("crates/a/tests/x.rs", True),
            ("crates/a/src/tests.rs", True),
            ("crates/a/src/flow_tests.rs", True),
            ("crates/a/src/contests.rs", False),
            ("crates/a/src/lib.rs", False),
        ):
            self.assertEqual(builtin_names.is_test_file(rel), is_test, rel)

    def run_main(self, args=(), members=()):
        self.write(builtin_names.SPEC, NAMES_SPEC)
        out = io.StringIO()
        cmd = json_cmd({"--std-names": ["zeroed"], "--builtin-members": list(members)})
        with mock.patch("sys.stdout", out):
            code = builtin_names.main(["--root", str(self.root), *args], cmd=cmd)
        return code, out.getvalue()

    def test_members_of_sema_are_names(self):
        # the builtin methods of sema's table (`--builtin-members`) are builtin names
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "checked_add" || n.starts_with("narrow_") }\n')
        self.write(builtin_names.ALLOW, "")
        code, out = self.run_main(members=["checked_add", "narrow_u8"])
        self.assertEqual(code, 1)
        self.assertIn('"checked_add" is written 1 time(s), the list allows 0', out)
        self.assertIn('"narrow_" is written 1 time(s)', out)
        self.assertEqual(self.run_main()[0], 0)  # without them, nothing is found

    def test_same_spelling(self):
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "min" }\n')
        listed = '[allow."crates/a/src/lib.rs"]\n"zeroed" = 1\n\n[same_spelling."crates/a/src/lib.rs"]\n"min" = { count = 1, note = "@param のキー" }\n'
        self.write(builtin_names.ALLOW, listed)
        self.assertEqual(self.run_main(members=["min"])[0], 0)
        # --print keeps the same_spelling entries and their notes
        self.assertEqual(self.run_main(["--print"], members=["min"]), (0, listed))
        # both tables count: one more fails, asking for the place or a note
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "min" || n == "min" }\n')
        code, out = self.run_main(members=["min"])
        self.assertEqual(code, 1)
        self.assertIn('"min" is written 2 time(s), the list allows 1', out)
        self.assertIn("[same_spelling]", out)
        # one fewer asks to lower the count
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        code, out = self.run_main(members=["min"])
        self.assertEqual(code, 1)
        self.assertIn('"min" is written 0 time(s), the list allows 1; lower the count', out)
        # an entry needs a count and a note
        for bad in ('"min" = 1', '"min" = { count = 1 }', '"min" = { count = 1, note = " " }', '"min" = { count = 0, note = "x" }'):
            with self.subTest(bad=bad):
                self.write(builtin_names.ALLOW, f'[same_spelling."crates/a/src/lib.rs"]\n{bad}\n')
                code, out = self.run_main(members=["min"])
                self.assertEqual(code, 1)
                self.assertIn("cannot check", out)

    def test_main(self):
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" }\n')
        self.write("crates/a/tests/t.rs", 'fn t() { "zeroed"; }\n')
        self.write("crates/onsa_diag/src/codes.rs", 'fn t() { "zeroed"; }\n')  # the registry
        allow = '[allow."crates/a/src/lib.rs"]\n"Option" = 2\n"zeroed" = 1\n'
        self.write(builtin_names.ALLOW, allow)
        code, out = self.run_main()
        self.assertEqual(code, 0, out)
        # the list prints itself
        code, out = self.run_main(["--print"])
        self.assertEqual((code, out), (0, allow))
        # one more literal fails
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" || n == "None" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn('"None" is written 1 time(s), the list allows 0', out)
        # one fewer fails too, asking to lower the list
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn('"Option" is written 1 time(s), the list allows 2; lower the count', out)
        # a file of the list that is gone
        self.write(builtin_names.ALLOW, allow + '[allow."crates/gone.rs"]\n"zeroed" = 1\n')
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("`crates/gone.rs` is not a file", out)
        # a malformed list
        for bad in ('[other]\nx = 1\n', '[allow."crates/a/src/lib.rs"]\n"zeroed" = 0\n', "[allow\n"):
            with self.subTest(bad=bad):
                self.write(builtin_names.ALLOW, bad)
                code, out = self.run_main()
                self.assertEqual(code, 1)
                self.assertIn("cannot check", out)

    def test_repository_list_is_sorted_and_positive(self):
        lists, notes = builtin_names.load_allow(builtin_names.ROOT / builtin_names.ALLOW)
        for table in builtin_names.TABLES:
            files = lists[table]
            self.assertEqual(list(files), sorted(files), table)
            for names in files.values():
                self.assertEqual(list(names), sorted(names), table)
        # every same_spelling entry says its meaning
        self.assertEqual(len(notes), sum(len(n) for n in lists["same_spelling"].values()))


class IgnoredFiles(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        self.write(".gitignore", "*.out\nbuild/\ntarget/\n")
        self.write("tests/spec/a.onsa")
        # a user's global excludes file that ignores everything Onsa
        self.home = Path(self.tmp.name) / "home"
        (self.home).mkdir()
        (self.home / "ignore").write_text("*.onsa\n*.rs\n")
        (self.home / "gitconfig").write_text(f"[core]\n\texcludesFile = {self.home / 'ignore'}\n")

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text="x\n"):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def check(self):
        out = io.StringIO()
        env = {"GIT_CONFIG_GLOBAL": str(self.home / "gitconfig")}
        with mock.patch("sys.stdout", out), mock.patch.dict(os.environ, env):
            code = ignored_files.main(["--root", str(self.root)])
        return code, out.getvalue()

    def test_clean(self):
        self.write("tests/pkg/onsa.toml")
        self.write("tests/pkg/target/host/x.c")  # the build output of a package
        self.write("crates/a/Cargo.toml")
        self.write("crates/a/target/debug/x")  # the build output of a crate
        self.write("target/debug/y")  # the build output at the root
        self.write("build/x")  # outside the scanned directories
        self.write("crates/a/src/lib.rs")  # the global excludes file ignores it; the check does not read it
        self.write(".git/info/exclude", "*.toml\n")
        self.write("std/math.onsa")
        code, out = self.check()
        self.assertEqual(code, 0, out)

    def test_ignored_files_fail(self):
        self.write("tests/build/case.onsa")
        self.write("tests/golden/c/x.out")
        self.write("tests/target/y.onsa")  # `target/` with no manifest beside it
        self.write("crates/a/src/target/m.rs")
        self.write("std/build/z.onsa")
        self.write("runtime/c/a.out")
        self.write("tools/build/t.py")
        code, out = self.check()
        self.assertEqual(code, 1)
        for p in ("tests/build/", "tests/golden/c/x.out", "tests/target/", "crates/a/src/target/", "std/build/",
                  "runtime/c/a.out", "tools/build/"):  # fmt: skip
            self.assertIn(f"{p}: the .gitignore ignores it", out)

    def test_tracked_but_matched_fails(self):
        self.write("tests/golden/c/kept.out")
        subprocess.run(["git", "add", "-f", "tests/golden/c/kept.out"], cwd=self.root, check=True)
        code, out = self.check()
        self.assertEqual(code, 1)
        self.assertIn("tests/golden/c/kept.out: committed, but a .gitignore pattern matches it", out)

    def test_not_a_repository(self):
        with tempfile.TemporaryDirectory() as d:
            out = io.StringIO()
            with mock.patch("sys.stdout", out):
                self.assertEqual(ignored_files.main(["--root", d]), 1)
            self.assertIn("cannot ask git", out.getvalue())

    def test_build_outputs(self):
        (self.root / "crates/a").mkdir(parents=True)
        (self.root / "crates/a/Cargo.toml").write_text("")
        for rel, out in (
            ("target/x", True),
            ("crates/a/target/x", True),
            ("crates/a/src/target/x", False),
            ("crates/target/x", False),
            ("tests/targets/x", False),
        ):
            self.assertEqual(repo.is_build_output(self.root, rel), out, rel)


# A stand-in for the compiler: an input with `X` is an internal error, one with
# `Y` a raw panic in the `check` command only, one with `Z` a signal, one that
# ends with `@` (no newline after it) another internal error. The signal is
# SIGKILL: an abort would make the system write a crash report.
FAKE_ONSA = r"""
import os, sys
text = open(sys.argv[-1], encoding="utf-8").read()
check = sys.argv[1] == "check"
if "X" in text:
    sys.stderr.write("onsa: internal error: index out of bounds: the len is 3 but the index is 7\n"
                     "  = at crates/onsa_sema/src/body.rs:12:5\n")
    sys.exit(101)
if text.endswith("@"):
    sys.stderr.write("onsa: internal error: range end index 4 out of range for slice of length 3\n"
                     "  = at crates/onsa_sema/src/layout.rs:7:9\n")
    sys.exit(101)
if "Y" in text and check:
    sys.stderr.write("thread 'main' panicked at crates/a.rs:1:1:\nboom\n")
    sys.exit(0)
if "Z" in text:
    os.kill(os.getpid(), 9)
sys.exit(1 if "e" in text else 0)
"""


# A stand-in for `onsa_cases --fix-same-place` (W3-17): an input with `BADCANDIDATE` breaks the
# contract of a fix candidate; with `CRASH_FIX` in a path list's first input, the tool fails.
FAKE_CASES = r"""
import json, sys
assert sys.argv[1] == "--fix-same-place"
out = []
for path in sys.argv[2:]:
    text = open(path, encoding="utf-8", errors="surrogateescape").read()
    if "CRASH_FIX" in text:
        sys.stderr.write("boom\n")
        sys.exit(3)
    v = []
    if "BADCANDIDATE" in text:
        v.append({"code": "E0010", "line": 1, "col": 1, "title": "parenthesize the `&&` of 12", "left": "E0010",
                  "left_line": 1, "left_col": 1, "message": "m"})
    out.append({"file": path, "candidates": len(v), "violations": v, "internal": None})
print(json.dumps(out))
"""


class Fuzz(TempRepo):
    def setUp(self):
        super().setUp()
        self.fake = self.repo.write("fake_onsa.py", FAKE_ONSA)
        self.argv = [sys.executable, "-B", str(self.fake)]
        self.fix_argv = [sys.executable, "-B", str(self.repo.write("fake_cases.py", FAKE_CASES))]

    def go(self, per_seed=0, save=False, truncated=fuzz.TRUNCATIONS, swept=False):
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, per_seed, "t", 2, save, out=lines.append,
                        truncated=truncated, swept=swept)
        return code, "\n".join(lines)

    def test_classify(self):
        self.assertIsNone(fuzz.classify(("check",), 1, "x.onsa:1:1: error[E0002]: ..."))
        c = fuzz.classify(
            ("check",), 101,
            "onsa: internal error: byte index 29 is not a char boundary; it is inside '辞' (bytes 28..31) of `\"{辞\n"
            "fn f() {`\n  --> m.onsa:1:1\n  = at crates/onsa_syntax/src/lexer.rs:283:34\n",
        )
        self.assertEqual(
            c.signature,
            "internal|crates/onsa_syntax/src/lexer.rs|byte index # is not a char boundary; it is inside '?' (bytes #..#) of `…`",
        )
        # a quoted name stays: two different panics are two classes
        a = fuzz.classify(("check",), 101, "onsa: internal error: called `Option::unwrap()` on a `None` value\n"
                          "  = at crates/a.rs:1:1\n")
        b = fuzz.classify(("check",), 101, "onsa: internal error: called `Result::unwrap()` on an `Err` value\n"
                          "  = at crates/a.rs:1:1\n")
        self.assertIn("`Option::unwrap()`", a.signature)
        self.assertNotEqual(a.signature, b.signature)
        lowering = fuzz.classify(("check",), 101, "onsa: internal error: internal lowering error: no field\n  --> m.onsa:1:1\n")
        self.assertEqual(lowering.signature, "internal|-|internal lowering error: no field")
        raw = fuzz.classify(("fmt", "--check"), 0, "thread 'main' panicked at a.rs:1:1:\n")
        self.assertEqual(raw.command, "fmt --check")
        overflow = fuzz.classify(("check",), -6, "thread 'main' has overflowed its stack\nfatal runtime error: stack overflow\n")
        self.assertTrue(overflow.signature.startswith("signal 6|check|"), overflow)
        self.assertEqual(fuzz.classify(("check",), None, "", timed_out=True).signature, "timeout")

    def test_mutants_are_the_same_for_the_same_seeds(self):
        files = [("tests/a.onsa", "pub fn f() -> I32 {\n  1\n}\n"), ("tests/b.onsa", "let x = 2\n")]
        a = fuzz.mutants(files, 5, "1")
        self.assertEqual(a, fuzz.mutants(files, 5, "1"))
        self.assertEqual(len(a), 10)
        self.assertNotEqual(a, fuzz.mutants(files, 5, "2"))
        # a new seed file does not change the mutants of the others
        more = fuzz.mutants(files + [("tests/c.onsa", "x\n")], 5, "1")
        self.assertEqual([m for m in more if m[0] != "tests/c.onsa"], a)

    def test_truncations_are_the_same_for_the_same_seeds(self):
        # FZ-1: each seed cut at the end of a token, with no blank or newline at the end of the file
        text = "// a comment: (x, y)\npub fn f(x: I32) -> I32 {\n  let y = x@3 ~ _\n  y\n}\n"
        files = [("tests/a.onsa", text), ("tests/b.onsa", "let x = 2\n")]
        a = fuzz.truncations(files, 50, "1")
        self.assertEqual(a, fuzz.truncations(files, 50, "1"))
        self.assertEqual(len(a), 100)
        self.assertNotEqual(a, fuzz.truncations(files, 50, "2"))
        self.assertEqual(len(fuzz.truncations(files, 0, "1")), 0)
        for path, k, t in a:
            seed = dict(files)[path]
            with self.subTest(path=path, k=k, t=t):
                self.assertTrue(t and seed.startswith(t), t)
                self.assertNotIn(t[-1], " \t\r\n")
                self.assertNotIn("//", t.rsplit("\n", 1)[-1])  # never inside the comment
                # at the end of a token: the next character of the seed does not continue a name or a number
                self.assertFalse(re.fullmatch(r"\w\w", seed[len(t) - 1:len(t) + 1]), seed[len(t):])
        # most of the cuts come right after a symbol, some after a name or a number
        after = [t for p, _, t in a if p == "tests/a.onsa" and fuzz.CUT_AFTER.search(t[-1])]
        self.assertGreater(len(after), 25)
        self.assertLess(len(after), 50)
        self.assertTrue(any(t.endswith("@") for _, _, t in a), a)
        # a symbol rare in the corpus is cut after as often as a common one: the one `@` among 30 `(`
        rare = fuzz.truncations([("tests/a.onsa", "f(" * 30 + "x@1\n"), ("tests/b.onsa", "g(" * 200 + "\n")], 40, "1")
        self.assertGreater(sum(1 for p, _, t in rare if p == "tests/a.onsa" and t.endswith("x@")), 20, rare)
        # a seed with no token (only a comment, or empty) gives itself without the blanks at its end
        self.assertEqual(fuzz.truncations([("tests/c.onsa", "// c\n\n")], 2, "1"),
                         [("tests/c.onsa", 0, "// c"), ("tests/c.onsa", 1, "// c")])
        self.assertEqual(fuzz.truncations([("tests/e.onsa", "")], 1, "1"), [("tests/e.onsa", 0, "")])

    # FZ-1: `_` inside a name, a line comment (its words and its end: the `?` and the `!` of the comments
    # end them), a string (its `@` and `//` are code), the operators `* / %` and the backslash.
    CUT_TEXT = 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//t"~\n// end!\n'

    def test_cut_sites_are_exact(self):
        after, ends = fuzz.cut_sites(self.CUT_TEXT)
        self.assertEqual(after, {"(": [4], "_": [5], "*": [8], "/": [11, 34, 35], "%": [14], "\\": [17],
                                 "@": [30, 33], '"': [31, 37], "~": [38]})
        self.assertEqual(ends, [3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 29, 31, 32, 34, 35, 36, 38])
        # the rare symbols of the sweep are symbols of CUT_AFTER (else `cut_sites` never gives them)
        self.assertTrue(all(fuzz.CUT_AFTER.fullmatch(c) for c in fuzz.RARE), fuzz.RARE)
        self.assertEqual(sorted(fuzz.RARE), sorted("~!?'^@#/\\%"))
        self.assertEqual(sorted(fuzz.RARE), sorted(set(fuzz.RARE)))

    def test_sweep_cuts_after_every_rare_symbol(self):
        # FZ-1: every place right after a rare symbol, outside a line comment and not at its end (the
        # first `/` of a comment is in it), in the order of the seeds and the places; the same text
        # once; no generator (no version). `*` is not rare: no cut after it.
        files = [("tests/a.onsa", self.CUT_TEXT), ("tests/b.onsa", "x@\n// ^\n"), ("tests/c.onsa", "y ~ z\n"),
                 ("tests/d.onsa", "a'b' #[c] !d ?e ^f\n")]
        self.assertEqual(fuzz.sweep(files), [
            ("tests/a.onsa", "sweep `/` at 1:11", "a_b(_) * c/"),
            ("tests/a.onsa", "sweep `%` at 1:14", "a_b(_) * c/d %"),
            ("tests/a.onsa", "sweep `\\` at 1:17", "a_b(_) * c/d % e\\"),
            ("tests/a.onsa", "sweep `@` at 2:2", 'a_b(_) * c/d % e\\f // g@ h?\nx@'),
            ("tests/a.onsa", "sweep `@` at 2:5", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@'),
            ("tests/a.onsa", "sweep `/` at 2:6", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@/'),
            ("tests/a.onsa", "sweep `/` at 2:7", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//'),
            ("tests/a.onsa", "sweep `~` at 2:10", 'a_b(_) * c/d % e\\f // g@ h?\nx@"s@//t"~'),
            ("tests/b.onsa", "sweep `@` at 1:2", "x@"),
            ("tests/c.onsa", "sweep `~` at 1:3", "y ~"),
            ("tests/d.onsa", "sweep `'` at 1:2", "a'"),
            ("tests/d.onsa", "sweep `'` at 1:4", "a'b'"),
            ("tests/d.onsa", "sweep `#` at 1:6", "a'b' #"),
            ("tests/d.onsa", "sweep `!` at 1:11", "a'b' #[c] !"),
            ("tests/d.onsa", "sweep `?` at 1:14", "a'b' #[c] !d ?"),
            ("tests/d.onsa", "sweep `^` at 1:17", "a'b' #[c] !d ?e ^"),
        ])
        # the same cut from another seed is not run twice
        self.assertEqual(fuzz.sweep([("tests/b.onsa", "x@\n"), ("tests/e.onsa", "x@\n\n// y\n")]),
                         [("tests/b.onsa", "sweep `@` at 1:2", "x@")])
        self.assertEqual(fuzz.sweep([("tests/c.onsa", "// only ~ a comment\n"), ("tests/e.onsa", "")]), [])

    def test_sweep_finds_crashes_but_skips_the_fix_stage(self):
        # FZ-1: every cut after a `@` crashes the fake compiler; the seed itself (with its newline) does
        # not, and the fix stage, which the seed would break, does not see the cuts
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE x@ y@\n")
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/layout.rs|range end index # out of range "
                      "for slice of length # (seed tests/spec/x.onsa, sweep `@` at 1:15)", text)
        self.assertIn("0 truncations (0 each, 0 crashing), 2 cuts swept after `~!?'^@#/\\%` (2 crashing), 2 crashing in all",
                      text)
        self.assertIn("0 mutants through the fix stage", text)
        self.assertNotIn("fix-same-place", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "@", new)
        # listed: known
        self.repo.write("tests/fuzz/at.onsa", "@")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/at.onsa"))
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 0, text)
        # without the sweep the cuts do not run, and the line does not name them
        code, text = self.go(truncated=0)
        self.assertEqual(code, 0, text)
        self.assertNotIn("swept", text)
        # a sweep with no place to cut is no pass
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE // x@\n")
        code, text = self.go(truncated=0, swept=True)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL the sweep found no place after a rare symbol (~!?'^@#/\\%) in 2 seeds", text)

    def test_main_passes_the_options_to_run(self):
        # FZ-1: --truncations reaches the run; --deep sweeps and has no weighted truncation unless asked
        calls = []

        def run(*args, **kw):
            calls.append((args, kw))
            return 0

        base = ["--root", str(self.repo.root), "--binary", "onsa", "--cases-binary", "onsa_cases"]
        with mock.patch.object(fuzz, "run", run), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"):
            for extra, want in (([], (fuzz.PER_SEED, fuzz.TRUNCATIONS, False, False)),
                                (["--truncations", "5"], (fuzz.PER_SEED, 5, False, False)),
                                (["--deep"], (fuzz.PER_SEED, 0, True, True)),
                                (["--deep", "--per-seed", "0", "--truncations", "3"], (0, 3, True, True))):
                with self.subTest(extra=extra):
                    calls.clear()
                    self.assertEqual(fuzz.main(base + extra), 0)
                    (args, kw), = calls
                    self.assertEqual((args[3], kw["truncated"], kw["deep"], kw["swept"]), want)
                    self.assertEqual(args[1:3], (["onsa"], ["onsa_cases"]))

    def test_truncations_find_crashes_but_skip_the_fix_stage(self):
        # FZ-1: a file that ends right after `@` crashes the fake compiler; the seed itself (with its
        # newline) and the fix stage do not see it. No mutant here: the truncations alone find it.
        # (the comment holds no cut: every cut ends with `@`)
        self.repo.write("tests/spec/x.onsa", "// BADCANDIDATE\n@@@@@@@@@@\n")
        code, text = self.go(per_seed=0, truncated=3)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/layout.rs|range end index # out of range "
                      "for slice of length # (seed tests/spec/x.onsa, truncation 0)", text)
        self.assertIn("6 truncations (3 each, 3 crashing)", text)
        # the truncations do not go through the fix stage: no broken candidate is seen
        self.assertIn("0 mutants through the fix stage", text)
        self.assertNotIn("fix-same-place", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "@", new)
        # listed: known, as the crash classes of the mutants
        self.repo.write("tests/fuzz/at.onsa", "@")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/at.onsa"))
        code, text = self.go(per_seed=0, truncated=3)
        self.assertEqual(code, 0, text)
        # without truncations nothing crashes
        self.repo.write("tests/pending.toml", "")
        self.repo.write("tests/fuzz/at.onsa", "ok")
        code, text = self.go(per_seed=0, truncated=0)
        self.assertEqual(code, 0, text)

    def test_minimize_keeps_the_class(self):
        runner = fuzz.Runner(self.argv, self.repo.root / "work")
        text = "fn a() {}\nfn b() { X }\nfn c() {}\n"
        sig = runner.crashes(text)[0].signature
        small = fuzz.minimize(runner, text, sig)
        self.assertEqual(small, "X")

    def test_replay_follows_the_list(self):
        self.repo.write("tests/fuzz/listed.onsa", "X")
        self.repo.write("tests/fuzz/fixed.onsa", "ok")
        self.repo.write("tests/fuzz/regression.onsa", "ok")
        self.repo.write("tests/fuzz/unlisted.onsa", "a Z")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/listed.onsa")
                        + entry("fuzz-input", "tests/fuzz/fixed.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        fails = [l for l in text.split("\n") if l.startswith("FAIL")]
        self.assertEqual(len(fails), 2, text)
        self.assertIn("tests/fuzz/fixed.onsa: no longer crashes", fails[0])
        self.assertIn("tests/fuzz/unlisted.onsa: crashes but is not listed", fails[1])

    def test_new_and_known_classes(self):
        # the seed's mutants crash (it holds an X); the class is new until a listed input shows it
        self.repo.write("tests/spec/x.onsa", "XXXXXXXXXXXXXXXXXXXX\n")
        code, text = self.go(per_seed=3)
        self.assertEqual(code, 1, text)
        self.assertIn("a new crash class: check: internal|crates/onsa_sema/src/body.rs|index out of bounds", text)
        self.assertIn('kind = "fuzz-input"', text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "X", new)
        self.assertFalse((self.repo.root / "tests" / "fuzz").exists())  # the gate writes nothing under tests/
        # listed: known
        self.repo.write("tests/fuzz/x.onsa", "X")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/x.onsa"))
        code, text = self.go(per_seed=3)
        self.assertEqual(code, 0, text)
        # --save writes the input under tests/fuzz
        self.repo.write("tests/spec/y.onsa", "YYYYYYYYYYYYYYYYYYYY\n")
        code, text = self.go(per_seed=3, save=True)
        self.assertEqual(code, 0, text)
        self.assertTrue((self.repo.root / "tests" / "fuzz" / f"{fuzz.short_name('Y')}.onsa").exists(), text)

    def test_replay_of_the_fix_stage(self):
        # W3-17: a listed input that still breaks a candidate's contract is still failing; one not
        # listed fails; a listed input that does neither asks for its entry to go
        self.repo.write("tests/fuzz/listed.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/fixed.onsa", "ok")
        self.repo.write("tests/fuzz/unlisted.onsa", "BADCANDIDATE")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/listed.onsa")
                        + entry("fuzz-input", "tests/fuzz/fixed.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        fails = [l for l in text.split("\n") if l.startswith("FAIL")]
        self.assertEqual(len(fails), 2, text)
        self.assertIn("tests/fuzz/fixed.onsa: no longer crashes nor breaks the contract", fails[0])
        self.assertIn("tests/fuzz/unlisted.onsa: breaks the contract of a fix candidate but is not listed", fails[1])
        self.assertIn("fix|E0010|parenthesize the `…` of #|E0010", fails[1])

    def test_fix_stage_classes(self):
        # one mutant in FIX_EVERY goes through the fix stage; a new class is minimized and written
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 1, text)
        self.assertIn("a new class of a broken fix candidate: fix-same-place: fix|E0010|parenthesize the `…` of #|E0010",
                      text)
        # 2 seeds of FIX_EVERY mutants: the first of each FIX_EVERY
        self.assertIn("2 mutants through the fix stage (0 not UTF-8)", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "BADCANDIDATE", new)
        # a listed input shows the class: known
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/f.onsa"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 0, text)

    BAD = "fix|E0010|parenthesize the `…` of #|E0010"

    def test_allowed_classes(self):
        # R-207: a class of the fix stage that the spec puts outside the contract is known through
        # tests/fuzz/allowed.toml, as long as its input shows it
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 0, text)
        self.assertIn("(0 listed, 1 allowed)", text)
        # the input no longer shows the class: the entry goes
        self.repo.write("tests/fuzz/f.onsa", "ok")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn(f"tests/fuzz/f.onsa: the class `{self.BAD}` with `m` no longer shows; remove its entry", text)
        # the class with another message left is not the entry's: a new class, and the input
        # does not show the entry's
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa", left="another"))
        code, text = self.go(per_seed=fuzz.FIX_EVERY)
        self.assertEqual(code, 1, text)
        self.assertIn(f"a new class of a broken fix candidate: fix-same-place: {self.BAD}", text)
        self.assertIn(f"tests/fuzz/f.onsa: shows `{self.BAD}` with `m`, which is not the entry's", text)
        self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa"))
        # the input shows another class too
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE X")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("tests/fuzz/f.onsa: shows `internal|", text)

    def test_allowed_entries_are_checked(self):
        self.repo.write("tests/fuzz/f.onsa", "BADCANDIDATE")
        good = allowed(self.BAD, "tests/fuzz/f.onsa")
        for toml, want in (
            (good.replace('note = "n"', 'note = "n"\nuntil = "W3-06"'), "unknown field `until`"),
            (good.replace('note = "n"\n', ""), "missing field `note`"),
            (allowed("internal|crates/a.rs|boom", "tests/fuzz/f.onsa"), "a crash is never allowed"),
            (allowed(self.BAD, "tests/fuzz/none.onsa"), "the input `tests/fuzz/none.onsa` does not exist"),
            (allowed(self.BAD, "tests/spec/ops/groups.onsa"), "must be a saved input"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("W3-07",)), "one or more S / R numbers"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-45", "s-45")), "one or more S / R numbers"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-99999",)),
             "the reason `S-99999` is not in the tables (plan §2 for S, review for R)"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("S-45", "R-1")),
             "the reason `R-1` is not in the tables (plan §2 for S, review for R)"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", reasons=("R-23", "R-23")), "a reason is listed twice"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", note=""), "`note` must be a non-empty string"),
            (good + good, f"the class `{self.BAD}` with `m` is listed twice"),
            (good + allowed(self.BAD, "tests/fuzz/f.onsa", left="other"), "is the input of another entry"),
            (good.replace('left = "m"\n', ""), "missing field `left`"),
            (allowed(self.BAD, "tests/fuzz/f.onsa", left="line 3"), "`left` must be the message"),
            ("[x]\n" + good, "unknown top-level key `x`"),
        ):
            with self.subTest(want=want):
                self.repo.write("tests/fuzz/allowed.toml", toml)
                code, text = self.go()
                self.assertEqual(code, 1, text)
                self.assertIn(want, text)
        # an R number of the review is a reason too (a low harm recorded there)
        for reasons in (("R-23",), ("S-45", "R-113")):
            with self.subTest(reasons=reasons):
                self.repo.write("tests/fuzz/allowed.toml", allowed(self.BAD, "tests/fuzz/f.onsa", reasons=reasons))
                code, text = self.go()
                self.assertEqual(code, 0, text)
                self.assertIn("(0 listed, 1 allowed)", text)
        # an input listed in tests/pending.toml too
        self.repo.write("tests/fuzz/allowed.toml", good)
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/f.onsa"))
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("is listed in tests/pending.toml too", text)

    def test_fix_stage_failure_fails(self):
        # the tool failing is never a pass
        self.repo.write("tests/fuzz/a.onsa", "CRASH_FIX")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("the fix stage cannot run on the saved inputs: exit 3: boom", text)

    def test_fix_signature(self):
        v = {"code": "E0320", "title": "rename `Foo1` to `foo1`", "left": "E0002"}
        self.assertEqual(fuzz.fix_signature(v), "fix|E0320|rename `…` to `…`|E0002")
        self.assertEqual(fuzz.fix_signature({**v, "title": "use 3 args"}), "fix|E0320|use # args|E0002")

    def test_inputs_are_bytes(self):
        # a `\r` and invalid UTF-8 reach the compiler as they are
        raw = b"fn f() {\r\n  1\xff\r\n}\r\n"
        self.repo.write("tests/spec/ops/groups.onsa", "")
        (self.repo.root / "tests/spec/ops/groups.onsa").write_bytes(raw)
        files = fuzz.seeds(self.repo.root)
        self.assertEqual(fuzz.encode(files[0][1]), raw)
        echo = self.repo.write("echo.py", "import sys\nsys.stdout.buffer.write(open(sys.argv[-1], 'rb').read())\n")
        runner = fuzz.Runner([sys.executable, "-B", str(echo)], self.repo.root / "work")
        self.assertEqual(runner.crashes(files[0][1]), [])

    def test_deep_mutants_only_on_request(self):
        # only the mutants are made here; none of them runs (an overflow aborts)
        files = [("tests/a.onsa", "pub fn f() -> I32 {\n  1\n}\n")]
        depth = lambda m: max(m[2].count("("), m[2].count("{"), m[2].count("["))  # noqa: E731
        self.assertTrue([m for m in fuzz.mutants(files, 200, "1", deep=True) if depth(m) >= 2000])
        self.assertFalse([m for m in fuzz.mutants(files, 200, "1") if depth(m) >= 2000])

    def test_time_budget(self):
        self.repo.write("tests/spec/x.onsa", "a\n")
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 50, "t", 1, False, out=lines.append,
                        time_budget=0.001)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("time budget" in l for l in lines), lines)
        # the truncations count against the budget too (FZ-1)
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 0, "t", 1, False, out=lines.append,
                        time_budget=0.001, truncated=50)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("of 100 inputs (0 mutants, 100 truncations, 0 swept) did not run" in l for l in lines),
                        lines)
        # and the sweep (FZ-1)
        self.repo.write("tests/spec/x.onsa", "a@ b@ c@\n")
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, 0, "t", 1, False, out=lines.append,
                        time_budget=0.001, truncated=0, swept=True)
        self.assertEqual(code, 1, lines)
        self.assertTrue(any("of 3 inputs (0 mutants, 0 truncations, 3 swept) did not run" in l for l in lines), lines)

    def test_seeds_skip_the_saved_inputs(self):
        self.repo.write("tests/fuzz/a.onsa", "X")
        paths = [p for p, _ in fuzz.seeds(self.repo.root)]
        self.assertEqual(paths, ["tests/spec/ops/groups.onsa"])

    # X-1: the narrowed runs and the base binaries.

    def test_a_narrowed_plan_is_a_part_of_the_whole(self):
        # the seeds, the corpus and the weights are the whole run's; the fix stage takes a mutant by its
        # index in the whole run (the subset experiment of the advisor: narrowing the list first breaks it)
        files = [(f"tests/spec/d{i % 4}/s{i}.onsa", f"pub fn f{i}(x: I32) -> I32 {{\n  x@{i} ~ 'a' + {i}\n}}\n")
                 for i in range(24)]
        only = {p for p, _ in files[3::5]}
        whole = fuzz.plan(files, 6, "1", truncated=3, swept=True)
        part = fuzz.plan(files, 6, "1", truncated=3, swept=True, only=only)
        self.assertEqual(whole[3], [i for i in range(len(whole[0])) if i % fuzz.FIX_EVERY == 0])
        mutants, cuts, swept, chosen = part
        self.assertEqual(mutants, [m for m in whole[0] if m[0] in only])
        self.assertEqual(cuts, [c for c in whole[1] if c[0] in only])
        self.assertTrue({c[2] for c in swept} <= {c[2] for c in whole[2]}, swept)
        self.assertEqual({c[0] for c in swept}, only)
        self.assertEqual([mutants[i] for i in chosen], [whole[0][i] for i in whole[3] if whole[0][i][0] in only])
        self.assertTrue(chosen and len(chosen) < len(whole[3]))

    def go_narrowed(self, selection=None, base=None, per_seed=fuzz.FIX_EVERY):
        lines = []
        code = fuzz.run(self.repo.root, self.argv, self.fix_argv, per_seed, "t", 2, False, out=lines.append,
                        selection=selection, base=base)
        return code, "\n".join(lines)

    def base_of(self, script=FAKE_CASES):
        return narrowing.Base("abc1234", (), (sys.executable, "-B", str(self.repo.write("base_cases.py", script))))

    SAMPLED = narrowing.Selection(sample=1.0, salt="W9-99")
    SIG = "fix|E0010|parenthesize the `…` of #|E0010"

    def test_a_class_the_base_shows_does_not_fail_a_narrowed_run(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go_narrowed(self.SAMPLED, self.base_of())
        self.assertEqual(code, 0, text)
        self.assertIn(f"\npre-existing (the base abc1234 shows it): fix-same-place: {self.SIG} (seed ", text)
        self.assertIn("from 2 of 2 seeds (sample 2) (4 each)", text)
        self.assertIn("; base abc1234: 1 pre-existing;", text)
        self.assertNotIn("FAIL", text)
        new = list((self.repo.root / "target" / "fuzz" / "new").glob("*.onsa"))
        self.assertTrue(new and new[0].read_text() == "BADCANDIDATE", new)  # written for the parent to register

    def test_a_class_the_base_does_not_show_fails(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        for name, script in (("no violation", FAKE_CASES.replace('"BADCANDIDATE" in text', "False")),
                             ("another message left", FAKE_CASES.replace('"message": "m"', '"message": "other"')),
                             ("another code left", FAKE_CASES.replace('"left": "E0010"', '"left": "E0011"'))):
            with self.subTest(name):
                code, text = self.go_narrowed(self.SAMPLED, self.base_of(script))
                self.assertEqual(code, 1, text)
                self.assertIn(f"FAIL a new class of a broken fix candidate: fix-same-place: {self.SIG}", text)
                self.assertIn("; base abc1234: 0 pre-existing;", text)
        # the base's tool fails: it cannot tell, and the class fails
        code, text = self.go_narrowed(self.SAMPLED, self.base_of("import sys\nsys.exit(3)\n"))
        self.assertEqual(code, 1, text)
        self.assertIn("(the base cannot tell: exit 3: no list of results)", text)

    def test_a_crash_from_before_fails(self):
        # an internal error fails even when the base would show it: the base does not run it
        self.repo.write("tests/spec/x.onsa", "XXXXXXXXXXXXXXXXXXXX\n")
        code, text = self.go_narrowed(self.SAMPLED, self.base_of(), per_seed=3)
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL a new crash class: check: internal|crates/onsa_sema/src/body.rs", text)
        self.assertNotIn("pre-existing", text.replace("0 pre-existing", ""))

    def test_an_unknown_base_and_whole_runs_fail(self):
        self.repo.write("tests/spec/x.onsa", "BADCANDIDATE " * 10 + "\n")
        code, text = self.go_narrowed(self.SAMPLED, "no target/base/abc1234/COMMIT")
        self.assertEqual(code, 1, text)
        self.assertIn("; base unknown (no target/base/abc1234/COMMIT);", text)
        self.assertIn(f"FAIL a new class of a broken fix candidate: fix-same-place: {self.SIG}", text)
        code, text = self.go_narrowed(self.SAMPLED, None)
        self.assertEqual(code, 1, text)
        self.assertNotIn("; base", text)
        # a whole run and a shard fail on a class from before, and mark it
        for selection in (None, narrowing.Selection(shard=(0, 1))):
            with self.subTest(selection=selection):
                code, text = self.go_narrowed(selection, self.base_of())
                self.assertEqual(code, 1, text)
                self.assertRegex(text, rf"FAIL a new class of a broken fix candidate: fix-same-place: {re.escape(self.SIG)} "
                                       r"\(seed [^)]*\) \(pre-existing: the base abc1234 shows it\)")
        self.assertIn("from 2 of 2 seeds (shard 0/1)", text)

    def test_a_narrowed_run_mutates_the_picked_seeds_only(self):
        # the seed that is not picked (the sample takes one seed of the group tests/spec/q) gives no mutant;
        # the replay is whole
        for i in range(6):
            self.repo.write(f"tests/spec/q/s{i}.onsa", "XXXXXXXXXXXXXXXXXXXX\n" if i else "ok\n")
        self.repo.write("tests/fuzz/x.onsa", "X")
        self.repo.write("tests/pending.toml", entry("fuzz-input", "tests/fuzz/x.onsa"))
        selection = narrowing.Selection(sample=1e-9, salt="W9-99")
        seeds = fuzz.seeds(self.repo.root)
        picked = narrowing.pick(seeds, selection, self.repo.root)
        self.assertEqual(len(picked.paths), 2)  # one of each group
        code, text = self.go_narrowed(selection, per_seed=2)
        self.assertEqual(code, 0, text)
        self.assertIn("4 mutants from 2 of 7 seeds (sample 2) (2 each)", text)
        self.assertIn("1 saved inputs replayed (1 listed", text)

    def test_main_passes_the_narrowing(self):
        calls = []

        def run(*args, **kw):
            calls.append(kw)
            return 0

        base = ["--root", str(self.repo.root), "--binary", "onsa", "--cases-binary", "onsa_cases"]
        with mock.patch.object(fuzz, "run", run), \
                mock.patch.object(fuzz, "target_directory", lambda root: self.repo.root / "target"):
            self.assertEqual(fuzz.main(base + ["--sample", "0.1", "--salt", "W9-99", "--base", "none"]), 0)
            self.assertEqual(calls[-1]["selection"], narrowing.Selection(sample=0.1, salt="W9-99"))
            self.assertIsNone(calls[-1]["base"])
            self.assertEqual(fuzz.main(base + ["--shard", "1/2"]), 0)
            self.assertEqual(calls[-1]["selection"], narrowing.Selection(shard=(1, 2)))
            self.assertIn("merge base", calls[-1]["base"])  # not a git work tree: unknown
            self.assertEqual(fuzz.main(base), 0)
            self.assertIsNone(calls[-1]["selection"])
            for bad in (["--sample", "0.1"], ["--salt", "x"], ["--sample", "0", "--salt", "x"],
                        ["--shard", "2/2"], ["--shard", "0/2", "--sample", "0.1", "--salt", "x"],
                        ["--code-cap", "5"], ["--changed-since", "auto"]):
                with self.subTest(bad=bad), self.assertRaises(SystemExit) as e:
                    quiet(fuzz.main, base + bad)
                self.assertEqual(e.exception.code, 2)


FAKE_FMT = r"""
import re, sys
args = sys.argv[1:]
def norm(t):
    t = t.replace("\r\n", "\n")
    lines = [re.sub(r" +([)\],:])", r"\1", re.sub(r"([(\[]) +", r"\1", re.sub(r"[ \t]+", " ", l.strip())))
             for l in t.split("\n")]
    if "KEEP_INDENT" in t:
        lines = [l.rstrip() for l in t.split("\n")]
    if "DROP" in t:
        lines = [l for l in lines if "drop" not in l]
    if "LOSE_COMMENT" in t:
        lines = [re.sub(r" *// lose.*", "", l) for l in lines]
    if "LOSE_DOC" in t:
        lines = [l for l in lines if not l.startswith("///")]
    for i in range(len(lines) - 1):  # the line break after it is lost (once: the joined line ends otherwise)
        if lines[i].endswith("JOIN_KEPT = 1"):
            lines[i:i + 2] = [lines[i] + " " + lines[i + 1]]
            break
    return "\n".join(l for l in lines if l).strip("\n") + "\n"
def code(t):
    return re.findall(r"\w+|[^\s\w]", re.sub(r"//[^\n]*", "", t))
def read(p):
    return open(p, encoding="utf-8", newline="").read()
if args[0] == "fmt":
    path = args[-1]
    t = read(path)
    if "PANIC" in t:
        sys.stderr.write("onsa: internal error: boom\n  = at crates/onsa_syntax/src/fmt.rs:1:1\n")
        sys.exit(101)
    if "REJECT" in t and re.search(r"[ ]$", t, re.M):
        sys.stderr.write(path + ":1:1: error[E0002]: no\n")
        sys.exit(2)
    if args[1] == "--check":
        sys.exit(0 if norm(t) == t else 1)
    open(path, "w", encoding="utf-8").write(norm(t) + (" " if "NOT_IDEMPOTENT" in t else ""))
elif args[0] == "diff":
    a, b = (read(p) for p in args[-2:])
    sys.exit(0 if code(a) == code(b) else 1)
elif args[0] == "check":
    # An E0401 for each `VERDICT` followed by two spaces or more (fmt makes it one: the verdict changes),
    # and for each line with `PLACE` (fmt moves the line: the place changes, not the code).
    t = read(args[-1])
    lines = t.split("\n")
    found = [(1, "the verdict") for _ in re.findall(r"VERDICT {2,}", t)]
    found += [(i + 1, f"at line {i + 1}") for i, l in enumerate(lines) if "PLACE" in l]
    for line, what in found:
        sys.stdout.write(f"{args[-1]}:{line}:1: error[E0401]: {what}\n")
    sys.exit(1 if found or "SILENT" in t else 0)
elif args[0] == "dump" and args[1] == "--levels":
    # one item; the output of fmt (written under b/) is deeper when the source says DEEPER
    t = read(args[-1])
    sys.stdout.write("2\n" if "DEEPER" in t and "/b/" in args[-1].replace("\\", "/") else "1\n")
elif args[0] == "dump":
    t = read(args[-1])
    sys.stdout.write(t.strip() if "CST_BAD" in t else t)
"""


class FmtProps(TempRepo):
    SOURCE = (
        "pub fn f(x: I32, ys: [I32; 2]) -> I32 { // head\n"
        "  let a = g(x, ys[0]) + -x // tail\n"
        "  let s = saw~(a, 1)\n"
        "  buf.push!(x)\n"
        "  let y = x + prev~(^y)\n"
        "  if !done {\n"
        "    \"a // not a comment, (x) [y]\"\n"
        "  } else {\n"
        "    'c'\n"
        "  }\n"
        "\n"
        "  return x *% 2\n"
        "}\n"
    )

    # The answer of the fake `onsa_cases --continuing` (the compiler's is
    # `onsa_tests::inventory::continuing_spellings`, tested there).
    CONTINUING = "+ - * / % == != < > <= >= && || & | ^ << >> +% -% *% +| -| *| ..< ..= = ->".split()
    SYMBOLS = "!== ... ..< ..= === != && *% ** *| +% ++ +| -% -- -> -| .. :: << <= == => >= >> ||".split()

    def cases_cmd(self, listed):
        """A fake `onsa_cases`: the cases `listed`, or the continuing symbols."""
        return (sys.executable, "-B", "-c",
                f"import json, sys; print(json.dumps({self.CONTINUING!r} if '--continuing' in sys.argv else "
                f"{self.SYMBOLS!r} if '--symbols' in sys.argv else {listed!r}))")

    def setUp(self):
        super().setUp()
        self.fake = self.repo.write("fake_onsa.py", FAKE_FMT)
        self.argv = [sys.executable, "-B", str(self.fake)]
        fmt_props.load_symbols(self.repo.root, self.cases_cmd([]))

    def go(self, prop="core", per_kind=3, cases=None, minimize=False):
        """Run the item over `tests/spec/a.onsa` (or `cases`: [(path, mode, syntax_errors)])."""
        cases = cases or [("tests/spec/a.onsa", "check", False)]
        listed = [{"path": p, "kind": "file", "mode": m, "files": [{"path": p, "syntax_errors": s}]}
                  for p, m, s in cases]
        cmd = self.cases_cmd(listed)
        lines = []
        code = fmt_props.run(self.repo.root, self.argv, prop, per_kind, "t", 2, cmd, out=lines.append,
                             minimize=minimize)
        return code, "\n".join(lines)

    def gaps(self, text):
        """[(token, gap before the next token: none / space / newline, next token)] of the code tokens."""
        toks = [t for t in fmt_props.tokenize(text) if t.kind == "code"]
        out = []
        for a, b in zip(toks, toks[1:]):
            gap = text[a.end:b.start]
            gap = re.sub(r"//[^\n]*", "", gap)
            out.append((a.text, "newline" if "\n" in gap else "space" if gap else "none", b.text))
        return out

    def test_tokenize(self):
        toks = fmt_props.tokenize('let s = "a // b" // c\nx->y..=z \'"\' +%')
        self.assertEqual(
            [(t.kind, t.text) for t in toks],
            [("code", "let"), ("code", "s"), ("code", "="), ("code", '"a // b"'), ("comment", "// c"), ("nl", "\n"),
             ("code", "x"), ("code", "->"), ("code", "y"), ("code", "..="), ("code", "z"), ("code", "'\"'"),
             ("code", "+%")],
        )
        # The range symbols are one token each (S-257).
        self.assertEqual([t.text for t in fmt_props.tokenize("0..<n 0..=n")], ["0", "..<", "n", "0", "..=", "n"])

    def test_perturbations_keep_the_places_where_whitespace_means_something(self):
        # C-118: no space before a postfix `(` / `[`, around `~` `!` `^` and the prefix `-`; no newline
        # removed, none added before `{` / `else`, nor before an attached `(` / `[`
        before = self.gaps(self.SOURCE)
        comments = [t.text for t in fmt_props.tokenize(self.SOURCE) if t.kind == "comment"]
        inputs = fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 20, "t")[1:]
        # The gaps (by the index of the token after them) that `break_places` counts inside an element.
        removable = {j for j, place, *_ in fmt_props.gap_places(self.SOURCE)[1] if place == "removable"}
        inside = fmt_props.INSIDE_SYMBOLS | fmt_props.INSIDE_KEYWORDS
        # The blanks are the space and the tab, and a line ends with LF or CR LF (§2.5, S-201): the
        # perturbations use both, and never a CR alone.
        self.assertTrue(any("\t" in p for _, _, p in inputs) and any("\r\n" in p for _, _, p in inputs))
        for label, kind, p in inputs:
            with self.subTest(label=label):
                after = self.gaps(p)
                self.assertEqual([(a, b) for a, _, b in after], [(a, b) for a, _, b in before])
                for i, ((a, g0, b), (_, g1, _)) in enumerate(zip(before, after)):
                    if g0 == "newline":
                        self.assertEqual(g1, "newline", (a, b))
                    if g1 == "newline" and g0 != "newline":
                        self.assertIn(kind, ("break", "continue", "inside", "mixed"))
                        self.assertNotIn(b, ("{", "else", "with"))
                        if b in ("(", "["):  # not a postfix one: after a list's opening or `,`, or a type after `:`
                            self.assertIn(a, ("(", "[", ",") if kind != "inside" else inside)
                        if kind == "inside":  # inside an element, before or after a token of §2.5's list
                            self.assertIn(i + 1, removable, (a, b))
                            self.assertTrue(a in inside or b in fmt_props.INSIDE_SYMBOLS, (a, b))
                        else:
                            self.assertTrue(a in ("(", "[", ",", "=") or a in fmt_props.continuing() or b == ".", (a, b))
                    if g0 == "none" and g1 == "space":
                        self.assertTrue(a in ("(", "[", ",") or b in (")", "]", ",", ":"), (a, b))
                self.assertNotRegex(p, r"\r(?!\n)")
                # the string, the character and the comments are untouched (no space after a comment)
                self.assertIn('"a // not a comment, (x) [y]"', p)
                kept = [t.text for t in fmt_props.tokenize(p) if t.kind == "comment" and "fmtprop" not in t.text]
                self.assertEqual(kept, comments)

    def test_the_line_breaks_inside_an_element(self):
        # `inside` (S-497, S-505): only in a gap that `break_places` counts `removable`, before and after `as`
        # `at` `:` `=>` `;`, and after a keyword of an expression followed by a blank (§2.5).
        text = (
            "struct P { @param(min: 0.0) x: F32, y: F32 }\n"
            "fn f[T: Num](x: T, ys: [T; 2]) -> T {\n"
            "  g(x as I64, saw~(a.b, -x)?, if c { 1 } else if d { 2 } else { 3 }, match v { 0 | 1 => 1, _ => 2 })\n"
            "  h(a + b, xs[0], f::[I32](x), fn(y: I32) -> I32 { y }, move m, inout n, if~ c { 1 } else { 2 },\n"
            "    s at clock, S { f: 1 }, !z, 0..<n, xs.at(0), t.as)\n"
            "}\n"
        )
        sites = [(a.text, b.text) for a, b in fmt_props.inside_sites(text)]
        self.assertEqual(sites, [
            ("min", ":"), (":", "0.0"), ("x", ":"), (":", "F32"), ("y", ":"), (":", "F32"),
            ("T", ":"), (":", "Num"), ("x", ":"), (":", "T"), ("ys", ":"), (":", "["), ("T", ";"), (";", "2"),
            ("x", "as"), ("as", "I64"), ("if", "c"), ("if", "d"), ("match", "v"),
            ("1", "=>"), ("=>", "1"), ("_", "=>"), ("=>", "2"),
            ("y", ":"), (":", "I32"), ("move", "m"), ("inout", "n"), ("s", "at"), ("at", "clock"), ("f", ":"), (":", "1"),
        ])
        # Never where §2.5 keeps a token on the line of its neighbour, though the gap is inside an element: a binary
        # operator, a range symbol, the `|` of a pattern, `->`, `?`, a postfix `(` / `[`, `~`, `::`, after `.` and a
        # prefix `!`, `else`, between `else` and `if`, `{`, `fn(`, `@name`, `if~`; and round a keyword after a `.`,
        # which is a name there (§2.2: `xs.at(0)`, `t.as`).
        code, places = fmt_props.gap_places(text)
        removable = {(code[j - 1].text, code[j].text) for j, place, *_ in places if place == "removable"}
        for pair in (("a", "+"), ("0", "..<"), ("0", "|"), (")", "->"), (")", "?"), ("xs", "["), ("]", "("),
                     ("saw", "~"), ("f", "::"), ("::", "["), (".", "b"), ("!", "z"), ("}", "else"), ("else", "if"),
                     ("c", "{"), ("fn", "("), ("@", "param"), ("if", "~"), (".", "at"), ("at", "("), (".", "as")):
            with self.subTest(pair=pair):
                self.assertIn(pair, removable)
                self.assertNotIn(pair, sites)
        # The inputs: line breaks (some of them blank lines) at the sites only; `breaks` finds those that stay, and
        # none in the source, where fmt has removed them all.
        inputs = [p for _, kind, p in fmt_props.inputs_of("tests/spec/a.onsa", text, 10, "t") if kind == "inside"]
        self.assertEqual(len(inputs), 10)
        self.assertTrue(any("\n\n" in p for p in inputs))
        old = {(a, b) for a, gap, b in self.gaps(text) if gap == "newline"}
        for p in inputs:
            with self.subTest(p=p):
                added = {(a, b) for a, gap, b in self.gaps(p) if gap == "newline"} - old
                self.assertTrue(added and added <= set(sites), added)
                problems = fmt_props.break_problems(p, p)
                self.assertTrue(problems and all(x.endswith("the line break inside an element stays") for x in problems))
                self.assertEqual(fmt_props.break_problems(p, text), [])
        # No site: no input.
        kinds = {k for _, k, _ in fmt_props.inputs_of("tests/spec/a.onsa", "fn f() {\n  g(a, b)\n}\n", 3, "t")}
        self.assertNotIn("inside", kinds)

    def test_inputs_are_the_same_for_the_same_tree(self):
        a = fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "1")
        self.assertEqual(a, fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "1"))
        self.assertNotEqual(a, fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "2"))
        self.assertEqual({k for _, k, _ in a[1:]}, set(fmt_props.KINDS))

    def test_strip(self):
        text = "a  // fmtprop-1\n  // fmtprop-2\nb // keep\n"
        self.assertEqual(fmt_props.strip_markers(text), "a\nb // keep\n")
        self.assertEqual(fmt_props.strip_comments("a // x\n// y\n\nb\n"), "a\n\nb\n")
        self.assertEqual(fmt_props.comment_texts("/// d\n//! m\n//// p\na // c\n"), (["//// p", "// c"], ["/// d", "//! m"]))
        self.assertEqual(fmt_props.unperturb("f(a,\n   b)  // c\n\n.g()\nx =\n 1\n"), "f(a, b).g()\nx = 1\n")

    def test_item_heads(self):
        text = "@repr(c)\npub struct P {\n  x: I32,\n}\n@inline pub fn f() {\n  let x = 1\n}\nconst K: Bool =\n  true\n"
        self.assertEqual(fmt_props.item_heads(text), [("struct", "P"), ("fn", "f"), ("const", "K")])

    def test_comment_problems(self):
        before = "fn f() -> I32 { // a\n  // b\n  return 1_0 // c\n}\n"
        # fmt's rewrites (return, the spelling of a number, the alignment) move no comment
        self.assertEqual(fmt_props.comment_problems(before, "fn f() -> I32 { // a\n  // b\n  10 // c\n}\n"), [])
        moved = fmt_props.comment_problems(before, "fn f() -> I32 {\n  // a\n  // b\n  10\n} // c\n")
        self.assertEqual(len(moved), 2, moved)
        self.assertIn("`// a`: was at a line end, now on its own line", moved[0])
        self.assertIn("`// c`: should be at the end of line 4 `10`, is at the end of line 5 `}`", moved[1])
        # the same last tokens on another line: moved (the place counts, not the tokens)
        self.assertTrue(fmt_props.comment_problems("fn f() {\n  g(x) // c\n  h(y)\n}\n", "fn f() {\n  g(x)\n  h(y) // c\n}\n"))
        self.assertTrue(fmt_props.comment_problems("fn f() {\n  a\n  // c\n}\n", "fn f() {\n  // c\n  a\n}\n"))
        # a return in an arm (S-68) and a redundant parenthesis are rewrites: not moves
        arm = "fn f(x: I32) -> I32 {\n  match x {\n    1 => return 2, // c\n    _ => 3,\n  }\n}\n"
        self.assertEqual(fmt_props.comment_problems(arm, arm.replace("return ", "")), [])
        paren = "fn f() {\n  if (a) { // c\n    b\n  }\n}\n"
        self.assertEqual(fmt_props.comment_problems(paren, paren.replace("(a)", "a")), [])
        # an empty body that fmt joins keeps its comment at the end of the joined line
        joined = fmt_props.comment_problems("fn f() {\n  for i in r {\n  } // c\n}\n", "fn f() {\n  for i in r {} // c\n}\n")
        self.assertEqual(joined, [])

    def test_comment_problems_of_a_line_of_brackets_alone(self):
        def body(text):
            return "fn f() -> I32 {\n" + text + "}\n"

        # a line of a bracket, `return` or `move` alone has a counterpart (the pairing keeps them)
        kept = [
            ("  g(\n    a,\n  ) // c\n", None),
            ("  h(\n  ) // c\n", "  h() // c\n"),
            ("  g(\n    a,\n    // c\n  )\n", None),
            ("  let x = {\n    // c\n    return\n  }\n  x\n", None),
            ("  let t =\n    ( // c\n      a,\n    )\n", None),
        ]
        for before, after in kept:
            self.assertEqual(fmt_props.comment_problems(body(before), body(after or before)), [], before)
        attribute = "@fp(relaxed\n)  // c\nfn f() -> F32 {\n  1.0\n}\n"
        self.assertEqual(fmt_props.comment_problems(attribute, attribute.replace("relaxed\n)  ", "relaxed) ")), [])
        # a comment moved away from such a line is still caught
        moved = [
            ("  g(\n    a,\n  ) // c\n", "  g(\n    a, // c\n  )\n", "should be at the end of line 4 `)`"),
            ("  g(\n    a,\n    // c\n  )\n", "  g(\n    a, // c\n  )\n", "was on its own line, now at a line end"),
            ("  g(\n    a,\n    // c\n  )\n", "  g(\n    a,\n  )\n  // c\n", "should be before line 4 `)`"),
            ("  let x = {\n    // c\n    return\n  }\n  x\n", "  let x = {\n    return\n    // c\n  }\n  x\n",
             "should be before line 3 `return`"),
            ("  h( // c\n    a,\n  )\n", "  h(\n    a, // c\n  )\n", "should be at the end of line 2 `h (`"),
        ]
        for before, after, want in moved:
            problems = fmt_props.comment_problems(body(before), body(after))
            self.assertEqual(len(problems), 1, problems)
            self.assertIn(want, problems[0])

    def test_comment_problems_of_s528_and_s529(self):
        def body(text):
            return "fn f() -> I32 {\n" + text + "}\n"

        # S-528: a comment after a closing bracket that fmt moves to a line of its own goes with it, `)` as `]`
        # and `}`; S-529: the comment of a line of a `,` alone stays as a line of a comment in its place
        kept = [
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  ) // c\n  x\n"),
            ("  [\n    1,\n    2]  // c\n", "  [\n    1,\n    2,\n  ] // c\n"),
            ("  if c {\n    a\n    b }  // c\n  x\n", "  if c {\n    a\n    b\n  } // c\n  x\n"),
            ("  g(\n    1\n    , // c2\n    2\n  )\n", "  g(\n    1,\n    // c2\n    2,\n  )\n"),
            ("  g(\n    1 // c1\n    , // c2\n    2\n  )\n", "  g(\n    1, // c1\n    // c2\n    2,\n  )\n"),
            ("  g(\n    1 // c38\n    // c\n    , // c39\n    2\n  )\n",
             "  g(\n    1, // c38\n    // c\n    // c39\n    2,\n  )\n"),
            ("  [\n    1\n    , // c\n  ]\n", "  [\n    1,\n    // c\n  ]\n"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  let xs = [1, // c1\n            // c2\n            2]\n  1\n"),
        ]
        for before, after in kept:
            self.assertEqual(fmt_props.comment_problems(body(before), body(after)), [], before)
        # a comment moved away from those places is still caught
        moved = [
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  )\n  x // c\n", "should be at the end of line 5 `)`"),
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  )\n  // c\n  x\n", "was at a line end"),
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a, // c\n    b,\n  )\n  x\n", "should be at the end of line 5 `)`"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  let xs = [1, // c1\n            2] // c2\n  1\n",
             "was on its own line, now at a line end"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  // c2\n  let xs = [1, // c1\n            2]\n  1\n",
             "should be before line 4 `2 ]`"),
            ("  [\n    1\n    , // c\n  ]\n", "  [\n    1,\n  ]\n  // c\n", "should be before line 4 `]`"),
        ]
        for before, after, want in moved:
            problems = fmt_props.comment_problems(body(before), body(after))
            self.assertEqual(len(problems), 1, problems)
            self.assertIn(want, problems[0])

    def test_run(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let x = g(a, b) // c\n  x\n}\n")
        code, text = self.go()
        self.assertEqual(code, 0, text)
        self.assertIn("no failure", text)
        code, text = self.go("cst")
        self.assertEqual(code, 0, text)
        for marker, failure in (
            ("let x = g(a, b) // DROP\n  drop(x)", "FAIL ast: tests/spec/a.onsa [source]"),  # not the same program
            ("let KEEP_INDENT = g(a, b)", "FAIL convergence: tests/spec/a.onsa [space#"),  # no normal form
            ("let x = g(a, b) // REJECT", "FAIL rejected: tests/spec/a.onsa ["),  # a perturbed input refused
            ("let x = g(a, b) // NOT_IDEMPOTENT", "FAIL idempotence: tests/spec/a.onsa [source]"),
            ("let x = g(a, b) // lose LOSE_COMMENT", "FAIL comment-text: tests/spec/a.onsa [source]: comment: 1 lost"),
            ("/// d LOSE_DOC\n  let x = 1", "FAIL docs: tests/spec/a.onsa [source]: doc comment: 1 lost"),
            ("let DEEPER = g(a, b)", "FAIL depth: tests/spec/a.onsa [source]: item 1: 1 levels before fmt, 2 after"),
            # A rewrite that changes what `onsa check` says (spec §18.2, W3-12/b2 3).
            ("let VERDICT  = g(a, b)",
             "FAIL meaning: tests/spec/a.onsa [source]: onsa check before fmt: exit 1, E0401; after fmt: exit 0, "
             "no diagnostic"),
            # A verdict of 1 with no diagnostic the item reads (another form of the output) fails, not passes.
            ("let SILENT = g(a, b)",
             "FAIL meaning: tests/spec/a.onsa [source]: onsa check ended with 1 and printed no diagnostic"),
            # A line break between two statements, and a blank line between two elements, that fmt lost.
            ("let JOIN_KEPT = 1",
             "FAIL breaks: tests/spec/a.onsa [source]: line 3, before `x` (line): the line break of the writer is gone"),
            ("let y = g(a,\n\n    b)",
             "FAIL breaks: tests/spec/a.onsa [source]: line 4, before `b` (element): the blank line between the elements "
             "is gone"),
        ):
            with self.subTest(marker=marker):
                self.repo.write("tests/spec/a.onsa", f"fn f() {{\n  {marker}\n  x\n}}\n")
                code, text = self.go()
                self.assertEqual(code, 1, text)
                self.assertIn(failure, text)
        self.assertFalse((self.repo.root / "tests" / "spec" / "a.onsa").read_text().count("fmtprop"))

    def test_the_meaning_compares_the_exit_code_and_the_codes_alone(self):
        # fmt moves the line of the diagnostic (it drops the blank lines): its place and its text change,
        # its code does not, so the meaning holds. The fake `check` of a file fmt does not change is not asked.
        self.repo.write("tests/spec/a.onsa", "fn f() {\n\n\n  let PLACE = 1\n  x\n}\n")
        code, text = self.go()
        self.assertNotIn("FAIL meaning", text)
        self.assertIn("inputs from 1 sources", text)

    def test_a_narrowed_run(self):
        # X-1: the cases of fmt always, a sample of one source per group (the first 3 parts of the
        # directory), each source's inputs as in the whole run (they depend on that source alone)
        paths = ["tests/spec/fmt/f.onsa"] + [f"tests/spec/q/{i}.onsa" for i in range(4)] + ["tests/spec/r/r.onsa"]
        for p in paths:
            self.repo.write(p, self.SOURCE)
        listed = [{"path": p, "kind": "file", "mode": "check", "files": [{"path": p, "syntax_errors": False}]}
                  for p in paths]
        whole = sum(len(fmt_props.inputs_of(p, self.SOURCE, 1, "t")) for p in paths)
        self.assertEqual(fmt_props.inputs_of(paths[1], self.SOURCE, 1, "t"),
                         fmt_props.inputs_of(paths[1], self.SOURCE, 1, "t"))
        for selection, picked, want in ((narrowing.Selection(sample=1e-9, salt="s"), 3,
                                         "picked 3 of 6 sources (always 1, sample 2)"),
                                        (narrowing.Selection(shard=(0, 1)), 6, "picked 6 of 6 sources (shard 0/1)"),
                                        (None, 6, "skipped); ")):
            with self.subTest(selection=selection):
                lines = []
                code = fmt_props.run(self.repo.root, self.argv, "cst", 1, "t", 2, self.cases_cmd(listed),
                                     out=lines.append, selection=selection)
                text = "\n".join(lines)
                self.assertEqual(code, 0, text)
                self.assertIn(f"{whole * picked // 6} inputs from {picked} sources", text)
                self.assertIn(want, text)

    def test_the_continuing_symbols_are_read_once_and_checked(self):
        # Read on the main thread from the injected command, before any
        # perturbation; none or an empty list is a usage error (exit 2).
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  x\n}\n")
        listed = [{"path": "tests/spec/a.onsa", "kind": "file", "mode": "check",
                   "files": [{"path": "tests/spec/a.onsa", "syntax_errors": False}]}]
        for answer in ("[]", "1"):
            with self.subTest(answer=answer):
                cmd = (sys.executable, "-B", "-c",
                       f"import json, sys; print({answer!r} if '--continuing' in sys.argv else json.dumps({listed!r}))")
                lines = []
                code = fmt_props.run(self.repo.root, self.argv, "core", 1, "t", 2, cmd, out=lines.append)
                self.assertEqual(code, 2, lines)
                self.assertIn("cannot read the symbols of the lexer", "\n".join(lines))
        fmt_props.load_symbols(self.repo.root, self.cases_cmd([]))
        self.assertEqual(fmt_props.continuing(), frozenset(self.CONTINUING))
        self.assertEqual(set(fmt_props.long_symbols()), set(self.SYMBOLS))

    def test_internal_and_cst_failures(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  PANIC\n}\n")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL internal: tests/spec/a.onsa [source]: fmt: internal|crates/onsa_syntax/src/fmt.rs|boom", text)
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  CST_BAD\n}\n")
        code, text = self.go("cst")
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL cst: tests/spec/a.onsa [source]: the output is not the source", text)

    def test_minimize(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let a = 1\n  PANIC\n  let b = 2\n}\n")
        code, text = self.go(per_kind=0, minimize=True)
        self.assertEqual(code, 1, text)
        saved = next((self.repo.root / "target" / "fmt_props" / "fail" / "core").glob("*.onsa"))
        self.assertEqual(saved.read_text(), "PANIC")
        # a refused input shrinks while the input without the perturbation is still read
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let a = 1\n  REJECT\n  let b = 2\n}\n")
        code, text = self.go(per_kind=1, minimize=True)
        self.assertEqual(code, 1, text)
        small = [p.read_text() for p in (self.repo.root / "target" / "fmt_props" / "fail" / "core").glob("*.onsa")]
        self.assertTrue(small and all("REJECT" in s and len(s) < 20 for s in small), small)

    def test_which_sources_may_be_unread(self):
        refused = "fn f() {\n  REJECT x \n}\n"
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  x\n}\n")
        self.repo.write("tests/spec/b.onsa", refused)
        # a file with a syntax diagnostic, a fragment of mode none, a pending case: skipped
        for mode, syntax, listed in (("check", True, False), ("none", False, False), ("check", False, True)):
            with self.subTest(mode=mode, syntax=syntax, listed=listed):
                self.repo.write("tests/pending.toml", entry("test-case", "tests/spec/b.onsa") if listed else "")
                code, text = self.go(cases=[("tests/spec/a.onsa", "check", False), ("tests/spec/b.onsa", mode, syntax)])
                self.assertEqual(code, 0, text)
                self.assertIn("1 that fmt may not read, skipped", text)
        # any other refusal fails
        self.repo.write("tests/pending.toml", entry("test-case", "tests/spec/b.onsa::t"))
        code, text = self.go(cases=[("tests/spec/a.onsa", "check", False), ("tests/spec/b.onsa", "check", False)])
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL unread: tests/spec/b.onsa [source]", text)
        # nothing ran: a failure
        self.repo.write("tests/pending.toml", "")
        code, text = self.go(cases=[("tests/spec/b.onsa", "none", False)])
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL no source ran", text)

    def test_std_and_examples_are_sources(self):
        self.repo.write("std/core/m.onsa", "fn f() {}\n")
        self.repo.write("examples/e/x.onsa", "fn g() {}\n")
        self.repo.write("examples/e/onsa.toml", "")
        self.repo.write("examples/e/target/out.onsa", "built")
        cmd = (sys.executable, "-B", "-c", "print('[]')")
        paths = [s.path for s in fmt_props.sources(self.repo.root, cmd)]
        self.assertEqual(paths, ["std/core/m.onsa", "examples/e/x.onsa"])

    def test_the_places_of_the_line_breaks(self):
        # Read on the text: the brackets, the elements, the attributes, the comments (`docs/onsa-tools.md` §3.2).
        text = ("@repr(c)\nstruct P { x: F32 }\nfn f() {\n  two(a, // c\n    b +\n    g(x\n    as F64))\n"
                "  match a {\n    0 =>\n      1,\n  }\n}\n")
        places = [(key, place, nl) for key, place, nl, _, _, _ in fmt_props.break_places(text)]
        self.assertEqual(places, [
            ("repr", "line", False), ("(", "line", False), ("c", "open", False), (")", None, False),
            ("struct", None, True), ("P", "line", False), ("{", "line", False), ("x", "open", False),
            (":", "removable", False), ("F32", "removable", False), ("}", None, False),
            ("fn", "line", True), ("f", "line", False), ("(", "line", False), (")", None, False), ("{", "line", False),
            ("two", None, True), ("(", "line", False), ("a", "open", False), ("b", "element", True),
            ("+", "removable", False), ("g", "continue", True), ("(", "removable", False), ("x", "open", False),
            ("as", "removable", True), ("F64", "removable", False), (")", None, False), (")", None, False),
            ("match", "line", True), ("a", "line", False), ("{", "line", False), ("#", "open", True),
            ("=>", "removable", False), ("#", "removable", True), ("}", None, True), ("}", None, True),
        ])

    def test_break_problems(self):
        body = lambda *lines: "fn f() {\n" + "".join(f"  {line}\n" for line in lines) + "}\n"
        for before, after, want in (
            # Kept: between statements, between elements (and the blank line there), after the opening bracket,
            # at a continuation; added there: a failure too.
            (body("let a = 1", "a"), body("let a = 1 a"), ["line 3, before `a` (line): the line break of the "
                                                           "writer is gone"]),
            (body("two(a,", "    b)"), body("two(a, b)"), ["line 3, before `b` (element): the line break of the "
                                                         "writer is gone"]),
            (body("two(a, b)"), body("two(a,", "    b)"), ["line 2, before `b` (element): the line break of the "
                                                          "writer is added"]),
            (body("two(a,", "", "    b)"), body("two(a,", "    b)"), ["line 4, before `b` (element): the blank line "
                                                                     "between the elements is gone"]),
            (body("two(", "    a, b,", "  )"), body("two(a, b)"), ["line 3, before `a` (open): the line break of the "
                                                                   "writer is gone"]),
            (body("two(a +", "    b, c)"), body("two(a + b, c)"), ["line 3, before `b` (continue): the line break of "
                                                                   "the writer is gone"]),
            # Removed: inside an element (S-497, S-505); one that stays is a failure.
            (body("g(x", "    as F64)"), body("g(x as F64)"), []),
            (body("g(x", "    as F64)"), body("g(x", "    as F64)"), ["line 3, before `as` (removable): the line "
                                                                       "break inside an element stays"]),
            (body("let s = S { f", "    : a }"), body("let s = S { f: a }"), []),
            # Not counted: what fmt adds or removes by the form, round attributes and the rewrites of §3.3.
            ("@repr(c) struct P { x: F32 }\n", "@repr(c)\nstruct P { x: F32 }\n", []),
            ("flow g() {\n  @mem(bulk)\n  let d = 1\n}\n", "flow g() {\n  @mem(bulk) let d = 1\n}\n", []),
            ("fn h() { g(a, b\n) }\n", "fn h() {\n  g(a, b)\n}\n", []),
            (body("two(a", "    , b)"), body("two(a,", "    b)"), []),
            (body("two(a // c", "    , b)"), body("two(a, // c", "    b)"), []),
            ("fn f() -> I32 {\n  return 1\n}\n", "fn f() -> I32 {\n  1\n}\n", []),
            # Another token changed: said, and the gaps round it are not judged.
            (body("g(x", "    as F64)"), body("g(y", "    as F64)"), ["token (but `,` and `return`) #7: 'x' became 'y'"]),
        ):
            with self.subTest(before=before, after=after):
                self.assertEqual(fmt_props.break_problems(before, after), want)



class Narrowing(unittest.TestCase):
    """tools/narrowing.py (X-1): the seeds of a narrowed run, the shards, the base binaries."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve() / "main"  # git names /private/var
        self.root.mkdir()
        git_in(self.root, "init", "-q")
        for rel, text in {"tests/spec/a/x.onsa": "// E0013\n", "tests/spec/a/y.onsa": "y\n",
                          "crates/c.rs": "// E0001\nfn c() {}\n", "docs/d.md": "d\n"}.items():
            self.write(rel, text)
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        self.full = git_in(self.root, "rev-parse", "HEAD").strip()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def change(self):
        """A WIP commit and changes on top of dev: what a worktree holds."""
        self.write("crates/c2.rs", "// E0007\n")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "WIP")
        self.write("crates/c.rs", "// E0002\nfn c() {}\n")  # E0001 removed, E0002 added
        self.write("docs/d.md", "E0003\n")  # docs/ and tests/ name no code
        self.write("tests/spec/a/y.onsa", "y // E0004\n")
        self.write("tests/spec/b/é.onsa", "// E0006\n")  # untracked, a name outside ASCII
        self.write("crates/new.rs", "// E0005\n")  # untracked: its codes count
        self.write("tools/test_t.py", "E0008\n")  # tools/: the self-tests write codes as data (X-1 U2)
        (self.root / "crates/blob.bin").write_bytes(b"\xff\xfe")  # untracked, not text: no code

    def test_changed_paths_and_codes(self):
        self.change()
        self.assertEqual(narrowing.merge_base(self.root), self.full)
        self.assertEqual(narrowing.changed_paths(self.root, self.full),
                         {"crates/c2.rs", "crates/c.rs", "docs/d.md", "tests/spec/a/y.onsa", "tests/spec/b/é.onsa",
                          "crates/new.rs", "crates/blob.bin", "tools/test_t.py"})
        self.assertEqual(narrowing.diff_codes(self.root, self.full), {"E0001", "E0002", "E0005", "E0007"})
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "tracked")
        self.write("tools/test_t.py", "E0009\n")  # a tracked file of tools/: still no code
        self.assertEqual(narrowing.diff_codes(self.root, self.full), {"E0001", "E0002", "E0005", "E0007"})
        with self.assertRaises(narrowing.NarrowError):
            narrowing.changed_paths(self.root, "no-such-commit")

    def test_pick(self):
        self.change()
        self.write("crates/c.rs", "// E0002 E0005 E0007\n")
        seeds = ([("tests/spec/a/y.onsa", "E0002"), ("tests/spec/b/é.onsa", "")]
                 + [(f"tests/spec/c/{i}.onsa", "E0002" if i < 5 else "E0005" if i < 6 else "E0007 E0005")
                    for i in range(8)]
                 + [(f"tests/spec/fmt/{i}.onsa", "") for i in range(3)])
        # the codes with the fewest seeds first: E0007 (2), E0005 (3 with E0007's), then E0002 (5 more,
        # 8 in all) would pass the cap 6: it and the codes after it are left out (y.onsa is in the diff)
        sel = narrowing.Selection(changed_since=self.full, code_cap=6)
        picked = narrowing.pick(seeds, sel, self.root, always=("tests/spec/fmt",))
        self.assertEqual(picked.counts, {"diff": 2, "codes": 3, "always": 3})
        self.assertEqual(picked.note, "codes over the cap 6 left to the sample: E0002")
        self.assertEqual(picked.describe(len(seeds)), "8 of 13 seeds (diff 2, codes 3, always 3; "
                                                       "codes over the cap 6 left to the sample: E0002)")
        # the cap holds them all: no note
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=8), self.root)
        self.assertEqual((picked.counts, picked.note), ({"diff": 2, "codes": 8}, ""))
        # the cap holds none: the codes left out are named
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=0), self.root)
        self.assertEqual(picked.counts, {"diff": 2, "codes": 0})
        self.assertIn("E0002 E0005 E0007", picked.note)
        # a sample is added after the rest
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=0, sample=1.0,
                                                           salt="s"), self.root)
        self.assertEqual((picked.counts, len(picked.paths)), ({"diff": 2, "codes": 0, "sample": 11}, 13))

    def test_sample(self):
        paths = [f"tests/spec/{d}/{i}.onsa" for d in ("a", "b", "c") for i in range(200)] + ["tests/spec/d/x/1.onsa",
                                                                                            "tests/spec/d/y/2.onsa"]
        a = narrowing.sampled(paths, 0.1, "W4-01")
        self.assertEqual(a, narrowing.sampled(list(reversed(paths)), 0.1, "W4-01"))  # the same salt: the same
        self.assertNotEqual(a, narrowing.sampled(paths, 0.1, "W4-02"))
        self.assertTrue(40 < len(a) < 90, len(a))
        # at least one of each group (the first 3 parts of the directory): tests/spec/d/x and /y are one group
        self.assertEqual(narrowing.group("tests/spec/d/x/1.onsa"), "tests/spec/d")
        few = narrowing.sampled(paths, 1e-9, "W4-01")
        self.assertEqual(sorted(narrowing.group(p) for p in few), [f"tests/spec/{d}" for d in "abcd"])
        self.assertEqual(narrowing.sampled(paths, 1.0, "x"), set(paths))

    def test_shards_partition_the_whole(self):
        paths = [f"tests/spec/{i}.onsa" for i in range(300)]
        for k in (1, 2, 3):
            parts = [{p for p in paths if narrowing.in_shard(p, (i, k))} for i in range(k)]
            self.assertEqual(set().union(*parts), set(paths))
            self.assertEqual(sum(map(len, parts)), len(paths))
            self.assertTrue(all(parts), parts)
        picked = narrowing.pick([(p, "") for p in paths], narrowing.Selection(shard=(1, 3)), None,
                                always=("tests",))  # a shard has no directory always in
        self.assertEqual(picked.paths, {p for p in paths if narrowing.in_shard(p, (1, 3))})

    def make_base(self, commit=None, tools=("onsa", "onsa_cases")):
        d = self.root / "target" / "base" / self.full[:7]
        d.mkdir(parents=True, exist_ok=True)
        if commit is not None:
            (d / "COMMIT").write_text(commit + "\n")
        for t in tools:
            (d / t).write_text("#!/bin/sh\nexit 0\n")
            (d / t).chmod(0o755)
        return d

    def test_resolve_base(self):
        self.assertIsNone(narrowing.resolve_base(self.root, "none"))
        self.assertIn("COMMIT", narrowing.resolve_base(self.root, "auto"))
        d = self.make_base(self.full)
        self.change()
        base = narrowing.resolve_base(self.root, "auto")
        self.assertEqual(base, narrowing.Base(self.full[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),)))
        # a short COMMIT of 7 characters or more is a prefix of the merge base
        self.make_base(self.full[:7])
        self.assertIsInstance(narrowing.resolve_base(self.root, "auto"), narrowing.Base)
        for wrong in (self.full[:6], "0" * 40):
            self.make_base(wrong)
            self.assertIn("not the merge base", narrowing.resolve_base(self.root, "auto"))
        self.make_base(self.full)
        (d / "onsa_cases").unlink()
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), f"no {d / 'onsa_cases'}")
        self.make_base(self.full)
        (d / "onsa").chmod(0o644)
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), f"no {d / 'onsa'}")
        (d / "onsa").chmod(0o755)
        # a directory named: its two tools, named by COMMIT
        self.assertEqual(narrowing.resolve_base(self.root, str(d)).commit, self.full[:7])
        # from a worktree: the main tree's target/base
        wt = Path(self.tmp.name) / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        self.assertEqual(narrowing.resolve_base(wt, "auto"), base)
        # no dev: unknown; not a git work tree: unknown
        git_in(self.root, "branch", "-D", "dev")
        self.assertIn("no merge base of HEAD and dev", narrowing.resolve_base(self.root, "auto"))
        self.assertIn("no merge base", narrowing.resolve_base(Path(self.tmp.name), "auto"))

    def test_selection(self):
        def parse(*argv):
            ap = argparse.ArgumentParser()
            ap.add_argument("--root", type=Path, default=self.root)
            narrowing.add_arguments(ap)
            return quiet(narrowing.parse, ap, list(argv))[1]

        self.assertIsNone(parse())
        self.assertEqual(parse("--changed-since", "auto"), narrowing.Selection(changed_since=self.full))
        self.assertEqual(parse("--changed-since", "HEAD", "--code-cap", "5", "--sample", "0.5", "--salt", "s"),
                         narrowing.Selection(self.full, 5, 0.5, "s"))
        self.assertTrue(parse("--sample", "0.5", "--salt", "s").narrowed)
        self.assertFalse(parse("--shard", "0/2").narrowed)
        for bad in (["--changed-since", "nope"], ["--code-cap", "-1", "--changed-since", "auto"]):
            with self.subTest(bad=bad), self.assertRaises(SystemExit) as e:
                parse(*bad)
            self.assertEqual(e.exception.code, 2)


class Keywords(unittest.TestCase):
    """tools/keywords.py: the lexer's keywords against §2.2 (W3-02/b 12)."""

    SPEC = "# s\n## 2. 字句\n### 2.2 キーワード\n\n```\nfn let\nat clock\n```\n\n### 2.3 次\n"

    def test_the_block_of_2_2(self):
        self.assertEqual(keywords.spec_keywords(self.SPEC), ["fn", "let", "at", "clock"])
        with self.assertRaises(repo.RepoError):
            keywords.spec_keywords("# s\n### 2.2 キーワード\n\nno block\n")

    def test_differences_and_the_list(self):
        diffs = keywords.differences(["fn", "let", "at", "clock"], ["fn", "let", "loop"])
        self.assertEqual(sorted(diffs), ["at", "clock", "loop"])
        e = types.SimpleNamespace(until="W3-04")
        pend, problems = keywords.apply_list(diffs, {"at": e, "clock": e, "fn": e})
        self.assertEqual(len(pend), 2)
        self.assertTrue(any(p.startswith("keywords/loop:") for p in problems), problems)
        self.assertTrue(any(p.startswith("keywords/fn:") and "remove the entry" in p for p in problems), problems)
        self.assertEqual(len(problems), 2)


import signal  # noqa: E402

import bg  # noqa: E402
import ignores  # noqa: E402
import take  # noqa: E402

RUST = '''\
//! A comment that names `#[ignore]` and `#[ignore = "x"]`.
const S: &str = "#[ignore] in a string";

macro_rules! out {
    ($($t:tt)*) => { println!($($t)*) };
}

#[test]
#[ignore = "W3-11 U3c: a \\"quoted\\" reason"]
fn direct_with_reason() {}

#[test]
/// A doc comment.
#[ignore]
fn direct_bare() {}

#[test]
fn not_ignored() {}

macro_rules! one {
    ($name:ident, $v:expr) => {
        #[test]
        fn $name() {}
    };
    ($name:ident, $v:expr, $why:literal) => {
        #[test]
        #[ignore = $why]
        fn $name() {}
    };
}

one!(one_plain, 1);
one!(
    one_multi,
    2,
    "W4-02"
);
one!(
    one_multi_plain,
    3
);

macro_rules! two {
    ($a:ident, $b:ident) => {
        #[test]
        fn $a() {}
        #[test]
        fn $b() {}
    };
    ($a:ident, $b:ident, second: $w:expr) => {
        #[test]
        fn $a() {}
        #[test]
        #[ignore = $w]
        fn $b() {}
    };
    ($a:ident, $b:ident, $w:expr) => {
        #[test]
        #[ignore = $w]
        fn $a() {}
        #[test]
        #[ignore = $w]
        fn $b() {}
    };
}

two!(both_a, both_b, "W3-04");
'''


class Ignores(unittest.TestCase):
    """tools/ignores.py: the ignored tests of the Rust sources, and taking the marks off and on."""

    def marks(self, text):
        tests, problems = ignores.scan(text)
        self.assertEqual(problems, [])
        return {t.name: (t.ignored, t.reason) for t in tests}

    def test_list(self):
        tests, problems = ignores.scan(RUST)
        self.assertEqual(problems, [])
        got = [(t.name, t.line, t.reason) for t in tests if t.ignored]
        line = RUST.splitlines().index
        self.assertEqual(sorted(got), sorted([
            ("direct_with_reason", line("fn direct_with_reason() {}") + 1, 'W3-11 U3c: a "quoted" reason'),
            ("direct_bare", line("fn direct_bare() {}") + 1, None), ("one_multi", line("    one_multi,") + 1, "W4-02"),
            ("both_a", line('two!(both_a, both_b, "W3-04");') + 1, "W3-04"),
            ("both_b", line('two!(both_a, both_b, "W3-04");') + 1, "W3-04"),
        ]))
        self.assertEqual({t.name for t in tests if not t.ignored}, {"not_ignored", "one_plain", "one_multi_plain"})

    def test_forms_not_read_are_named(self):
        cases = {
            "#[ignore]\nfn helper() {}\n": "1: an `#[ignore`",
            "#[test]\n#[ignore = \"a\"] // why\nfn t() {}\n": "2: an `#[ignore`",
            RUST + "const W: &str = \"x\";\none!(by_const, 4, W);\n": "the reason `W` is not a string literal",
            RUST + "two!(x, y, z, w);\n": "no arm of `two!` fits",
            "macro_rules! r {\n    ($($n:ident),*) => { $(#[test] #[ignore] fn $n() {})* };\n}\n": "the macro `r`",
        }
        for text, needle in cases.items():
            problems = ignores.scan(text)[1]
            self.assertTrue(any(needle in p for p in problems), (text, problems))

    def test_direct_edits_keep_the_rest(self):
        out = ignores.edit(RUST, "direct_bare", False)
        self.assertEqual(out, RUST.replace("/// A doc comment.\n#[ignore]\n", "/// A doc comment.\n"))
        out = ignores.edit(out, "not_ignored", True, "W5-08")
        self.assertIn('#[test]\n#[ignore = "W5-08"]\nfn not_ignored()', out)
        out = ignores.edit(out, "direct_with_reason", True, 'new "one"')
        self.assertIn('#[ignore = "new \\"one\\""]\nfn direct_with_reason()', out)
        self.assertEqual(self.marks(out)["direct_with_reason"], (True, 'new "one"'))
        self.assertEqual(ignores.edit(out, "direct_with_reason", True, 'new "one"'), out)

    def test_macro_edits(self):
        out = ignores.edit(RUST, "one_multi", False)
        self.assertEqual(out, RUST.replace('    2,\n    "W4-02"\n);', "    2\n);"))
        out = ignores.edit(out, "one_multi_plain", True, "W9-01")
        self.assertIn('    one_multi_plain,\n    3,\n    "W9-01"\n);', out)
        out = ignores.edit(out, "one_plain", True, "W9-02")
        self.assertIn('one!(one_plain, 1, "W9-02");', out)
        out = ignores.edit(out, "both_a", False)
        self.assertIn('two!(both_a, both_b, second: "W3-04");', out)
        self.assertEqual(self.marks(out)["both_b"], (True, "W3-04"))
        out = ignores.edit(out, "both_b", False)
        self.assertIn("two!(both_a, both_b);", out)
        with self.assertRaises(ignores.Unreadable):  # no arm ignores only the first test
            ignores.edit(out, "both_a", True, "W1-01")

    def test_cli_writes_all_or_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "t.rs"
            f.write_text(RUST, encoding="utf-8")
            self.assertEqual(quiet(ignores.main, ["remove", str(f), "direct_bare", "no_such_test"]), 1)
            self.assertEqual(f.read_text(encoding="utf-8"), RUST)
            self.assertEqual(quiet(ignores.main, ["remove", str(f), "direct_bare", "both_a", "both_b"]), 0)
            self.assertEqual({n for n, (i, _) in self.marks(f.read_text(encoding="utf-8")).items() if i},
                             {"direct_with_reason", "one_multi"})
            (Path(tmp) / "bad.rs").write_text("#[ignore]\nfn helper() {}\n", encoding="utf-8")
            self.assertEqual(quiet(ignores.main, ["list", tmp, "--reason", "W3-11"]), 1)

    def test_passing_against_cargo(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "crates" / "c" / "tests").mkdir(parents=True)
            (Path(tmp) / "crates" / "c" / "tests" / "t.rs").write_text(RUST, encoding="utf-8")
            out = "\n".join([
                "     Running tests/t.rs (target/debug/deps/t-0)", "test direct_with_reason ... ok",
                "test direct_bare ... FAILED", "test both_a ... ok", "test stray ... ok",
            ])
            done = subprocess.CompletedProcess([], 101, stdout=out)
            with mock.patch.object(ignores, "ROOT", Path(tmp)), mock.patch.object(ignores.subprocess, "run",
                                                                                   return_value=done) as run:
                buf = io.StringIO()
                with mock.patch.object(sys, "stdout", buf):
                    code = ignores.main(["passing", "-p", "c", "--reason", "W"])
            self.assertIn("--ignored", run.call_args.args[0])
            self.assertEqual(run.call_args.kwargs["timeout"], 540)
            lines = buf.getvalue().splitlines()
            self.assertEqual(code, 1)  # `stray` ran but the files do not show it
            self.assertTrue(any(x.startswith("pass\t") and "direct_with_reason" in x for x in lines), lines)
            self.assertTrue(any(x.startswith("not run\t") and "\tboth_b\t" in x for x in lines), lines)
            self.assertFalse(any("direct_bare" in x for x in lines), lines)  # no reason, so `--reason` leaves it out
            self.assertTrue(any("`stray`" in x for x in lines), lines)


class PendingEdit(TempRepo):
    """tools/pending.py list / remove / add: the other entries stay byte for byte, the list stays valid."""

    def setUp(self):
        super().setUp()
        self.text = ("# head\n\n" + entry("test-case", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
                     + "# group\n" + entry("diag-code", "E0812", ("R-23",), "W5-07")
                     + entry("gate", "c-header/x", ("S-34",), "T5-8").rstrip("\n") + "\n")
        self.repo.write("tests/pending.toml", self.text)

    def cmd(self, *args):
        return quiet(pending.main, [*args, "--root", str(self.repo.root)])

    def test_list(self):
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf):
            self.assertEqual(pending.main(["list", "--until", "W5", "--root", str(self.repo.root)]), 0)
        self.assertEqual(buf.getvalue(), "W5-07\tR-23\tdiag-code\tE0812\n")

    def test_remove(self):
        self.assertEqual(self.cmd("remove", "E0812", "c-header/x"), 0)
        self.assertEqual(self.repo.pending.read_text(encoding="utf-8"),
                         "# head\n\n" + entry("test-case", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08") + "# group\n")
        self.assertEqual(self.repo.validate(), [])
        self.assertEqual(self.cmd("remove", "tests/spec/ops/groups.onsa", "nothing"), 1)
        self.assertIn("tests/spec/ops/groups.onsa", self.repo.pending.read_text(encoding="utf-8"))

    def test_add(self):
        self.assertEqual(self.cmd("add", "--kind", "diag-code", "--target", "E0601", "--reasons", "S-45, R-23",
                                  "--until", "W3-07", "--note", 'a "note"'), 0)
        added = '\n[[pending]]\nkind = "diag-code"\ntarget = "E0601"\nreasons = ["S-45", "R-23"]\nuntil = "W3-07"\nnote = "a \\"note\\""\n'
        self.assertEqual(self.repo.pending.read_text(encoding="utf-8"), self.text + added)
        self.assertEqual(self.repo.validate(), [])
        self.assertEqual(self.cmd("add", "--kind", "diag-code", "--target", "E0602", "--reasons", "S-9",
                                  "--until", "W3-07", "--note", "n"), 1)
        self.assertEqual(self.cmd("add", "--kind", "diag-code", "--target", "E0601", "--reasons", "S-45",
                                  "--until", "W3-07", "--note", "n"), 1)  # the same target twice
        self.assertEqual(self.repo.pending.read_text(encoding="utf-8"), self.text + added)

    def test_a_table_of_another_shape_stops(self):
        odd = self.text.replace('reasons = ["R-23"]', 'reasons = [\n  "R-23",\n]')
        self.repo.write("tests/pending.toml", odd)
        self.assertEqual(self.cmd("remove", "c-header/x"), 1)
        self.assertEqual(self.repo.pending.read_text(encoding="utf-8"), odd)

    def test_the_check_is_unchanged(self):
        self.assertEqual(quiet(pending.main, ["--root", str(self.repo.root), "--gate-steps", "c-header"]), 0)


def git_in(tree, *args):
    return subprocess.run(["git", "-C", str(tree), "-c", "user.name=t", "-c", "user.email=t@t",
                           "-c", "commit.gpgsign=false", *args], capture_output=True, text=True, check=True).stdout


class Take(unittest.TestCase):
    """tools/take.py: a patch of a worktree with a WIP commit, changes and new files, applied to a busy tree."""

    LINES = "".join(f"{i}\n" for i in range(1, 10))

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = Path(self.tmp.name)
        self.main, self.wt, self.patch = t / "main", t / "wt", t / "p.patch"
        self.main.mkdir()
        git_in(self.main, "init", "-q")
        for name in ("a.txt", "b.txt", "c.txt"):
            (self.main / name).write_text(self.LINES)
        git_in(self.main, "add", "-A")
        git_in(self.main, "commit", "-qm", "base")
        self.base = git_in(self.main, "rev-parse", "HEAD").strip()
        git_in(self.main, "worktree", "add", "-q", "-b", "work", str(self.wt))
        (self.wt / "a.txt").write_text(self.LINES.replace("2\n", "two\n"))
        git_in(self.wt, "commit", "-qam", "WIP")
        (self.wt / "b.txt").write_text(self.LINES.replace("2\n", "two\n"))
        (self.wt / "n.rs").write_text("fn n() {}\n")
        (self.wt / "tests").mkdir()
        (self.wt / "tests" / "x.rs").write_text("a\nb\n")

    def tearDown(self):
        self.tmp.cleanup()

    def take(self, *args):
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf):
            code = take.main(list(map(str, args)))
        return code, buf.getvalue()

    def make_patch(self):
        code, out = self.take("patch", self.wt, self.base, self.patch, "--main", self.main)
        self.assertEqual(code, 0, out)
        return out

    def test_patch(self):
        out = self.make_patch()
        self.assertEqual(git_in(self.wt, "diff", "--cached", "--name-only"), "")
        self.assertIn("4 file(s), +5 -2; without the tests and the data: +1 -0", out)
        self.assertIn("n.rs  (new)", out)
        text = self.patch.read_text()
        self.assertIn("+two", text)
        self.assertIn("b/tests/x.rs", text)
        self.assertTrue(take.is_code("tools/take.py"))
        self.assertFalse(any(map(take.is_code, ("tools/test_gate.py", "crates/a/tests/t.rs", "crates/a/src/tests.rs",
                                                "crates/a/src/cst_tests.rs", "tests/pending.toml", "docs/x.md"))))
        other = git_in(self.main, "commit-tree", "-m", "x", git_in(self.main, "write-tree").strip()).strip()
        self.assertEqual(self.take("patch", self.wt, other, self.patch, "--main", self.main)[0], 1)

    RUST = "\n".join([
        "fn a() {}",
        "",
        "#[cfg(test)]",
        "#[allow(unused)]",
        "mod tests {",
        "    fn t<'a>(x: &'a str) {",
        '        let s = "fn f() {";',
        '        let r = r#"}"#;',
        "        let (c, d) = ('{', b\"}\");",
        "        /* } /* } */ } */ // }",
        "        assert_eq!(s.len(), 8);",
        "    }",
        "}",
        "",
    ])

    def test_the_test_modules_inside_a_rust_file_are_tests(self):
        # The braces in the strings, the character, the comments and the lifetime are not the block's.
        self.assertEqual(take.test_lines(self.RUST), set(range(3, 14)))
        (self.wt / "m.rs").write_text(self.RUST)
        git_in(self.wt, "add", "m.rs")
        git_in(self.wt, "commit", "-qm", "m")
        base = git_in(self.wt, "rev-parse", "HEAD").strip()
        (self.wt / "m.rs").write_text(self.RUST.replace("fn a() {}", "fn a() { b() }\nfn b() {}")
                                      .replace("s.len(), 8);", "s.len(), 9);\n        let e = \"{{\";")
                                      + "fn after() {}\n")
        code, out = self.take("patch", self.wt, base, self.patch, "--main", self.main)
        self.assertEqual(code, 0, out)
        # m.rs: +3 -1 of code (fn a, fn b, fn after) and +2 -1 in its test module; n.rs: +1.
        self.assertIn("without the tests and the data: +4 -1 (the test modules inside 1 file(s), +2 -1, left out)", out)

    def test_plain_with_a_change_in_the_same_file(self):
        self.make_patch()
        (self.main / "b.txt").write_text(self.LINES.replace("8\n", "eight\n"))
        (self.main / "c.txt").write_text("other\n")
        code, out = self.take("check", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertIn("applies: plain", out)
        self.assertIn("b.txt: uncommitted change (M)", out)
        self.assertNotIn("c.txt", out)
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertEqual((self.main / "b.txt").read_text(), self.LINES.replace("2\n", "two\n").replace("8\n", "eight\n"))
        self.assertEqual(git_in(self.main, "diff", "--cached", "--name-only"), "")
        code, out = self.take("apply", self.patch, "--to", self.main)  # a second time: nothing to do
        self.assertEqual((code, out.splitlines()[0]), (0, f"applies: {take.ALREADY}"))

    def test_three_way_after_the_main_tree_moved(self):
        (self.main / "a.txt").write_text(self.LINES.replace("5\n", "five\n"))
        git_in(self.main, "commit", "-qam", "moved")
        (self.main / "c.txt").write_text("other\n")
        out = self.make_patch()
        self.assertIn("of the patch: a.txt", out)
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 0, out)
        self.assertIn("applies: 3way", out)
        self.assertEqual((self.main / "a.txt").read_text(), self.LINES.replace("2\n", "two\n").replace("5\n", "five\n"))
        self.assertEqual(git_in(self.main, "diff", "--cached", "--name-only"), "")
        self.assertEqual((self.main / "c.txt").read_text(), "other\n")
        self.assertIn("?? n.rs", git_in(self.main, "status", "--porcelain"))

    def test_an_untracked_file_in_the_way(self):
        self.make_patch()
        (self.main / "n.rs").write_text("mine\n")
        code, out = self.take("apply", self.patch, "--to", self.main)
        self.assertEqual(code, 1)
        self.assertIn("n.rs: untracked, already there", out)
        self.assertEqual((self.main / "n.rs").read_text(), "mine\n")
        self.assertEqual((self.main / "b.txt").read_text(), self.LINES)


class Bg(unittest.TestCase):
    """tools/bg.py: a command in the background, waited for by its pid; nothing is left running."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dirs = []

    def tearDown(self):
        for d in self.dirs:
            quiet(bg.stop, d)
            pid = bg.read(d, "pid")
            self.assertFalse(pid and bg.alive(int(pid)), f"{d}: left running")
        self.tmp.cleanup()

    def bg(self, *args):
        r = subprocess.run([sys.executable, "-B", str(Path(bg.__file__)), *map(str, args)], capture_output=True,
                           text=True, timeout=60)
        return r.returncode, r.stdout

    def run_(self, name, *cmd):
        d = Path(self.tmp.name) / name
        self.dirs.append(d)
        self.assertEqual(self.bg("run", d, "--", *cmd)[0], 0)
        return d

    def test_exit_and_output(self):
        d = self.run_("short", "sh", "-c", "echo out; echo err >&2; exit 3")
        code, out = self.bg("wait", d, "--timeout", "30")
        self.assertEqual(code, 3, out)
        self.assertIn("exit 3", out)
        self.assertIn("| out\n  | err", out)
        self.assertIn("finished, exit 3", self.bg("status", d)[1])

    def test_timeout_stop_and_status(self):
        d = self.run_("long", "sleep", "30")
        self.assertEqual(self.bg("run", d, "--", "true")[0], 1)  # still running
        code, out = self.bg("wait", d, "--timeout", "0.3")
        self.assertEqual(code, bg.TIMEOUT_EXIT, out)
        self.assertIn("still running", out)
        self.assertIn(": running", self.bg("status", d)[1])
        self.assertEqual(self.bg("stop", d)[0], 0)
        self.assertIn("finished, exit SIGTERM", self.bg("status", d)[1])
        self.assertEqual(self.bg("wait", d)[0], 128 + signal.SIGTERM)
        self.assertEqual(self.bg("run", d, "--", "true")[0], 0)  # finished: the directory is free again
        self.assertEqual(self.bg("wait", d, "--timeout", "30")[0], 0)

    def test_a_lost_watcher(self):
        d = self.run_("lost", "sleep", "30")
        watcher, pid = int(bg.read(d, "watcher")), int(bg.read(d, "pid"))
        os.kill(watcher, signal.SIGKILL)
        deadline = time.monotonic() + 10
        while bg.alive(watcher) and time.monotonic() < deadline:
            time.sleep(0.05)
        code, out = self.bg("wait", d, "--timeout", "5")
        self.assertEqual(code, bg.LOST_EXIT, out)
        self.assertIn("lost", out)
        self.assertIn(": lost", self.bg("status", d)[1])
        self.assertEqual(self.bg("run", d, "--", "true")[0], 1)  # its command still runs
        self.assertEqual(self.bg("stop", d)[0], 0)
        self.assertFalse(bg.alive(pid))


class IgnoresStale(TempRepo):
    """tools/ignores.py stale (the gate item `ignores`, R-224): an ignore whose reason names a work done or unknown."""

    def stale(self, *argv):
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf), mock.patch.object(sys, "stderr", buf):
            code = ignores.main(["stale", "--root", str(self.repo.root), *argv])
        return code, buf.getvalue()

    def ignored(self, reason):
        return f'#[test]\n#[ignore = "{reason}"]\nfn t() {{}}\n'

    def check(self, reason, *argv):
        self.repo.write("crates/a/tests/t.rs", self.ignored(reason))
        return self.stale(*argv)

    def test_a_done_work_fails(self):
        for reason in ("W1-01", "W1-01 U2: why", "T1-1 (S-45)"):
            code, out = self.check(reason)
            self.assertEqual(code, 1, out)
            self.assertIn(f"crates/a/tests/t.rs:3\tt\t{reason}\n    the work {reason.split()[0]} is done", out)

    def test_a_work_not_done_passes(self):
        for reason in ("W3-07", "W3-08 U1: why", "T5-8", "W5-07"):
            code, out = self.check(reason)
            self.assertEqual(code, 0, out)
            self.assertIn("1 ignored test(s) in 1 file(s): 1 by a work, 0 for another reason", out)

    def test_an_id_not_in_the_tables_fails(self):
        # W9-99 is outside the table of §3; W3-071 is not W3-07
        for reason in ("W9-99", "W3-071: a typo", "T9-3"):
            code, out = self.check(reason)
            self.assertEqual(code, 1, out)
            self.assertIn("is no work of the tables", out)

    def test_the_works_of_a_stage_fail_at_its_end(self):
        self.repo.write("crates/a/tests/t.rs", self.ignored("W3-07 U1") + self.ignored("W5-07").replace("t()", "u()"))
        code, out = self.stale("--stage-end", "W3")
        self.assertEqual(code, 1, out)
        self.assertIn("the work W3-07 is of W3, which ends here", out)
        self.assertNotIn("W5-07", out)
        self.assertEqual(self.stale("--stage-end", "W5")[0], 1)
        self.assertEqual(self.stale("--stage-end", "W1")[0], 0)
        self.assertEqual(self.stale("--stage-end", "M9")[1].count("which ends here"), 2)  # the end of the first phase
        code, out = self.stale("--stage-end", "W99")
        self.assertEqual(code, 2, out)
        self.assertIn("unknown stage", out)

    def test_a_reason_without_an_id_passes_and_is_counted(self):
        self.repo.write("crates/a/tests/t.rs", RUST.replace("W3-11 U3c", "slow").replace("W4-02", "flaky")
                        .replace('"W3-04"', '"see W1-01"'))  # fmt: skip
        code, out = self.stale()
        self.assertEqual(code, 0, out)
        self.assertIn("5 ignored test(s) in 1 file(s): 0 by a work, 5 for another reason", out)

    def test_nothing_to_read_fails(self):
        code, out = self.stale()  # no crates directory
        self.assertEqual(code, 1, out)
        self.assertIn("no such file or directory", out)
        self.repo.write("crates/a/README.md", "")
        code, out = self.stale()
        self.assertEqual(code, 1, out)
        self.assertIn("no `.rs` file found", out)
        self.repo.write("crates/a/src/lib.rs", "")
        self.assertEqual(self.stale(), (0, "0 ignored test(s) in 1 file(s): 0 by a work, 0 for another reason\n"))

    def test_a_form_not_read_fails(self):
        self.repo.write("crates/a/src/lib.rs", "#[ignore]\nfn helper() {}\n")
        code, out = self.stale()
        self.assertEqual(code, 1, out)
        self.assertIn("an `#[ignore` of a form this tool does not read", out)

    def test_the_paths_and_a_reason_through_a_macro(self):
        # the reason argument of a macro arm, as `stop_case!` of syntax_units.rs (the ignores of R-224)
        f = self.repo.write("crates/a/tests/m.rs", RUST.replace('"W3-04"', '"W1-01"'))
        self.repo.write("crates/b/tests/t.rs", self.ignored("W1-01"))
        code, out = self.stale(str(f))
        self.assertEqual(code, 1, out)
        self.assertEqual(out.count("the work W1-01 is done"), 2)  # both_a and both_b
        self.assertIn("\tboth_a\t", out)
        self.assertNotIn("crates/b", out)
        self.assertIn("is no work of the tables", self.stale(str(f))[1])  # W3-11 and W4-02 are not in the tables



# The real `onsa_cases` from any directory: tools/default_inits.py runs it in the root it reads.
REAL_CASES = ("cargo", "run", "-q", "--manifest-path", str(repo.ROOT / "Cargo.toml"), "-p", "onsa_tests", "--bin",
              "onsa_cases", "--")  # fmt: skip
INIT_FLOW = "pub flow f(x: F32 at sample, b: Bool at sample, s: F32 at init) -> F32 at sample {{\n  {}\n}}\n"


class DefaultInits(unittest.TestCase):
    """tools/default_inits.py: the documents write the omitted `init` (S-539 (c3a))."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def docs(self, spec, tools="", std=None, example=None):
        """A spec of one block, the tools document, one file of `std/` and of `examples/`."""
        self.write(repo.SPEC, f"# s\n## 11. flow\n### 11.4 遅延\n\n本文の `prev~(^y, 0)` は読まない。\n\n```onsa\n{spec}```\n")
        self.write(default_inits.TOOLS_DOC, tools)
        self.write("std/a.onsa", std if std is not None else INIT_FLOW.format("prev~(x)"))
        self.write("examples/b.onsa", example if example is not None else INIT_FLOW.format("delay~(x, 4)"))

    def check(self, cmd=REAL_CASES):
        return default_inits.check(self.root, cmd)[0]

    def test_an_init_equal_to_the_default_fails(self):
        self.docs(
            INIT_FLOW.format("let y = prev~(x, 0.0)\n  y"),
            tools="# t\n\n```onsa\n" + INIT_FLOW.format("delay~(b, 3, false)") + "```\n",
            std=INIT_FLOW.format("vdelay~(x, x, 8, 0x0_0) + prev~(x, (0e3))"),
            example="// c\n" + INIT_FLOW.format("delay~(x, 4, -0) + prev~(x, 00.00)"),
        )
        problems = self.check()
        shown = sorted(p.split("  ")[0] for p in problems)
        self.assertEqual(
            shown,
            ["docs/onsa-tools.md:5", "examples/b.onsa:3", "examples/b.onsa:3", "onsa-lang-spec-0.3.md:9",
             "std/a.onsa:2", "std/a.onsa:2"],
            problems,
        )  # fmt: skip
        self.assertTrue(all("write the omitted form" in p for p in problems), problems)
        self.assertIn("`prev~` has the init `0.0`", "\n".join(problems))
        self.assertEqual(quiet(default_inits.main, [], self.root, REAL_CASES), 1)

    def test_the_omitted_form_and_other_values_pass(self):
        # the omitted form, values that are not 0, `-0.0` (not the default), a name, `true`; the text
        # outside the blocks names `prev~(^y, 0)` on purpose
        self.docs(
            INIT_FLOW.format("prev~(x) + prev~(x, 1.0) + prev~(x, -0.0) + delay~(x, 4, s) + vdelay~(x, x, 8, 0.5)"),
            tools="# t\n\n例の `prev~(^y, 0)`。\n",
            std=INIT_FLOW.format("delay~(b, 3, true)\n  x"),
        )
        problems, summary = default_inits.check(self.root, REAL_CASES)
        self.assertEqual(problems, [])
        self.assertIn("1 onsa-lang-spec-0.3.md blocks, 0 docs/onsa-tools.md blocks, 1 examples files, 1 std files; "
                      "7 delay calls", summary)  # fmt: skip
        self.assertEqual(quiet(default_inits.main, [], self.root, REAL_CASES), 0)

    def test_reading_nothing_fails(self):
        self.docs("fn f() {}\n", std="fn g() {}\n", example="fn h() {}\n")
        self.assertEqual([p for p in self.check() if "reading nothing" in p], [
            "no delay call in the documents; the check would pass reading nothing"])  # fmt: skip
        (self.root / "std" / "a.onsa").unlink()
        self.assertIn("no std files to read; the check would pass reading nothing", self.check())

    def test_a_source_the_compiler_cannot_read_fails(self):
        self.docs(INIT_FLOW.format("prev~(x)"))
        script = ("import json, sys; print(json.dumps([{'file': f, 'internal': 'boom'} for f in sys.argv[2:]]"
                  " + [{'file': 'other', 'calls': 1, 'hits': []}]))")  # fmt: skip
        problems = self.check((sys.executable, "-B", "-c", script))
        self.assertEqual(len([p for p in problems if "could not read it: boom" in p]), 3, problems)
        script = "import json; print(json.dumps([]))"
        problems = self.check((sys.executable, "-B", "-c", script))
        self.assertEqual(len([p for p in problems if "could not read it: no report" in p]), 3, problems)

    def test_a_fence_that_cannot_be_trusted_fails(self):
        self.docs(INIT_FLOW.format("prev~(x)"), tools="# t\n\n```Onsa\nprev~(x, 0.0)\n```\n")
        self.assertTrue(any(p.startswith("docs/onsa-tools.md:3") and "looks like onsa" in p for p in self.check()))

    def test_a_call_the_tree_does_not_hold_fails(self):
        # the item with a syntax error has no tree, nor has the spaced `prev ~(` (§2.6): the tokens count them
        broken = INIT_FLOW.format("let a = prev~(x, 0.0)\n  let b = )\n  a")
        self.docs(broken + INIT_FLOW.replace("flow f", "flow g").format("prev ~(x, 0.0)"))
        problems = self.check()
        self.assertEqual(problems, ["onsa-lang-spec-0.3.md:8  2 of its 2 delay calls are not in the tree (an item with "
                                    "a syntax error); their init is not checked"])  # fmt: skip
        # a file of std/ with a syntax error fails by itself too, also when the tree holds all its calls
        self.docs(INIT_FLOW.format("prev~(x)"), std=broken)
        problems = self.check()
        self.assertEqual(sorted(p.split("  ")[1].split(";")[0] for p in problems),
                         ["1 of its 1 delay calls are not in the tree (an item with a syntax error)",
                          "has a diagnostic of the syntax stage (`onsa check` shows it)"], problems)  # fmt: skip
        self.docs(INIT_FLOW.format("prev~(x)"), example="fn g() -> I32 { 1 + }\n" + INIT_FLOW.format("delay~(x, 4)"))
        self.assertEqual([p.split("  ")[0] for p in self.check()], ["examples/b.onsa:1"])

    def test_the_counts_agree_without_a_call_in_the_spec(self):
        # no delay call in the blocks of the spec, some in std/: nothing unread, so it passes
        self.docs("fn f() {}\n")
        problems, summary = default_inits.check(self.root, REAL_CASES)
        self.assertEqual(problems, [])
        self.assertTrue(summary.endswith("; 2 delay calls"), summary)


# A sentence of 100 characters, and others: a line of three is longer than docs.LONG.
S = "あ" * 99 + "。"
T = "い" * 99 + "。"
LONG_SENTENCE = "う" * 299 + "。"


class DocsTool(unittest.TestCase):
    """tools/docs.py (X-2 U1): `fmt`, `swaps`, `check`, and the documents they read."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def main(self, *argv):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main([*argv, "--root", str(self.root)])
        return code, out.getvalue()

    def fmt(self, text):
        new, wrapped, left = docs_tool.fmt_text(text)
        # idempotent: a second run changes nothing; the round trip gives the text back
        self.assertEqual(docs_tool.fmt_text(new)[:2], (new, []))
        return new.split("\n"), wrapped, left

    # ------------------------------------------------ fmt

    def test_fmt_breaks_after_a_sentence_and_packs_to_the_width(self):
        lines, wrapped, left = self.fmt("intro\n- " + S + S + T + "\nend")
        self.assertEqual(lines, ["intro", "- " + S + S, "  " + T, "end"])
        self.assertEqual((wrapped, left), ([2], []))

    def test_fmt_goes_on_at_the_indentation_of_the_item(self):
        cases = {
            "> " + S * 3: "> ",  # a quote
            "1. " + S * 3: "   ",  # a numbered item
            "  - " + S * 3: "    ",  # a nested item
            "    " + S * 3: "    ",  # a line that goes on an item
            S * 3: "",  # a paragraph
        }
        for line, cont in cases.items():
            lines, wrapped, _ = self.fmt(line)
            self.assertEqual(lines, [line[: len(line) - 100], cont + S], line[:4])
            self.assertEqual(wrapped, [1])

    def test_fmt_leaves_the_blocks_and_the_kept_lines(self):
        long = S * 3
        text = "\n".join([
            "+++", f'title = "{long}"', "+++",
            "```", long, "```", "  ~~~~ x", long, "  ~~~", long, "~~~~",
            f"| {long} |", f"# {long}", f"欠番: {long}", f"<!-- {long} -->", "<!--", long, "-->",
        ])  # fmt: skip
        new, wrapped, left = docs_tool.fmt_text(text)
        self.assertEqual((new, wrapped, left), (text, [], []))
        # a head field that does not close keeps the whole file (the check of the head fields reports it)
        self.assertEqual(docs_tool.fmt_text("+++\n" + long)[0], "+++\n" + long)

    def test_fmt_breaks_only_at_the_depth_0_outside_code_and_bold(self):
        for inner in ("（" + S * 2 + "）", "`" + S * 2 + "`", "`` a`b " + S * 2 + " ``", "**" + S * 2 + "**", "「" + S * 2 + "」"):
            lines, wrapped, left = self.fmt(inner + S)
            self.assertEqual((wrapped, left), ([], [(1, len(inner) + 100)]), inner[:4])
        # an escaped backtick opens no code span (the backtick after it has no partner); a closed bracket
        # comes back to the depth 0
        middle = "（あ。）" + "え" * 50 + "。"
        tail = "お`" + "お" * 97 + "。"
        lines, wrapped, _ = self.fmt("\\`" + S + middle + tail)
        self.assertEqual(lines, ["\\`" + S + middle, tail])

    def test_fmt_never_starts_a_line_like_a_block(self):
        for start in ("- x", "* x", "+ x", "> x", "| x", "# x", "```x", "~~~x", "<b>", "=== x", "___", "12. x", "3) x", " x"):
            piece = start + "え" * (99 - len(start)) + "。"
            lines, wrapped, left = self.fmt(S * 2 + piece + T)
            self.assertEqual(lines, [S, S + piece, T], start)
            for line in lines[1:]:
                self.assertIsNone(docs_tool.NO_START.match(line), line[:6])

    def test_fmt_reports_the_lines_with_no_place_to_break(self):
        lines, wrapped, left = self.fmt("x\n- " + LONG_SENTENCE)
        self.assertEqual((wrapped, left), ([], [(2, 302)]))
        lines, wrapped, left = self.fmt(S + LONG_SENTENCE)  # broken, but a piece is still long
        self.assertEqual((lines, wrapped, left), ([S, LONG_SENTENCE], [1], [(1, 300)]))

    def test_fmt_writes_checks_and_lists(self):
        doc = self.write("docs/a.md", "# a\n\n- " + S * 3 + "\n")
        self.write("docs/b.md", "short\n")
        code, out = self.main("fmt", "--check")
        self.assertEqual(code, 1)
        self.assertIn("docs/a.md: 1 line(s) would be wrapped (lines 3)", out)
        self.assertEqual(self.main("fmt", "--list")[0], 0)
        self.assertEqual(doc.read_text(encoding="utf-8"), "# a\n\n- " + S * 3 + "\n")
        code, out = self.main("fmt")
        self.assertEqual(code, 0, out)
        self.assertEqual(doc.read_text(encoding="utf-8"), "# a\n\n- " + S * 2 + "\n  " + S + "\n")
        self.assertEqual(self.main("fmt", "--check"), (0, "docs fmt: 0 line(s) in 0 file(s) would be wrapped; "
                                                          "0 long line(s) have no place to break\n"))  # fmt: skip
        # a long line with no place to break is shown, and is not a change
        self.write("docs/c.md", LONG_SENTENCE)
        code, out = self.main("fmt", "--check")
        self.assertEqual(code, 0)
        self.assertIn("docs/c.md:1: 300 characters left on one line (no place to break)", out)

    def test_fmt_leaves_out_the_spec_unless_asked(self):
        for rel in ("docs/a.md", "onsa-lang-spec-0.3.md", "docs/onsa-tools.md", "spec/02-lexical.md", "README.md"):
            self.write(rel, S * 3)
        out = self.main("fmt", "--check")[1]
        self.assertEqual(sorted(re.findall(r"^(\S+): 1 line", out, re.M)), ["README.md", "docs/a.md"])
        out = self.main("fmt", "--check", "--spec")[1]
        self.assertEqual(len(re.findall(r"^\S+: 1 line", out, re.M)), 5)
        code, out = self.main("fmt", str(self.root / "onsa-lang-spec-0.3.md"))
        self.assertEqual(code, 0)
        self.assertIn("onsa-lang-spec-0.3.md: skipped, the spec (pass --spec)", out)
        self.assertEqual((self.root / "onsa-lang-spec-0.3.md").read_text(encoding="utf-8"), S * 3)
        # a path given: only that document
        self.assertEqual(self.main("fmt", str(self.root / "README.md"))[0], 0)
        self.assertEqual((self.root / "README.md").read_text(encoding="utf-8"), S * 2 + "\n" + S)
        self.assertEqual((self.root / "docs/a.md").read_text(encoding="utf-8"), S * 3)

    def test_fmt_writes_nothing_when_the_round_trip_breaks(self):
        a = self.write("docs/a.md", S * 3)
        b = self.write("docs/b.md", T * 3)
        real = docs_tool.wrap

        def broken(line):  # breaks the round trip of the second file only
            return ([line[:5], line[6:]], "") if line.startswith("い") else real(line)

        with mock.patch.object(docs_tool, "wrap", side_effect=broken):
            code, out = self.main("fmt")
        self.assertEqual(code, 2)
        self.assertIn("does not give the line back; nothing is written", out)
        self.assertEqual((a.read_text(encoding="utf-8"), b.read_text(encoding="utf-8")), (S * 3, T * 3))

    def test_fmt_does_not_write_a_file_open_in_vim(self):
        a = self.write("docs/a.md", S * 3)
        b = self.write("docs/b.md", T * 3)
        self.write("docs/.a.md.swo", "")
        code, out = self.main("fmt")
        self.assertEqual(code, 1)
        self.assertIn("docs/a.md: skipped, the swap file .a.md.swo", out)
        self.assertEqual(a.read_text(encoding="utf-8"), S * 3)
        self.assertEqual(b.read_text(encoding="utf-8"), T * 2 + "\n" + T)

    def test_fmt_keeps_the_bytes_and_skips_cr(self):
        a = self.write("docs/a.md", "x")
        a.write_bytes((S * 3 + "\r\n").encode("utf-8"))
        code, out = self.main("fmt")
        self.assertEqual(code, 0)
        self.assertIn("docs/a.md: skipped, it has CR line ends", out)
        self.assertEqual(a.read_bytes(), (S * 3 + "\r\n").encode("utf-8"))
        self.write("docs/b.md", "x").write_bytes(b"\xff")
        self.assertEqual(self.main("fmt")[0], 2)

    # ------------------------------------------------ swaps

    def test_swaps(self):
        for rel in ("docs/.a.md.swp", ".x.swo", "rules/.r.md.swn", "target/.t.swp", ".git/.g.swp",
                    ".claude/worktrees/w/.w.md.swp", "crates/c/target/.c.swp", "docs/a.swp", "docs/.a.md.swpx"):
            self.write(rel, "")
        self.write("crates/c/Cargo.toml", "")
        code, out = self.main("swaps")
        self.assertEqual(code, 1)
        self.assertEqual(out, ".x.swo\ndocs/.a.md.swp\nrules/.r.md.swn\ndocs swaps: 3 swap file(s)\n")
        self.assertEqual(docs_tool.swap_files_of(self.root / "docs/a.md"), [self.root / "docs/.a.md.swp"])
        for rel in (".x.swo", "docs/.a.md.swp", "rules/.r.md.swn"):
            (self.root / rel).unlink()
        self.assertEqual(self.main("swaps"), (0, "docs swaps: 0 swap file(s)\n"))

    # ------------------------------------------------ check and the documents

    def test_check_counts_the_cells_of_the_tables(self):
        self.write("docs/a.md", "\n".join([
            "| a | b |", "|---|:-:|", "| 1 | 2 |", "| 1 | 2 | 3 |", "| 1 |", "| `x|y` | a \\| b |", "| ``a`|`b`` | c",
            "", "| a | b |", "|---|---|---|", "| 1 | 2 |",
            "", "```", "| a | b |", "|---|---|", "| 1 |", "```",
            "<!--", "| a | b |", "|---|---|", "| 1 |", "-->",
            "- item", "  | x | y |", "  |---|---|", "  | 1 |",
            "", "| t | u |", "", "| 1 | 2 |",
        ]))  # fmt: skip
        code, out = self.main("check")
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), [
            "== tables",
            "docs/a.md:4: the row has 3 cells, the header 2",
            "docs/a.md:5: the row has 1 cells, the header 2",
            "docs/a.md:10: the delimiter row has 3 cells, the header 2",
            "docs/a.md:26: the row has 1 cells, the header 2",
            "docs/a.md:28: table rows with no header and delimiter row before them",
            "docs/a.md:30: table rows with no header and delimiter row before them",
            "heads, refs, relations: no directory of the new layout",
            "docs check: 6 problem(s) (tables 6, heads 0, refs 0, relations 0, links 0)",
        ])  # fmt: skip

    def test_check_passes_and_fails_on_an_open_fence(self):
        self.write("docs/a.md", "| a | b |\n|---|---|\n| 1 | 2 |\n")
        none = "heads, refs, relations: no directory of the new layout\n"
        self.assertEqual(self.main("check"), (0, none + "docs check: no problem in 1 document(s) "
                                                        "(tables, heads, refs, relations, links)\n"))  # fmt: skip
        self.write("docs/b.md", "x\n````\n| a |\n```\n")
        self.assertEqual(self.main("check"), (1, "== tables\ndocs/b.md:2: the code fence is not closed\n" + none +
                                                 "docs check: 1 problem(s) (tables 1, heads 0, refs 0, relations 0, "
                                                 "links 0)\n"))  # fmt: skip

    def test_check_with_no_document_is_an_error(self):
        self.write("history/a.md", "| a |\n| 1 | 2 |\n")
        code, out = self.main("check")
        self.assertEqual(code, 2)
        self.assertIn("no document found", out)
        self.assertEqual(self.main("fmt", "--check")[0], 2)

    def test_the_documents_by_the_layout(self):
        current = ["CLAUDE.md", "README.md", "docs/a.md", "docs/onsa-tools.md", "onsa-lang-spec-0.3.md"]
        for rel in current + ["onsa-lang-spec-0.2.md", "kumi-lang-spec.md", "docs/sub/x.md", "docs/f.toml", "history/h.md"]:
            self.write(rel, "| a |\n|---|\n| 1 | 2 |\n")
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root)], current)
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root, spec=False)], current[:3])
        out = self.main("check")[1]
        self.assertEqual(re.findall(r"^(\S+):3:", out, re.M), current)
        # the new layout: read where the files are; `history/` is never read
        new = ["decisions/S/S-1.md", "issues/R/R-1.md", "rules/common.md", "spec/02-lexical.md", "spec/README.md",
               "tasks/W/W1-01.md"]  # fmt: skip
        for rel in new:
            self.write(rel, "| a |\n|---|\n| 1 | 2 |\n")
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root)], sorted(current + new))
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root, spec=False)],
                         sorted(current[:3] + new[:3] + new[5:]))  # fmt: skip
        out = self.main("check")[1]
        self.assertEqual(re.findall(r"^(\S+):3:", out, re.M), sorted(current + new))



FIELDS_HEADER = "| キー | 形 | 値 | 要る | 意味 |\n|---|---|---|---|---|\n"
# A made-up repository in the new layout (X-2 DS-1): it passes `docs check`.
NEW_LAYOUT = {
    "decisions/README.md": "# 決定\n\n## 頭の欄\n\n" + FIELDS_HEADER + """\
| `status` | 閉じた値 | `OPEN` / `DECIDED` / `DROPPED` | はい | 状態 |
| `spec` | 節の並び | — | いいえ | 仕様の節 |
| `tasks` | ID の並び（W、T、P2） | — | いいえ | 担う作業 |
| `amends` | ID の並び（S、D、K、Q、A） | — | いいえ | 改めた前の決定 |
| `amended_by` | ID の並び（S、D、K、Q、A） | — | いいえ | 改めた後の決定 |
| `found_by` | 文字列 | — | いいえ | 見つけた票 |
| `before` | ID（W） | — | いいえ | 期限の作業 |
| `group` | 整数 | — | いいえ | 組 |
| `decided` | 日付 | — | いいえ | 決めた日 |
""",
    "decisions/S/S-1.md": """\
+++
status = "DECIDED"
spec = ["§2.1"]
tasks = ["W1-01"]
amended_by = ["S-2"]
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
tasks = ["W1-02", "P2"]
amends = ["S-1"]
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
| `depends` | ID の並び（W） | — | いいえ | 依存 |
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
# The same IDs in the current layout (a T work only here).
OLD_LAYOUT = {
    "docs/rework-phase1.md": "## 3. 作業\n| ID | 作業 |\n|---|---|\n| W1-01 ✅ | gate |\n| W1-02 | 式 |\n## 4. 残り\n",
    "docs/implementation-tasks.md": "## 2. S\n| ID | 項目 |\n|---|---|\n| S-1 ✅ | 字句 |\n| S-2 | b |\n## 3. 設計\n"
                                    "## 4. 作業\n| ID | 作業 |\n|---|---|\n| T1-1 | t |\n## 5. 診断コード\n"
                                    "| コード | 内容 | 段 | M |\n|---|---|---|---|\n| E0612〜E0613 | x | — | 第 2 期 |\n\n"
                                    "欠番: E0611（S-1 でまとめた）。\n## 6. 例\n",
    "docs/review-impl-phase1.md": "| ID | 内容 |\n|---|---|\n| R-1 | 候補 |\n",
    "docs/api-candidates.md": "| ID | 候補 |\n|---|---|\n| A-1 | is_some |\n",
    "docs/onsa-tools.md": NEW_LAYOUT["spec/tools.md"],
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
    (root / repo.SPEC_README).write_bytes((head + repo.SPEC_INDEX_HEAD + "\n\n| § | ファイル |\n").encode())
    for a, b in zip(starts, [*starts[1:], len(lines)]):
        n = int(re.match(r"## (\d+)", lines[a]).group(1))
        part = "\n".join(lines[a:b]) + ("\n" if b < len(lines) else "")
        (root / "spec" / f"{n:02d}-c.md").write_bytes(part.encode())


class DocsTree(unittest.TestCase):
    """A made-up tree of documents in a temporary directory (the base of DocsLayout and DocsCommands)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def layout(self, files=NEW_LAYOUT):
        for rel, text in files.items():
            self.write(rel, text)

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1, old)
        p.write_text(text.replace(old, new), encoding="utf-8")


class DocsLayout(DocsTree):
    """X-2 U2: the IDs and their paths, `repo.Layout`, the spec as one text, the head fields, the field
    tables of the READMEs, `docs check` (a), (b), (c), (e), and the readers switched to the new layout."""

    def check(self):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main(["check", "--root", str(self.root)])
        lines = [x for x in out.getvalue().splitlines() if not x.startswith(("== ", "docs check: "))]
        return code, lines

    def assertOne(self, rel, old, new, finding):
        """Broken by one edit, `docs check` finds exactly `finding`; the edit undone, nothing."""
        self.edit(rel, old, new)
        self.assertEqual(self.check(), (1, [finding]), (rel, new))
        self.edit(rel, new, old)

    # ------------------------------------------------ the IDs and their paths

    def test_the_kinds_and_the_paths(self):
        self.assertEqual([repo.kind_of(i).name for i in ("RF-3", "R-3", "W3-13", "T5-8", "P2", "C-40", "S-01")],
                         ["RF", "R", "W", "T", "P2", "C", "S"])  # fmt: skip
        self.assertIsNone(repo.kind_of("S-1a"))
        self.assertEqual(repo.ID_RE.findall("UTF-8 RF-3 _S-1 S-2 W3-13/t S-345a P2 T5-8 xR-9 `S-6`"),
                         ["RF-3", "S-2", "W3-13", "S-345", "T5-8", "S-6"])  # fmt: skip
        self.assertEqual(repo.path_of("S-537"), Path("decisions/S/S-537.md"))
        self.assertEqual(repo.path_of("S-537", draft=True), Path("decisions/S/S-537.draft.md"))
        self.assertEqual(repo.path_of("W3-13"), Path("tasks/W/W3-13.md"))
        for bad, draft in (("W3-13", True), ("C-40", False), ("P2", False), ("x", False)):
            with self.assertRaises(repo.RepoError):
                repo.path_of(bad, draft)
        with self.assertRaisesRegex(repo.RepoError, "not split"):
            repo.section_path(self.root, "§2.1")
        self.layout()
        self.assertEqual([repo.section_path(self.root, s).as_posix() for s in ("§2.1", "§3", "§0.1", "§1", "tools.md §1")],
                         ["spec/02-a.md", "spec/03-b.md", "spec/README.md", "spec/README.md", "spec/tools.md"])  # fmt: skip
        for bad in ("§7", "6.1", "§"):
            with self.assertRaises(repo.RepoError):
                repo.section_path(self.root, bad)

    # ------------------------------------------------ Layout

    def test_the_layout_new_old_and_both(self):
        self.layout(OLD_LAYOUT)
        self.write(repo.SPEC, "# s\n\n## 2. a\n")
        names = ("S", "W", "R", "A", "spec", "tools", "diag")
        self.assertEqual([repo.Layout(self.root).source(n) for n in names], ["old"] * 7)
        self.assertEqual([repo.Layout(self.root).source(n) for n in ("D", "RF", "C", "P2", "T")], [None] * 4 + ["old"])
        new = {"S": "decisions/S/S-1.md", "W": "tasks/W/W1-01.md", "R": "issues/R/R-1.md", "A": "decisions/A/A-1.md",
               "spec": "spec/README.md", "tools": "spec/tools.md", "diag": "tasks/diag-codes.md"}  # fmt: skip
        for name, rel in new.items():
            self.write(rel, NEW_LAYOUT[rel])
            with self.assertRaisesRegex(repo.RepoError, f"^{name} is in both .*DS-5"):
                repo.Layout(self.root).source(name)
        self.assertEqual(self.check(), (2, ["docs.py check: S is in both decisions/S/ and the S numbers of "
                                            "docs/implementation-tasks.md `## 2.`; the migration keeps no copy of what it moved (DS-5)"]))
        # the current tables taken out: the new layout alone
        self.layout(dict.fromkeys(OLD_LAYOUT, "# moved\n"))
        (self.root / repo.SPEC).unlink()
        (self.root / repo.DOC_TOOLS).unlink()
        self.assertEqual([repo.Layout(self.root).source(n) for n in names], ["new"] * 7)
        self.write(repo.DOC_PLAN, "## 2. S\nno rows\n## 3. x\n")  # a section with no row is not a table
        self.assertEqual(repo.Layout(self.root).source("S"), "new")
        self.layout()
        self.assertEqual(self.check(), (0, []))

    def test_the_layout_reads_only_what_it_needs(self):
        self.layout(OLD_LAYOUT)
        (self.root / repo.DOC_PLAN).write_bytes(b"\xff")
        lay = repo.Layout(self.root)
        self.assertEqual((lay.source("S"), lay.source("diag")), ("old", "old"))  # the plan is not read
        self.assertEqual(lay.old_rows("W"), {"W1-01": True, "W1-02": False})
        self.write("decisions/S/S-1.md", "")
        with self.assertRaisesRegex(repo.RepoError, "implementation-tasks.md"):
            repo.Layout(self.root).source("S")  # the new layout is there: the plan is looked at

    # ------------------------------------------------ the spec as one text

    def test_the_spec_joined_from_its_chapters(self):
        self.layout()
        doc = repo.spec_doc(self.root)
        readme = NEW_LAYOUT["spec/README.md"]
        one = readme[: readme.index(repo.SPEC_INDEX_HEAD)] + NEW_LAYOUT["spec/02-a.md"] + NEW_LAYOUT["spec/03-b.md"]
        self.assertEqual(doc.text, one)
        self.assertEqual(repo.spec_text(self.root), one)
        line = one.split("\n").index("### 3.1 群") + 1
        self.assertEqual((doc.where(1), doc.where(line), doc.where(13)), ("spec/README.md:1", "spec/03-b.md:3", "spec/02-a.md:1"))
        self.assertEqual(spec_blocks.headings(doc.text), ["0", "0.1", "1", "2", "2.1", "2.2", "3", "3.1"])
        # the round trip: a spec of one file cut into chapters is joined back to the same text
        other = Path(self.tmp.name) / "cut"
        split_spec(one, other)
        self.assertEqual(repo.spec_text(other), one)
        self.assertEqual(repo.tools_text(self.root), NEW_LAYOUT["spec/tools.md"])

    def test_the_real_spec_joins_back(self):
        text = repo.spec_text(repo.ROOT)
        split_spec(text, self.root)
        self.assertGreater(len(repo.chapters(self.root)), 10)
        self.assertEqual(repo.spec_text(self.root), text)

    def test_the_spec_that_cannot_be_joined(self):
        self.layout()
        readme = NEW_LAYOUT["spec/README.md"]
        for rel, text, error in (
            ("spec/README.md", readme.replace(repo.SPEC_INDEX_HEAD, "## 章"), "expected one line .*found 0"),
            ("spec/README.md", readme + repo.SPEC_INDEX_HEAD + "\n", "found 2"),
            ("spec/03-b.md", "## 4. 演算子\n", "spec/03-b.md:1: a chapter file starts with its heading `## 3. `"),
            ("spec/02-a.md", NEW_LAYOUT["spec/02-a.md"].rstrip("\n"), "spec/02-a.md: does not end with a line end"),
            ("spec/notes.md", "x\n", "spec/notes.md: not a chapter file"),
            ("spec/02-b.md", "## 2. x\n", "the chapter 2 is also spec/02-a.md"),
            (str(repo.SPEC), "# s\n", "spec is in both spec/README.md and onsa-lang-spec-0.3.md"),
        ):
            before = (self.root / rel).read_text(encoding="utf-8") if (self.root / rel).exists() else None
            self.write(rel, text)
            with self.assertRaisesRegex(repo.RepoError, error):
                repo.spec_text(self.root)
            if before is None:
                (self.root / rel).unlink()
            else:
                self.write(rel, before)
        self.assertEqual(repo.spec_text(self.root)[:6], "# Spec")
        for rel in ("spec/02-a.md", "spec/03-b.md"):
            (self.root / rel).unlink()
        with self.assertRaisesRegex(repo.RepoError, "spec/: no chapter file"):
            repo.spec_text(self.root)

    # ------------------------------------------------ the head fields

    def test_read_the_head_fields(self):
        head = docs_tool.read_head(NEW_LAYOUT["decisions/S/S-1.md"])
        self.assertEqual(head.values, {"status": "DECIDED", "spec": ["§2.1"], "tasks": ["W1-01"], "amended_by": ["S-2"],
                                       "decided": datetime.date(2026, 10, 15)})  # fmt: skip
        self.assertEqual((head.key_lines["decided"], head.heading), (6, (8, "# S-1 字句")))
        self.assertEqual(docs_tool.read_head(NEW_LAYOUT["issues/R/R-1.md"]).values["aspect"], 1)
        for text, error, line in (("# S-1\n", docs_tool.NO_HEAD, 1), ("+++\nstatus = 1\n", docs_tool.NOT_CLOSED, 1),
                                  ("+++\n", docs_tool.NOT_CLOSED, 1), ('+++\na = "x"\nb = OPEN\n+++\n', "Invalid value", 3),
                                  ('+++\na = "x"\na = "y"\n+++\n', "Cannot overwrite a value", 4)):  # where tomllib stops  # fmt: skip
            head = docs_tool.read_head(text)
            self.assertEqual((head.values, head.error, head.error_line), (None, error, line), text)

    def test_write_the_head_fields_in_the_normal_form(self):
        self.layout()
        order = docs_tool.field_table(docs_tool.Tree(self.root, []), repo.KIND["S"]).order
        body = "# S-3 x\n\n本文 `+++` と\n+++\n末尾\n"
        p = self.write("decisions/S/S-3.md", "+++\ndecided=2026-10-15\n  status  =  'OPEN'\ntasks=['W1-01','W1-02']\n+++\n" + body)
        values = docs_tool.read_head(p.read_text(encoding="utf-8")).values
        docs_tool.write_head(self.root, "decisions/S/S-3.md", values, order)
        self.assertEqual(p.read_bytes().decode(), '+++\nstatus = "OPEN"\ntasks = ["W1-01", "W1-02"]\ndecided = 2026-10-15\n+++\n' + body)
        new = docs_tool.head_update(self.root, "decisions/S/S-3.md", {**values, "decided": None, "group": 3}, order)
        self.assertEqual(new, '+++\nstatus = "OPEN"\ntasks = ["W1-01", "W1-02"]\ngroup = 3\n+++\n' + body)
        # a file with no head fields gets them; the closing line with no line end gets one
        self.write("decisions/S/S-4.md", "# S-4\n")
        self.assertEqual(docs_tool.head_update(self.root, "decisions/S/S-4.md", {"status": "OPEN"}, order),
                         '+++\nstatus = "OPEN"\n+++\n# S-4\n')  # fmt: skip
        self.write("decisions/S/S-5.md", '+++\nstatus = "OPEN"\n+++')
        self.assertEqual(docs_tool.head_update(self.root, "decisions/S/S-5.md", {"status": "DROPPED"}, order),
                         '+++\nstatus = "DROPPED"\n+++\n')  # fmt: skip
        # nothing is written: a key not in the table, a value TOML has but the form not, a swap file,
        # head fields that cannot be read, CR line ends
        before = p.read_bytes()
        for values, error in (({"color": "x"}, "`color` is not a field"), ({"status": True}, "cannot write True")):
            with self.assertRaisesRegex(docs_tool.DocsError, error):
                docs_tool.write_head(self.root, "decisions/S/S-3.md", values, order)
        self.write("decisions/S/.S-3.md.swp", "")
        with self.assertRaisesRegex(docs_tool.DocsError, "swap file"):
            docs_tool.write_head(self.root, "decisions/S/S-3.md", {"status": "OPEN"}, order)
        self.assertEqual(p.read_bytes(), before)
        self.write("decisions/S/S-6.md", "+++\nstatus = OPEN\n+++\n# S-6\n")
        with self.assertRaisesRegex(docs_tool.DocsError, "S-6.md:2: Invalid value; fix the head fields by hand"):
            docs_tool.head_update(self.root, "decisions/S/S-6.md", {"status": "OPEN"}, order)
        (self.root / "decisions/S/S-7.md").write_bytes(b'+++\r\nstatus = "OPEN"\r\n+++\r\n')
        with self.assertRaisesRegex(docs_tool.DocsError, "CR line ends"):
            docs_tool.head_update(self.root, "decisions/S/S-7.md", {"status": "OPEN"}, order)

    # ------------------------------------------------ docs check

    def test_check_passes_on_the_new_layout(self):
        self.layout()
        code, lines = self.check()
        self.assertEqual((code, lines), (0, []))

    def test_check_heads(self):
        self.layout()
        s1, w2, r1, a1 = "decisions/S/S-1.md", "tasks/W/W1-02.md", "issues/R/R-1.md", "decisions/A/A-1.md"
        self.assertOne(s1, 'status = "DECIDED"', "status = DECIDED", f"{s1}:2: Invalid value")
        self.assertOne(s1, "+++\n#", "#", f"{s1}:1: {docs_tool.NOT_CLOSED}")
        self.assertOne(a1, '+++\nstatus = "DECIDED"\n+++\n', "<!-- x -->\n", f"{a1}:1: {docs_tool.NO_HEAD}")
        self.assertOne(a1, '"DECIDED"', '"DECIDED"\ncolor = "red"', f"{a1}:3: `color` is not a field of decisions/README.md")
        self.assertOne(a1, 'status = "DECIDED"', 'group = 1', f"{a1}:1: the field `status` is required (decisions/README.md)")
        self.assertOne(a1, '"DECIDED"', '"DONE"', f"{a1}:2: `status` has \"DONE\", not one of OPEN / DECIDED / DROPPED")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'tasks = "W1-01"', f"{s1}:4: `tasks` is not an array; its form is ID の並び（W、T、P2）")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'tasks = ["S-2"]', f"{s1}:4: `tasks` has \"S-2\", not an ID of W、T、P2")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'before = "S-2"', f"{s1}:4: `before` has \"S-2\", not an ID of W")
        self.assertOne(s1, '["§2.1"]', '["2.1"]', f"{s1}:3: `spec` has \"2.1\", not a section (`§6.1`, `tools.md §3.2`)")
        self.assertOne(s1, "2026-10-15", '"2026-10-15"', f"{s1}:6: `decided` has \"2026-10-15\", not a date")
        self.assertOne(r1, "aspect = 1", 'aspect = "1"', f"{r1}:4: `aspect` has \"1\", not one of 1 / 2 / 3")
        self.assertOne(w2, '["基盤"]', '["基盤", "危険"]', f"{w2}:5: `marks` has \"危険\", not one of 基盤 / メモ")
        self.assertOne(a1, "# A-1 is_some", "# A-2 is_some", f"{a1}:4: the first line after the head fields is not `# A-1 <title>`")
        self.assertOne(a1, "# A-1 is_some", "A-1", f"{a1}:4: the first line after the head fields is not `# A-1 <title>`")
        self.write("decisions/S/S1.md", "x")
        self.write("decisions/S/R-1.md", "x")
        code, lines = self.check()
        self.assertEqual(lines, ["decisions/S/R-1.md:1: the name is not an ID of S (decisions/S/<ID>.md)",
                                 "decisions/S/S1.md:1: the name is not an ID of S (decisions/S/<ID>.md)"])  # fmt: skip
        (self.root / "decisions/S/S1.md").unlink()
        (self.root / "decisions/S/R-1.md").unlink()
        (self.root / "decisions/K").mkdir()
        self.assertEqual(self.check(), (1, ["decisions/K: no file of an ID; the checks would pass reading nothing"]))

    def test_check_a_broken_field_table_is_one_finding(self):
        self.layout()
        readme = "tasks/W/README.md"
        # the files of the directory are not checked (W1-02 is broken too); the others still are
        self.edit("tasks/W/W1-02.md", 'size = "M"', 'size = "XL"')
        for old, new, what in (
            ("| `size` | 閉じた値 | `S` / `M` / `L` | いいえ | 大きさ |", "| `size` | 閉じた値 | `S` / `M` / `L` | いいえ |", "8: the field table: 4 cells, not 5"),
            ("| `depends` | ID の並び（W） |", "| `depends` | ID の列（W） |", "9: the field table: the form `ID の列（W）` is not known"),
            ("| `depends` | ID の並び（W） |", "| `depends` | ID の並び（W、Z） |", "9: the field table: the form `ID の並び（W、Z）` names a kind"),
            ("`S` / `M` / `L`", "`S` /  / `L`", "8: the field table: the values `S` /  / `L`"),
            ("`S` / `M` / `L`", "`S` / `S`", "8: the field table: the values `S` / `S`"),
            ("| `commit` | 文字列 | — |", "| `commit` | 文字列 | x |", "12: the field table: the values x of the form 文字列"),
            ("| コミット |", "| コミット |\n| `Commit` | 文字列 | — | いいえ | x |", "13: the field table: the key `Commit`"),
            ("| コミット |", "| コミット |\n| `size` | 文字列 | — | いいえ | x |", "13: the field table: the key `size` is given twice"),
            ("| `size` | 閉じた値 | `S` / `M` / `L` | いいえ |", "| `size` | 閉じた値 | `S` / `M` / `L` | yes |", "8: the field table: 要る is `yes`"),
            ("| キー | 形 | 値 | 要る | 意味 |", "| キー | 型 | 値 | 要る | 意味 |", "5: the field table: the header is not"),
            ("## 頭の欄\n\n", "## 頭の欄\n\n## 次\n\n", "3: the field table: no table under the heading"),
            ("# 作業\n", "# 作業\n\n## 頭の欄\n", "5: the field table: a second `## 頭の欄`"),
        ):
            self.edit(readme, old, new)
            code, lines = self.check()
            if "cells" in what:  # the check of the tables (d) finds the row too
                self.assertEqual(lines.pop(0), f"{readme}:8: the row has 4 cells, the header 5")
            self.assertEqual(len(lines), 1, (what, lines))
            self.assertTrue(lines[0].startswith(f"{readme}:{what}"), (what, lines))
            self.edit(readme, new, old)
        (self.root / readme).unlink()
        self.assertEqual(self.check()[1], ["tasks/W/README.md: no field table (`## 頭の欄` in tasks/W/README.md or tasks/README.md)"])

    def test_check_refs(self):
        self.layout()
        s1, s2, w2 = "decisions/S/S-1.md", "decisions/S/S-2.md", "tasks/W/W1-02.md"
        self.assertOne(s2, '["W1-02", "P2"]', '["W1-09", "P2", "T9-9"]', f"{s2}:3: tasks: W1-09 is not found (tasks/W/)")
        self.assertOne(s2, "found_by = \"W1-01/t\"", "found_by = \"W1-08/t\"", f"{s2}:5: found_by: W1-08 is not found (tasks/W/)")
        self.assertOne(s2, "R-1 と A-1", "R-1 と A-1、R-1、A-2、A-2", f"{s2}:8: A-2 is not found (decisions/A/)")
        self.assertOne(w2, '["W1-01"]', '["W1-08"]', f"{w2}:4: depends: W1-08 is not found (tasks/W/)")
        self.assertOne(s1, '["§2.1"]', '["§2.1", "§9.9"]', f"{s1}:3: spec: §9.9 is not a numbered heading of the spec")
        self.assertOne(s1, "§3 と §2", "§3 と §2、§7", f"{s1}:10: §7 is not a numbered heading of the spec")
        self.assertOne(s1, "`tools.md §1`", "`tools.md §1・§2`", f"{s1}:10: tools.md §2 is not a numbered heading of the spec of the tools")
        # a kind still in the current table: read there
        for rel in ("issues/R/R-1.md", "issues/R/README.md"):
            (self.root / rel).unlink()
        (self.root / "issues/R").rmdir()
        self.write(repo.DOC_REVIEW, OLD_LAYOUT["docs/review-impl-phase1.md"])
        self.assertEqual(self.check(), (0, []))
        self.assertOne(s2, "R-1 と", "R-5 と", f"{s2}:8: R-5 is not found (the R numbers of docs/review-impl-phase1.md)")

    def test_check_relations(self):
        self.layout()
        s1, s2, r1, w1 = "decisions/S/S-1.md", "decisions/S/S-2.md", "issues/R/R-1.md", "tasks/W/W1-01.md"
        self.assertOne(s2, '["W1-02", "P2"]', '["W1-01"]', f"{s2}:2: OPEN, but every work of `tasks` is DONE (W1-01)")
        self.assertOne(s1, 'amended_by = ["S-2"]\n', "group = 1\n", f"{s2}:4: `amends` has S-1, but S-1 has no S-2 in `amended_by`")
        self.assertOne(s2, 'amends = ["S-1"]\n', "group = 1\n", f"{s1}:5: `amended_by` has S-2, but S-2 has no S-1 in `amends`")
        self.assertOne(r1, 'fix = ["W1-02"]', 'fix = ["W1-01"]', f"{r1}:2: OPEN, but every work of `fix` is DONE (W1-01)")
        self.assertOne(w1, 'commit = "abc"', 'doing = ["U1/i"]', f"{w1}:3: `doing` on a work that is DONE, not DOING")

    def test_check_links(self):
        self.layout()
        self.assertOne("README.md", "[仕様](spec/README.md)", "[仕様](spec/README.md)、[無い](docs/none.md#x)", "README.md:3: the link docs/none.md#x is not found")
        self.assertOne("rules/README.md", "(common.md)", "(commons.md)", "rules/README.md:3: the link commons.md is not found")

    # ------------------------------------------------ the readers of the current tools

    def test_load_docs_reads_both_layouts_alike(self):
        self.layout()
        new = pending.load_docs(self.root)
        old_root = Path(self.tmp.name) / "old"
        for rel, text in {**OLD_LAYOUT, str(repo.SPEC): repo.spec_text(self.root)}.items():
            (old_root / rel).parent.mkdir(parents=True, exist_ok=True)
            (old_root / rel).write_text(text, encoding="utf-8")
        old = pending.load_docs(old_root)
        self.assertEqual((new.works, new.done, new.reasons), ({"W1-01", "W1-02"}, {"W1-01"}, {"S-1", "S-2", "R-1"}))
        self.assertEqual((old.works - {"T1-1"}, old.done, old.reasons, old.sections), (new.works, new.done, new.reasons, new.sections))
        self.assertEqual(gap_marks.api_ids(self.root), gap_marks.api_ids(old_root))
        for root in (self.root, old_root):
            text, doc = repo.diag_text(root)
            self.assertEqual((repo.retired_codes(text, doc), repo.phase2_codes(text, doc)), ({"E0611"}, {"E0612", "E0613"}))
        self.assertEqual(repo.diag_text(self.root)[1], repo.DIAG_CODES)
        with self.assertRaisesRegex(repo.RepoError, "tasks/diag-codes.md: no row of the table is `第 2 期`"):
            repo.phase2_codes("| E0001 | x |\n", repo.DIAG_CODES)
        # a directory with no file of an ID is an error, not an empty table
        for rel in ("tasks/W/W1-01.md", "tasks/W/W1-02.md"):
            (self.root / rel).unlink()
        with self.assertRaisesRegex(pending.DocsError, "tasks/W/: no file of an ID"):
            pending.load_docs(self.root)

    def test_the_readers_of_the_spec_in_the_new_layout(self):
        self.layout()
        # spec_sections: a section only the chapters have
        cases = [{"path": "tests/a.onsa", "spec": ["§3.1"]}, {"path": "tests/b.onsa", "spec": ["§9.9"]}]
        with mock.patch.object(repo, "cases_json", return_value=cases):
            out = io.StringIO()
            with mock.patch.object(sys, "stdout", out):
                code = spec_sections.main(["--check"], root=self.root)
        self.assertEqual(code, 1)
        self.assertIn("tests/b.onsa: [test] spec names §9.9", out.getvalue())
        self.assertNotIn("§3.1", out.getvalue())
        # keywords: §2.2 of the chapter 2
        with mock.patch.object(repo, "cases_json", return_value=["fn", "let"]):
            self.assertEqual(quiet(keywords.main, ["--root", str(self.root)]), 0)
        # default_inits: the lines of the blocks in their files
        srcs = default_inits.sources(self.root)[0]
        self.assertEqual([(s.shown, s.first) for s in srcs], [("spec/03-b.md", 6), ("spec/tools.md", 6)])
        # check_spec_examples: the lines of the blocks in their files
        problems, _ = cse.check(repo.spec_doc(self.root), self.root / "tests" / "spec", self.root / repo.PENDING, self.root)
        self.assertEqual([p.split("  ")[0] for p in problems], ["spec/03-b.md:6"])


class DocsCommands(DocsTree):
    """X-2 U3: the commands of `docs.py` that read (path, back, refs; show, list, changes, ticket) and
    write (set, note, new, draft, amend), on NEW_LAYOUT and OLD_LAYOUT."""

    def setUp(self):
        super().setUp()
        patcher = mock.patch.object(docs_tool, "today", return_value=datetime.date(2026, 10, 16))
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_(self, *argv):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main([*argv, "--root", str(self.root)])
        return code, out.getvalue().splitlines()

    def read(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    def old_layout(self):
        readme = NEW_LAYOUT["spec/README.md"]
        spec = readme[: readme.index(repo.SPEC_INDEX_HEAD)] + NEW_LAYOUT["spec/02-a.md"] + NEW_LAYOUT["spec/03-b.md"]
        self.layout({**OLD_LAYOUT, str(repo.SPEC): spec})

    def assertRefused(self, argv, lines, unchanged=()):
        """`docs.py <argv>` writes nothing, prints `lines`, and exits 1."""
        before = {rel: self.read(rel) for rel in unchanged}
        code, out = self.run_(*argv)
        self.assertEqual((code, out), (1, [*lines, f"docs {argv[0]}: nothing is written"]), argv)
        self.assertEqual({rel: self.read(rel) for rel in unchanged}, before)

    # ------------------------------------------------ path, back, refs

    def test_path(self):
        self.layout()
        self.assertEqual(self.run_("path", "S-1", "W1-02", "R-1", "A-1", "§2.1", "§0.1", "§3", "tools.md §1"), (0, [
            "decisions/S/S-1.md", "tasks/W/W1-02.md", "issues/R/R-1.md", "decisions/A/A-1.md", "spec/02-a.md:3",
            "spec/README.md:5", "spec/03-b.md:1", "spec/tools.md:3"]))  # fmt: skip
        self.assertEqual(self.run_("path", "S-9", "S-2", "§9.9", "tools.md §2", "C-40", "D-1"), (1, [
            "S-9: not found (decisions/S/)", "decisions/S/S-2.md", "§9.9: not found (not a numbered heading of the spec)",
            "tools.md §2: not found (not a numbered heading of the spec of the tools)",
            "C-40: not found (a kind with no file: the history or the second phase)", "D-1: not found (no decisions/D/)"]))  # fmt: skip
        self.assertEqual(self.run_("path", "--abs", "S-1"), (0, [(self.root / "decisions/S/S-1.md").resolve().as_posix()]))
        code, out = self.run_("path", "S-1", "x")
        self.assertEqual((code, out[-1]), (2, "docs.py path: x: not an ID or a section (`S-537`, `§6.1`, `tools.md §3.2`)"))

    def test_path_back_refs_in_the_current_layout(self):
        self.old_layout()
        self.assertEqual(self.run_("path", "S-1", "W1-02", "R-1", "A-1", "T1-1", "§2.1", "tools.md §1"), (0, [
            "docs/implementation-tasks.md:4", "docs/rework-phase1.md:5", "docs/review-impl-phase1.md:3",
            "docs/api-candidates.md:3", "docs/implementation-tasks.md:10", "onsa-lang-spec-0.3.md:15",
            "docs/onsa-tools.md:3"]))  # fmt: skip
        self.assertEqual(self.run_("path", "S-9"), (1, ["S-9: not found (the S numbers of docs/implementation-tasks.md `## 2.`)"]))
        # back: the row of the ID itself is not a mention
        self.assertEqual(self.run_("back", "S-1"), (0, [
            "== text", "docs/implementation-tasks.md:16: 欠番: E0611（S-1 でまとめた）。",
            "docs back: S-1: 0 key(s), 1 line(s) of text in 1 file(s)"]))  # fmt: skip
        self.write("docs/carry.md", "# 持ち越し\n\nS-1 と W1-02、R-1、A-1、T1-1、S-9、S-1。\n")
        self.assertEqual(self.run_("refs", "docs/carry.md"), (0, [
            "S-1\t✅\tdocs/implementation-tasks.md:4\t-", "W1-02\t-\tdocs/rework-phase1.md:5\t-",
            "R-1\t-\tdocs/review-impl-phase1.md:3\t-", "A-1\t-\tdocs/api-candidates.md:3\t-",
            "T1-1\t-\tdocs/implementation-tasks.md:10\t-",
            "S-9\t-\tnot found (the S numbers of docs/implementation-tasks.md `## 2.`)\t-",
            "docs refs: docs/carry.md: 6 ID(s), 1 not found"]))  # fmt: skip
        # the refs of an ID of a current table: its row
        self.assertEqual(self.run_("refs", "S-2"), (0, ["docs refs: docs/implementation-tasks.md:5: 0 ID(s), 0 not found"]))

    def test_back(self):
        self.layout()
        self.write("history/old.md", "S-2 と S-22\n")
        long = "あ" * 100 + "S-2" + "い" * 100
        self.write("rules/common.md", f"# 共通\n\n{long}\n")
        self.assertEqual(self.run_("back", "S-2"), (0, [
            "== keys", "decisions/S/S-1.md:5: amended_by", "issues/R/R-1.md:5: decisions",
            "== text", "decisions/S/S-1.md:11: - 経緯: C-40 と T5-8 と D-15 は確かめない。`decisions/S/S-2.md` も指す。",
            "rules/common.md:3: …" + "あ" * 60 + "S-2" + "い" * 60 + "…",
            "docs back: S-2: 2 key(s), 2 line(s) of text in 3 file(s)"]))  # fmt: skip
        code, out = self.run_("back", "S-2", "--history")
        self.assertEqual(out[-2:], ["history/old.md:1: S-2 と S-22", "docs back: S-2: 2 key(s), 3 line(s) of text in 4 file(s)"])
        # a key of the head fields: in a string (`found_by`) too; a work in the second phase
        self.assertEqual(self.run_("back", "W1-01")[1][:3], ["== keys", "decisions/S/S-1.md:4: tasks", "decisions/S/S-2.md:5: found_by"])
        self.assertEqual(self.run_("back", "P2")[1], ["== keys", "decisions/S/S-2.md:3: tasks", "docs back: P2: 1 key(s), 0 line(s) of text in 1 file(s)"])
        self.assertEqual(self.run_("back", "S-99")[1], ["docs back: S-99: 0 key(s), 0 line(s) of text in 0 file(s)"])
        self.assertEqual(self.run_("back", "x")[0], 2)

    def test_refs(self):
        self.layout()
        rows = [
            "W1-01\tDONE\ttasks/W/W1-01.md\tgate", "S-2\tOPEN\tdecisions/S/S-2.md\tR-1 と A-1。", "W1-02\tDOING\ttasks/W/W1-02.md\t式",
            "C-40\t-\tnot found (a kind with no file: the history or the second phase)\t-",
            "T5-8\t-\tnot found (a kind with no file: the history or the second phase)\t-",
            "D-15\t-\tnot found (no decisions/D/)\t-", "S-77\t-\tnot found (decisions/S/)\t-",
            "docs refs: decisions/S/S-1.md: 7 ID(s), 4 not found",
        ]  # fmt: skip
        self.assertEqual(self.run_("refs", "decisions/S/S-1.md"), (0, rows))
        self.assertEqual(self.run_("refs", "S-1"), (0, rows))
        self.assertEqual(self.run_("refs", str(self.root / "decisions/S/S-1.md")), (0, rows))
        # head fields that cannot be read are read as text; the draft is not its S
        self.assertEqual(self.run_("refs", "decisions/S/S-2.draft.md")[1][:2], ["S-3\t-\tnot found (decisions/S/)\t-", "S-999\t-\tnot found (decisions/S/)\t-"])
        self.assertEqual(self.run_("refs", "docs/none.md"), (1, ["docs/none.md: not found"]))
        self.assertEqual(self.run_("refs", "S-9"), (1, ["S-9: not found (decisions/S/)"]))
        self.assertEqual(self.run_("refs", "/elsewhere/a.md")[0], 2)

    # ------------------------------------------------ show, list, changes, ticket

    def test_show(self):
        self.layout()
        self.write("tests/pending.toml", entry("spec-example", "§2.1 0123abcd: x", reasons=("S-2", "R-1")) + entry("gate", "g", reasons=("S-1",)))
        code, out = self.run_("show", "S-2")
        self.assertEqual((code, out), (0, [
            "== decisions/S/S-2.md", *NEW_LAYOUT["decisions/S/S-2.md"].splitlines()[:7], "== relations",
            "tasks\tW1-02\tDOING\t式\t-", "tasks\tP2\t-\t-\t-", "amends\tS-1\tDECIDED\t字句\t§2.1", "issue\tR-1\tOPEN\t候補\t-",
            "pending\tspec-example\t§2.1 0123abcd: x\tuntil W3-07", "== body", "- 空白: R-1 と A-1。"]))  # fmt: skip
        self.assertEqual(self.run_("show", "W1-02", "--relations")[1][-4:], [
            "== relations", "decision\tS-2\tOPEN\tR-1 と A-1。\t-", "fixes\tR-1\tOPEN\t候補\t-", "waiting\tS-2\tOPEN\tR-1 と A-1。\t-"])  # fmt: skip
        self.assertEqual(self.run_("show", "W1-01")[1][-3:], ["== relations", "decision\tS-1\tDECIDED\t字句\t§2.1", "depended_by\tW1-02\tDOING\t式\t-"])
        self.assertEqual(self.run_("show", "R-1")[1][-3:], ["== relations", "fix\tW1-02\tDOING\t式\t-", "decisions\tS-2\tOPEN\tR-1 と A-1。\t-"])
        # a work waits for a decision due before it, too
        self.edit("decisions/S/S-2.md", 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W1-01"')
        self.assertEqual(self.run_("show", "W1-01")[1][-1], "waiting\tS-2\tOPEN\tR-1 と A-1。\t-")
        self.write("tests/pending.toml", "x = 1\n")
        self.assertEqual(self.run_("show", "S-2", "--relations")[1][-1], "pending\ttests/pending.toml: 1 error(s); `pending.py` shows them")
        self.assertEqual(self.run_("show", "S-9"), (1, ["S-9: not found (decisions/S/)"]))
        self.assertEqual(self.run_("show", "D-1"), (2, ["docs.py show: D: not in the new layout (no decisions/D/)"]))
        self.assertEqual(self.run_("show", "C-1")[0], 2)

    def test_list(self):
        self.layout()
        s1, s2 = "S-1\tDECIDED\ttasks=W1-01 spec=§2.1\t字句", "S-2\tOPEN\ttasks=W1-02,P2\tR-1 と A-1。"
        self.assertEqual(self.run_("list", "S"), (0, [s1, s2, "docs list: 2 of 2 S"]))
        self.assertEqual(self.run_("list", "S", "--status", "OPEN"), (0, [s2, "docs list: 1 of 2 S"]))
        self.assertEqual(self.run_("list", "S", "--count"), (0, ["S\tOPEN 1, DECIDED 1 (2)", "docs list: 2 of 2 S"]))
        self.assertEqual(self.run_("list", "W", "--count"), (0, ["W1\tDOING 1, DONE 1 (2)", "docs list: 2 of 2 W"]))
        w2 = "W1-02\tDOING\tsize=M depends=W1-01 doing=U2/i\t式"
        self.assertEqual(self.run_("list", "W", "--waiting"), (0, [w2, "docs list: 1 of 2 W"]))
        self.assertEqual(self.run_("list", "W", "--stage", "W2")[1], ["docs list: 0 of 2 W"])
        self.assertEqual(self.run_("list", "S", "--stage", "W1")[1][-1], "docs list: 2 of 2 S")
        self.assertEqual(self.run_("list", "R", "--no-fix")[1], ["docs list: 0 of 1 R"])
        self.assertEqual(self.run_("list", "R")[1][0], "R-1\tOPEN\tseverity=中 fix=W1-02 decisions=S-2\t候補")
        # `before` this work or an earlier one; the group
        self.edit("decisions/S/S-2.md", 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W1-02"\ngroup = 3')
        s2 = "S-2\tOPEN\ttasks=W1-02,P2 before=W1-02 group=3\tR-1 と A-1。"
        for before, rows in (("W1-02", [s2]), ("W2-01", [s2]), ("W1-01", [])):
            self.assertEqual(self.run_("list", "S", "--before", before)[1][:-1], rows, before)
        self.assertEqual(self.run_("list", "S", "--group", "3")[1], [s2, "docs list: 1 of 2 S"])
        # the title of an S with none: the head of its 空白
        self.edit("decisions/S/S-2.md", "- 空白: R-1 と A-1。", "- 空白: " + "あ" * 50)
        self.assertEqual(self.run_("list", "S", "--status", "OPEN")[1][0].split("\t")[-1], "あ" * 40)
        for argv, error in ((("S", "--waiting"), "--waiting is for W, not S"), (("W", "--group", "1"), "--group is for S, D"),
                            (("S", "--status", "DONE"), "--status DONE: not one of OPEN / DECIDED / DROPPED"),
                            (("S", "--stage", "4"), "4: not a stage"), (("S", "--before", "S-1"), "--before S-1: not a work"),
                            (("D",), "D: not in the new layout"), (("Z",), "Z: not an ID or a kind of S, D")):  # fmt: skip
            code, out = self.run_("list", *argv)
            self.assertEqual(code, 2, argv)
            self.assertIn(error, out[-1])

    def test_changes(self):
        self.layout()
        self.write("decisions/S/S-3.md", '+++\nstatus = "DECIDED"\nspec = ["§3.1"]\ndecided = 2026-10-16\n+++\n# S-3 群\n')
        s1, s3 = "S-1\t2026-10-15\t§2.1\t字句", "S-3\t2026-10-16\t§3.1\t群"
        note = "note: A-1 is DECIDED with no `decided`"
        self.assertEqual(self.run_("changes"), (0, [s3, s1, note, "docs changes: 2 decision(s); 1 DECIDED with no `decided`"]))
        self.assertEqual(self.run_("changes", "--since", "2026-10-16")[1][:2], [s3, note])
        self.assertEqual(self.run_("changes", "--section", "§2")[1][:1], [s1])
        self.assertEqual(self.run_("changes", "--section", "§3.1")[1][:1], [s3])
        self.assertEqual(self.run_("changes", "--stage", "W1")[1], [s1, "docs changes: 1 decision(s); 0 DECIDED with no `decided`"])
        self.assertEqual(self.run_("changes", "--section", "3")[0], 2)
        with self.assertRaises(SystemExit):  # argparse: a date
            self.run_("changes", "--since", "16 Oct")

    def test_ticket(self):
        self.layout()
        self.edit("decisions/S/S-2.md", 'status = "OPEN"', 'status = "OPEN"\nspec = ["§3.1", "§2.2"]')
        self.edit("issues/R/R-1.md", 'aspect = 1', 'aspect = 1\nspec = ["§3.1", "tools.md §1"]')
        self.write("tasks/W/W1-02.md", self.read("tasks/W/W1-02.md") + "\n- 持ち越し:\n  - W1-01/b の報告: x\n")
        expected = [
            "# 作業 W1-02 U2/i: 式", "", "- 作業のファイル: tasks/W/W1-02.md（`docs.py show W1-02`）", "- 状態: DOING（doing: U2/i）",
            "- 規模: M", "- 依存: W1-01（DONE）", "- 実現する決定:", "  - S-2 OPEN R-1 と A-1。（§3.1, §2.2）",
            "- 直す R:", "  - R-1 OPEN 候補（§3.1, tools.md §1）", "- 仕様の節: §2.2、§3.1、tools.md §1",
            "- 持ち越し: 作業のファイルの `持ち越し` を読む", "- 役割と単位: U2/i",
            *(f"- {f}:" for f in docs_tool.TICKET_FIELDS),
        ]  # fmt: skip
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i"), (0, expected))
        out = self.root / "t.md"
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i", "--out", str(out)), (0, [str(out)]))
        self.assertEqual(out.read_text(encoding="utf-8"), "\n".join(expected) + "\n")
        self.assertRefused(("ticket", "W1-02", "U2/b", "--out", str(out)), [f"{out}: there already"], ["t.md"])
        self.assertEqual(self.run_("ticket", "W1-01", "U1/t")[1][4:8], ["- 規模: -", "- 依存: なし", "- 実現する決定:", "  - S-1 DECIDED 字句（§2.1）"])
        self.assertEqual(self.run_("ticket", "W1-02", "U2")[0], 2)
        self.assertEqual(self.run_("ticket", "S-1", "U2/i")[0], 2)
        self.assertEqual(self.run_("ticket", "W1-09", "U2/i"), (1, ["W1-09: not found (tasks/W/)"]))

    def test_the_commands_of_the_new_layout_in_the_current_one(self):
        self.old_layout()
        for argv in (("show", "S-1"), ("list", "S"), ("changes",), ("ticket", "W1-01", "U1/i"), ("set", "S-1", "status=OPEN"),
                     ("note", "S-1", "補い", "x"), ("new", "S"), ("draft", "S-1", "--group", "1"), ("amend", "S-2", "S-1")):  # fmt: skip
            code, out = self.run_(*argv)
            self.assertEqual(code, 2, argv)
            self.assertIn("not in the new layout", out[-1], argv)
        self.assertEqual(self.read(repo.DOC_PLAN), OLD_LAYOUT["docs/implementation-tasks.md"])

    # ------------------------------------------------ set, note, new, draft, amend

    def test_set(self):
        self.layout()
        w2 = "tasks/W/W1-02.md"
        self.assertEqual(self.run_("set", "W1-02", "size=L", "doing="), (0, [f'{w2}: size = "L"; doing removed']))
        self.assertEqual(self.read(w2), '+++\nstatus = "DOING"\nsize = "L"\ndepends = ["W1-01"]\nmarks = ["基盤"]\n+++\n# W1-02 式\n')
        self.assertEqual(self.run_("set", "W1-02", "doing=U2/i, U2/b")[1], [f'{w2}: doing = ["U2/i", "U2/b"]'])
        self.assertEqual(self.run_("set", "S-1", "decided=2026-10-17", "group=4")[0], 0)
        self.assertIn("group = 4\ndecided = 2026-10-17\n+++", self.read("decisions/S/S-1.md"))
        # the values do not fit the field table
        self.assertRefused(("set", "W1-02", "size=XL", "marks=基盤,,メモ", "color=red", "size=M", "depends=S-1"), [
            '`size` has "XL", not one of S / M / L', "`marks` has an empty item: 基盤,,メモ",
            "`color` is not a field of tasks/W/README.md (status, size, depends, marks, doing, commit)", "`size` is given twice",
            '`depends` has "S-1", not an ID of W'], [w2])  # fmt: skip
        self.assertRefused(("set", "S-1", "decided=17 Oct"), ['`decided` has "17 Oct", not a date'], ["decisions/S/S-1.md"])
        # after the write, the file or a partner breaks a relation, or a required field is gone
        self.assertRefused(("set", "W1-02", "status=DONE"), [
            "issues/R/R-1.md:2: OPEN, but every work of `fix` is DONE (W1-02)",
            "tasks/W/W1-02.md:6: `doing` on a work that is DONE, not DOING"], [w2, "issues/R/R-1.md"])  # fmt: skip
        self.assertRefused(("set", "W1-02", "status=DONE", "doing="), ["issues/R/R-1.md:2: OPEN, but every work of `fix` is DONE (W1-02)"], [w2])
        self.assertRefused(("set", "W1-02", "status=", "doing="), ["tasks/W/W1-02.md:1: the field `status` is required (tasks/W/README.md)"], [w2])
        self.assertRefused(("set", "S-2", "amends="), ["decisions/S/S-1.md:5: `amended_by` has S-2, but S-2 has no S-1 in `amends`"], ["decisions/S/S-2.md"])
        # in order, both are written
        self.assertEqual(self.run_("set", "R-1", "status=DONE")[0], 0)
        self.assertEqual(self.run_("set", "W1-02", "status=DONE", "doing=")[0], 0)
        self.assertEqual(self.run_("check")[0], 0)
        # a file open in vim; not an ID's file; not KEY=VALUE
        self.write("tasks/W/.W1-02.md.swp", "")
        self.assertRefused(("set", "W1-02", "size=S"), [f"{w2}: the swap file .W1-02.md.swp (open in vim?)"], [w2])
        self.assertEqual(self.run_("set", "W1-09", "size=S"), (1, ["W1-09: not found (tasks/W/)"]))
        self.assertEqual(self.run_("set", "W1-01", "size")[0], 2)

    def test_note(self):
        self.layout()
        r1 = "issues/R/R-1.md"
        self.assertEqual(self.run_("note", "R-1", "判断", "直す。"), (0, [f"{r1}: - 判断（2026-10-16、親）: 直す。"]))
        self.assertEqual(self.run_("note", "R-1", "判断", "直さない。", "--by", "利用者")[0], 0)
        self.assertEqual(self.read(r1), NEW_LAYOUT[r1] + "- 判断（2026-10-16、親）: 直す。\n- 判断（2026-10-16、利用者）: 直さない。\n")
        self.write("decisions/A/A-1.md", NEW_LAYOUT["decisions/A/A-1.md"].rstrip("\n"))
        self.assertEqual(self.run_("note", "A-1", "補い", "x")[0], 0)
        self.assertEqual(self.read("decisions/A/A-1.md"), NEW_LAYOUT["decisions/A/A-1.md"] + "- 補い（2026-10-16、親）: x\n")
        self.assertRefused(("note", "R-1", "判断", "a\nb"), ["the label, the text and the writer are each one line, not empty"], [r1])
        self.assertRefused(("note", "R-1", "", "x"), ["the label, the text and the writer are each one line, not empty"], [r1])
        self.write("issues/R/.R-1.md.swo", "")
        self.assertRefused(("note", "R-1", "判断", "x"), [f"{r1}: the swap file .R-1.md.swo (open in vim?)"], [r1])
        self.assertEqual(self.run_("note", "R-9", "判断", "x"), (1, ["R-9: not found (issues/R/)"]))

    def test_new(self):
        self.layout()
        # the next number counts the drafts (S-2.draft.md); the head fields in the normal form
        self.assertEqual(self.run_("new", "S", "--title", "新しい", "tasks=W1-02", "spec=§3.1"), (0, ["decisions/S/S-3.md"]))
        self.assertEqual(self.read("decisions/S/S-3.md"), '+++\nstatus = "OPEN"\nspec = ["§3.1"]\ntasks = ["W1-02"]\n+++\n# S-3 新しい\n')
        self.write("decisions/S/S-7.draft.md", "")
        # the labels of the body from the README
        self.edit("decisions/README.md", "# 決定\n", "# 決定\n\n## 本文のラベル\n\n- `空白`: 論点\n- `決定`: 決めたこと\n  - 字下げは読まない\n")
        self.assertEqual(self.run_("new", "S")[1], ["decisions/S/S-8.md"])
        self.assertEqual(self.read("decisions/S/S-8.md"), '+++\nstatus = "OPEN"\n+++\n# S-8\n\n- 空白:\n- 決定:\n')
        self.assertEqual(self.run_("new", "W", "--stage", "W1", "--title", "次")[1], ["tasks/W/W1-03.md"])
        self.assertEqual(self.read("tasks/W/W1-03.md"), '+++\nstatus = "PLAN"\n+++\n# W1-03 次\n')
        self.assertEqual(self.run_("new", "W", "--stage", "W12")[1], ["tasks/W/W12-01.md"])
        self.assertEqual(self.run_("check")[0], 0)
        # nothing is written: a field required, a value, a relation, the title, a swap file
        self.edit("issues/R/README.md", "高 / 中 / 低 | いいえ", "高 / 中 / 低 | はい")
        self.assertRefused(("new", "R"), ["the field `severity` is required (issues/R/README.md)"])
        self.assertRefused(("new", "S", "status=MAYBE"), ['`status` has "MAYBE", not one of OPEN / DECIDED / DROPPED'])
        self.assertRefused(("new", "S", "tasks=W1-01"), ["decisions/S/S-9.md:2: OPEN, but every work of `tasks` is DONE (W1-01)"])
        self.assertRefused(("new", "S", "--title", "a\nb"), ["the title is one line, not empty"])
        self.write("decisions/S/.S-9.md.swp", "")
        self.assertRefused(("new", "S"), ["decisions/S/S-9.md: the swap file .S-9.md.swp (open in vim?)"])
        self.assertFalse((self.root / "decisions/S/S-9.md").exists() or (self.root / "issues/R/R-2.md").exists())
        self.assertEqual(self.run_("new", "R", "severity=中")[1], ["issues/R/R-2.md"])
        # usage: the stage of W; in a git worktree, the parent gives the numbers
        for argv in (("new", "W"), ("new", "S", "--stage", "W1"), ("new", "W", "--stage", "4")):
            self.assertEqual(self.run_(*argv)[0], 2, argv)
        with mock.patch.object(repo, "tree_kind", return_value="worktree"):
            self.assertEqual(self.run_("new", "S"), (2, ["docs.py new: the numbers are given in the main tree only "
                                                         "(this is a git worktree; write NEW)"]))  # fmt: skip

    def test_draft(self):
        self.layout()
        self.assertEqual(self.run_("draft", "S-1", "S-2", "--group", "3"), (0, [
            "decisions/S/S-2.draft.md: there already; not written", "decisions/S/S-1.draft.md"]))  # fmt: skip
        self.assertEqual(self.read("decisions/S/S-1.draft.md"), "+++\ngroup = 3\ndrafted = 2026-10-16\n+++\n# S-1 字句\n\n" +
                         "".join(f"- {label}:\n" for label in docs_tool.DRAFT_LABELS))  # fmt: skip
        self.assertEqual(self.read("decisions/S/S-2.draft.md"), NEW_LAYOUT["decisions/S/S-2.draft.md"])
        self.write("decisions/S/S-3.md", '+++\nstatus = "OPEN"\n+++\n# S-3\n')
        self.write("decisions/S/S-4.md", '+++\nstatus = "OPEN"\n+++\n# S-4\n')
        self.assertRefused(("draft", "S-3", "S-9", "--group", "4"), ["S-9: not found (decisions/S/)"])
        self.write("decisions/S/.S-4.draft.md.swp", "")
        self.assertRefused(("draft", "S-3", "S-4", "--group", "4"), ["decisions/S/S-4.draft.md: the swap file .S-4.draft.md.swp (open in vim?)"])
        self.assertFalse((self.root / "decisions/S/S-3.draft.md").exists())
        self.assertEqual(self.run_("draft", "S-3", "--group", "4"), (0, ["decisions/S/S-3.draft.md"]))
        self.assertTrue(self.read("decisions/S/S-3.draft.md").endswith("+++\n# S-3\n\n- 決定済みで戻さないもの:\n" + "".join(f"- {x}:\n" for x in docs_tool.DRAFT_LABELS[1:])))
        self.assertEqual(self.run_("draft", "W1-01", "--group", "1")[0], 2)
        with self.assertRaises(SystemExit):  # argparse: --group is required
            self.run_("draft", "S-3")

    def test_amend(self):
        self.layout()
        s1, s3 = "decisions/S/S-1.md", "decisions/S/S-3.md"
        self.write(s3, '+++\nstatus = "DECIDED"\n+++\n# S-3 後\n')
        self.assertEqual(self.run_("amend", "S-3", "S-1"), (0, [f"{s1}: written", f"{s3}: written"]))
        self.assertIn('amended_by = ["S-2", "S-3"]\n', self.read(s1))
        self.assertEqual(self.read(s3), '+++\nstatus = "DECIDED"\namends = ["S-1"]\n+++\n# S-3 後\n')
        self.assertEqual(self.run_("check")[0], 0)
        self.assertEqual(self.run_("amend", "S-3", "S-1"), (0, ["docs amend: S-3 amends S-1 already"]))
        self.assertRefused(("amend", "S-1", "S-1"), ["S-1 cannot amend itself"])
        self.assertRefused(("amend", "S-9", "S-1"), ["S-9: not found (decisions/S/)"], [s1])
        self.assertEqual(self.run_("amend", "W1-01", "S-1")[0], 2)
        self.write("decisions/S/.S-3.md.swp", "")
        self.assertRefused(("amend", "S-3", "S-2"), [f"{s3}: the swap file .S-3.md.swp (open in vim?)"], [s3, "decisions/S/S-2.md"])
        (self.root / "decisions/S/.S-3.md.swp").unlink()
        # the second write fails: the first is put back
        self.write("decisions/S/S-4.md", '+++\nstatus = "DECIDED"\n+++\n# S-4\n')
        before = {rel: self.read(rel) for rel in (s1, "decisions/S/S-4.md")}
        real, calls = docs_tool.write_atomic, []

        def fail_second(path, text):
            calls.append(path)
            if len(calls) == 2:
                raise OSError("no space left")
            real(path, text)

        with mock.patch.object(docs_tool, "write_atomic", side_effect=fail_second):
            code, out = self.run_("amend", "S-4", "S-1")
        self.assertEqual(code, 2)
        self.assertEqual(out[-1], f"docs.py amend: decisions/S/S-4.md: no space left; {s1} put back")
        self.assertEqual(len(calls), 3)
        self.assertEqual({rel: self.read(rel) for rel in before}, before)


if __name__ == "__main__":
    unittest.main(verbosity=1)
