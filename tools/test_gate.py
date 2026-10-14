#!/usr/bin/env python3
"""Self-tests of the gate's own checks (the `gate-selftest` item of tools/gate_steps.py).

Small made-up inputs: a spec, a `tests/spec`, a pending list and the document
tables, in a temporary directory. The gate's wiring is tested with made-up
items that stand in for cargo.

    python3 -B tools/test_gate.py
"""
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
import diag_codes  # noqa: E402
import fmt_props  # noqa: E402
import fuzz  # noqa: E402
import gap_marks  # noqa: E402
import gate  # noqa: E402
import gate_steps  # noqa: E402
import ignored_files  # noqa: E402
import keywords  # noqa: E402
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


class GateWiring(TempRepo):
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
            "fmt-props", "vectors", "ignores",
        )  # fmt: skip
        for r in required + ("spec-coverage",):
            self.assertIn(r, names)
        by_name = {s.name: s for s in gate_steps.STEPS}
        self.assertTrue(by_name["golden"].info)
        self.assertTrue(by_name["spec-coverage"].info)
        # the convergence of the fix candidates shows its cycles and divergences, never listed (W3-22)
        self.assertTrue(by_name["fix-loop"].info and not by_name["fix-loop"].pendable)
        self.assertFalse(by_name["spec-sections"].info)
        self.assertTrue(by_name["pending"].stage_args and by_name["pending"].gate_steps)
        # the ignores of the Rust tests: light, so also in `--quick`, and failing at a stage end like the list (R-224)
        self.assertTrue(by_name["ignores"].stage_args and not by_name["ignores"].pendable)
        self.assertFalse(by_name["fmt-props"].pendable)
        # `--quick` leaves out the fuzzing, the self-test, the C and the fmt properties (2026-10-08)
        slow = ["fuzz", "fuzz-deep", "fix-loop", "gate-selftest"] + self.c_items() + ["vectors-c", "fmt-props", "fmt-comments", "fmt-cst"]
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
        return marks, gap_marks.check(marks, known)

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


if __name__ == "__main__":
    unittest.main(verbosity=1)
