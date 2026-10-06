#!/usr/bin/env python3
"""Self-tests of the gate's own checks (the `gate-selftest` item of tools/gate_steps.py).

Small made-up inputs: a spec, a `tests/spec`, a pending list and the document
tables, in a temporary directory. The gate's wiring is tested with made-up
items that stand in for cargo.

    python3 -B tools/test_gate.py
"""
import io
import os
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_spec_examples as cse  # noqa: E402
import gate  # noqa: E402
import gate_steps  # noqa: E402
import pending  # noqa: E402
import spec_blocks  # noqa: E402

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
## 5. 診断コード
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
            "spec.md": SPEC,
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
            + entry("gate", "c-header", ("S-34",), "T5-8")
            + entry("gate", "c-header/span_const", ("S-34",), "T5-8")
            + entry("test-case", "tests/spec/ops/groups.onsa::a test", ("S-45",), "W3-08")
            + entry("fuzz-input", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
        )
        self.assertEqual(self.errors_of(text), [])

    def test_empty_list_is_valid(self):
        self.assertEqual(self.errors_of(""), [])

    def test_missing_field(self):
        text = entry("spec-example", self.sid).replace('until = "W3-07"\n', "")
        self.assertOneError(text, "missing field `until`")

    def test_unknown_field(self):
        text = entry("spec-example", self.sid).replace('note = "n"\n', 'note = "n"\nline = 3\n')
        self.assertOneError(text, "unknown field `line`")

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
        # the real items keep the gate complete (or only show something): none may be listed
        for step in gate_steps.STEPS:
            with self.subTest(step=step.name):
                self.repo.write("tests/pending.toml", entry("gate", step.name))
                entries, errors = pending.load(self.repo.pending)
                errors += pending.validate(entries, pending.load_docs(self.repo.root), self.repo.root)
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("may be listed", errors[0])

    def test_missing_path(self):
        self.assertOneError(entry("test-case", "tests/spec/nope.onsa"), "does not exist")

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
        code, out = self.run_main([], [fake("c-x", 1, pendable=True), fake("fmt", 1)])
        self.assertEqual(code, 1)  # `fmt` is not pendable: listing it does not hide its failure
        self.assertIn("PENDING c-x", out)
        self.assertIn("FAIL    fmt", out)
        code, out = self.run_main([], [fake("c-x", 0, pendable=True)])
        self.assertEqual(code, 1)
        self.assertIn("remove the entry", out)

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
        results = gate.run_steps(steps, listed, cwd=self.repo.root, out=io.StringIO())
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

    def test_summary(self):
        results = gate.run_steps([fake("ok"), fake("bad", 2)], {}, cwd=self.repo.root, out=io.StringIO())
        lines = gate.summary(results, [], ["M tests/golden/c/a.c"])
        self.assertEqual(lines[-1], "gate: FAIL (bad)")
        self.assertIn("    M tests/golden/c/a.c", lines)
        self.assertIn("  pending: none", lines)


class RealSteps(unittest.TestCase):
    def test_required_items(self):
        names = [s.name for s in gate_steps.STEPS]
        self.assertEqual(len(names), len(set(names)))
        for required in ("fmt", "clippy", "test", "spec-examples", "pending", "gate-selftest", "golden"):
            self.assertIn(required, names)
        by_name = {s.name: s for s in gate_steps.STEPS}
        self.assertTrue(by_name["golden"].info)
        self.assertTrue(by_name["pending"].stage_args and by_name["pending"].gate_steps)
        self.assertEqual(gate_steps.pendable(), [])  # none of today's items may be listed
        for n in names:
            self.assertRegex(n, pending.TARGET_FORMS["gate"])
            self.assertNotIn("/", n)


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


if __name__ == "__main__":
    unittest.main(verbosity=1)
