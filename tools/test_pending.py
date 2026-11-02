#!/usr/bin/env python3
"""Self-tests of tools/pending.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_pending.py
"""
import io
import shutil
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gap_marks  # noqa: E402
import gate  # noqa: E402
import gate_steps  # noqa: E402
import ignores  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
from selftest_support import STAGES, entry, quiet, quiet_out, Repo, TempRepo  # noqa: E402


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
            + entry("gate", "c-x", ("S-34",), "W5-07")
            + entry("gate", "c-header/span_const", ("S-34",), "W5-07")
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
        self.assertOneError(entry("spec-example", self.sid, reasons=("S-99",)), "reason `S-99` is not in decisions/S/, issues/R/")

    def test_work_not_in_tables(self):
        self.assertOneError(entry("spec-example", self.sid, until="W9-99"),
                            "until `W9-99` is not a work of tasks/W/ (`W3-07`) or `PH2`")

    def test_done_work_fails(self):
        self.assertOneError(entry("spec-example", self.sid, until="W1-01"), "marked done")

    def test_a_t_work_is_no_work(self):
        # X-2 U6: the T works are not works of the list (the history keeps them)
        for t in ("T1-1", "T5-8"):
            self.assertOneError(entry("spec-example", self.sid, until=t), f"until `{t}` is not a work of tasks/W/")
        self.assertNotIn("T5-8", pending.load_docs(self.repo.root).works)

    def test_bad_work(self):
        self.assertOneError(entry("spec-example", self.sid, until="M3"), "is not a work of")
        self.assertOneError(entry("spec-example", self.sid, until="M5"), "is not a work of")  # a stage is no work

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
        # a row of spec/foreign-forms.toml by its id (S-250, W3-15)
        self.assertOneError(entry("foreign-form", "semicolon"), "`spec/foreign-forms.toml` does not exist")
        self.repo.write("spec/foreign-forms.toml", '[[form]]\nid = "semicolon"\n\n[[form]]\nid = "let_mut"\n')
        self.assertEqual(self.errors_of(entry("foreign-form", "semicolon") + entry("foreign-form", "let_mut")), [])
        self.assertOneError(entry("foreign-form", "loop"), "is not the `id` of a row of `spec/foreign-forms.toml`")
        for bad in ("Semicolon", "semi colon", "semi-colon", "_semicolon", "semicolon_", "semi__colon", "1st"):
            with self.subTest(target=bad):
                self.assertOneError(entry("foreign-form", bad), "not of the foreign-form form")
        self.repo.write("spec/foreign-forms.toml", "[[form]\n")
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

    def test_a_directory_of_the_ids_missing(self):
        # X-2 DT-7: each kind is read from its directory alone; with no directory, or no file of an ID in it,
        # the tools stop (exit 1), never with no ID
        for d in ("decisions/S", "issues/R", "decisions/A", "tasks/W"):
            for why, make in (("no directory", False), ("no file of an ID", True)):
                with self.subTest(d=d, why=why), tempfile.TemporaryDirectory() as tmp:
                    r = Repo(tmp)
                    shutil.rmtree(r.root / d)
                    if make:
                        (r.root / d).mkdir()
                    said = f"cannot read the IDs: {d}/: {why}"
                    self.assertEqual(quiet_out(gap_marks.main, ["--root", str(r.root)]), (1, [said]))
                    if d == "decisions/A":  # read by gap_marks alone
                        self.assertEqual(pending.load_docs(r.root).works, {"W1-01", "W3-07", "W3-08", "W5-07"})
                        continue
                    with self.assertRaisesRegex(pending.DocsError, f"^{d}/: {why}$"):
                        pending.load_docs(r.root)
                    self.assertEqual(quiet_out(pending.main, ["--root", str(r.root)]), (1, [said]))
                    self.assertEqual(quiet_out(ignores.main, ["stale", "--root", str(r.root)]), (1, [said]))

    def test_stages(self):
        # X-2 U6: the stages and their order are the table of tasks/stages.md, not the IDs of the works
        stages = repo.Layout(self.repo.root).stages()
        self.assertEqual(stages, ("W1", "W3", "W5", "M5", "M9"))
        self.assertEqual(pending.load_docs(self.repo.root).stages, stages)
        text = entry("diag-code", "E0812", until="W5-07") + entry("spec-example", self.sid) + entry("gate", "c-header", until="W3-08")
        self.repo.write("tests/pending.toml", text)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        self.assertEqual(pending.stage_counts(entries, stages), {"W3": 2, "W5": 1})
        self.assertEqual(pending.stages_line(entries, stages), "pending by stage: W3 2, W5 1 (total 3)")
        # the order is the table's, not the numbers'
        self.assertEqual(pending.stages_line(entries, ("W5", "W3")), "pending by stage: W5 1, W3 2 (total 3)")
        self.assertEqual(len(pending.stage_end_errors(entries, "W3", stages)), 2)
        self.assertEqual(pending.stage_end_errors(entries, "W1", stages), [])
        self.assertEqual([pending.stage_of(x) for x in ("W3-07", "M5", "PH2", "T5-8", "S-45")], ["W3", "M5", "PH2", None, None])
        # RF-18 (C2): the stages not in the table after PH2, by their numbers (`repo.stage_key`, as `docs.py list --count`)
        untils = [types.SimpleNamespace(until=u) for u in ("W10-01", "W4-02", "PH2", "W1-01", "S-45")]
        self.assertEqual(pending.stages_line(untils, stages), "pending by stage: W1 1, PH2 1, W4 1, W10 1, ? 1 (total 5)")

    def test_the_last_stage_of_the_table_ends_the_first_phase(self):
        self.repo.write("tests/pending.toml", entry("spec-example", self.sid))
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 1)  # the last: everything but PH2 is left
        self.repo.write("tasks/stages.md", STAGES.replace("| M9 | 締め | — | — |\n", "| M9 | 締め | — | — |\n| M10 | 次 | — | — |\n"))
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 0)  # now a stage like the others
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M10"]), 1)
        docs = pending.load_docs(self.repo.root)
        self.assertIn("the last stage is M10", pending.stage_problem("PH2", docs))
        self.assertTrue(pending.left_at_end("W1-01", "M10", docs.stages))
        self.assertFalse(pending.left_at_end("PH2", "M10", docs.stages))

    def test_an_unknown_stage_names_the_stages_of_the_table(self):
        docs = pending.load_docs(self.repo.root)
        self.assertEqual(pending.stage_problem("W4", docs), "unknown stage `W4` (one of W1, W3, W5, M5, M9: tasks/stages.md)")
        self.assertIsNone(pending.stage_problem("M5", docs))  # a stage with no work is a stage
        code, out = quiet_out(pending.main, ["--root", str(self.repo.root), "--stage-end", "W4"])
        self.assertEqual(code, 2)
        self.assertEqual(out, ["unknown stage `W4` (one of W1, W3, W5, M5, M9: tasks/stages.md)"])

    def test_the_table_of_the_stages_broken(self):
        # every tool stops on the same RepoError of `repo.Layout.stages`
        head = "# 段\n\n| 段 | 名前 |\n"
        for text, why in (
            (None, "tasks/stages.md: [Errno 2]"),
            ("# 段\nno table\n", "expected one table whose first column is `段`, found 0"),
            (head + "|---|---|\n| W1 | a |\n\n" + head + "|---|---|\n", "found 2"),
            (head + "| W1 | a |\n", "tasks/stages.md:4: no delimiter row"),
            (head + "|---|---|\n\nW1\n", "tasks/stages.md:3: the table of the stages has no row"),
            (head + "|---|---|\n| W1 | a |\n| PH2 | b |\n", "tasks/stages.md:6: `PH2` is not a stage"),
            (head + "|---|---|\n| W1-01 | a |\n", "tasks/stages.md:5: `W1-01` is not a stage"),
            (head + "|---|---|\n| W1 | a |\n| W1 | b |\n", "tasks/stages.md:6: `W1` is given twice"),
        ):
            with self.subTest(why=why):
                if text is None:
                    (self.repo.root / repo.STAGES).unlink(missing_ok=True)
                else:
                    self.repo.write("tasks/stages.md", text)
                with self.assertRaises(repo.RepoError) as caught:
                    repo.Layout(self.repo.root).stages()
                self.assertIn(why, str(caught.exception))
                self.assertRaises(repo.RepoError, pending.load_docs, self.repo.root)
                code, out = quiet_out(pending.main, ["--root", str(self.repo.root)])
                self.assertEqual((code, out), (1, [f"cannot read the IDs: {caught.exception}"]))
                code, out = quiet_out(ignores.main, ["stale", "--root", str(self.repo.root)])
                self.assertEqual((code, out), (1, [f"cannot read the IDs: {caught.exception}"]))
                code, out = quiet_out(gate.main, [], steps=[], root=self.repo.root, out=io.StringIO())
                self.assertEqual(code, 2)
                self.assertIn(str(caught.exception), "\n".join(out))

    def test_stage_end_m9(self):
        # X-2 U6: M9 is a stage (the table's), the T works are none
        self.repo.write("tests/pending.toml", entry("diag-code", "E0612", until="PH2"))
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 0)
        self.repo.write("tests/pending.toml", entry("spec-example", self.sid))
        code, out = quiet_out(pending.main, base + ["--stage-end", "M9"])
        self.assertEqual(code, 1)
        self.assertIn("still pending at the end of M9 (until W3-07)", "\n".join(out))

    def test_stage_end_cli(self):
        self.repo.write("tests/pending.toml", entry("spec-example", self.sid))
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W1"]), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W3"]), 1)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "W4"]), 2)  # no such stage in the table
        self.assertEqual(quiet(pending.main, base + ["--stage-end", ""]), 2)

    def test_gate_steps_cli(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-header", until="W5-07"))
        base = ["--root", str(self.repo.root)]
        self.assertEqual(quiet(pending.main, base + ["--gate-steps", "c-header"]), 0)
        self.assertEqual(quiet(pending.main, base + ["--gate-steps", ""]), 1)

    def test_phase2(self):
        # K-13 rule 3: a code of the second phase waits for no work
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", until="PH2")), [])
        self.assertOneError(entry("spec-example", self.sid, until="PH2"), "only for diag-code")
        self.assertOneError(entry("test-case", "tests/spec/ops/groups.onsa", until="PH2"), "only for diag-code")
        self.assertOneError(entry("diag-code", "E0612", until="P3"), "is not a work of")
        self.assertOneError(entry("diag-code", "E0612", until="p2"), "is not a work of")

    def test_phase2_spec_sections(self):
        # a PH2 entry may give a numbered heading of the spec as a reason
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", reasons=("§17.4", "S-45"), until="PH2")), [])
        self.assertEqual(self.errors_of(entry("diag-code", "E0612", reasons=("§3",), until="PH2")), [])
        self.assertOneError(entry("diag-code", "E0612", reasons=("§9.9",), until="PH2"), "not a numbered heading")
        self.assertOneError(entry("diag-code", "E0612", reasons=("§3.",), until="PH2"), "not an S / R number")
        self.assertOneError(entry("diag-code", "E0612", reasons=("§3.1",)), 'only of `until = "PH2"`')
        self.assertOneError(entry("spec-example", self.sid, reasons=("§3.1",)), 'only of `until = "PH2"`')
        (self.repo.root / repo.SPEC_README).unlink()
        with self.assertRaisesRegex(pending.DocsError, "spec/README.md"):
            pending.load_docs(self.repo.root)

    def test_phase2_stages(self):
        text = entry("diag-code", "E0612", until="PH2") + entry("diag-code", "E0001", until="W5-07") + entry("spec-example", self.sid)
        self.repo.write("tests/pending.toml", text)
        entries, errors = pending.load(self.repo.pending)
        self.assertEqual(errors, [])
        stages = pending.load_docs(self.repo.root).stages
        self.assertEqual(pending.stage_of("PH2"), "PH2")
        # the second phase comes after every stage of the first
        self.assertEqual(pending.stages_line(entries, stages), "pending by stage: W3 1, W5 1, PH2 1 (total 3)")
        # the end of the first phase leaves only PH2
        left = pending.stage_end_errors(entries, "M9", stages)
        self.assertEqual(len(left), 2, left)
        self.assertFalse(any("E0612" in m for m in left), left)
        self.assertEqual(len(pending.stage_end_errors(entries, "W3", stages)), 1)
        base = ["--root", str(self.repo.root), "--gate-steps", ""]
        self.assertEqual(quiet(pending.main, base), 0)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "PH2"]), 2)
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 1)
        self.repo.write("tests/pending.toml", entry("diag-code", "E0612", until="PH2"))
        self.assertEqual(quiet(pending.main, base + ["--stage-end", "M9"]), 0)
        self.assertIn("PH2", gate.summary([], pending.load(self.repo.pending)[0], [], stages)[2])


class PendingEdit(TempRepo):
    """tools/pending.py list / remove / add: the other entries stay byte for byte, the list stays valid."""

    def setUp(self):
        super().setUp()
        self.text = ("# head\n\n" + entry("test-case", "tests/spec/ops/groups.onsa", ("S-45",), "W3-08")
                     + "# group\n" + entry("diag-code", "E0812", ("R-23",), "W5-07")
                     + entry("gate", "c-header/x", ("S-34",), "W3-08").rstrip("\n") + "\n")
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
        # with no command, `check` (X-9 U9): the same exit and output by name
        for steps in ("c-header", "c-gcc"):
            calls = [quiet_out(pending.main, [*cmd, "--root", str(self.repo.root), "--gate-steps", steps])
                     for cmd in ([], ["check"])]  # fmt: skip
            self.assertEqual(calls[0], calls[1])
            self.assertEqual(calls[0][0], 0 if steps == "c-header" else 1)

    def test_help(self):
        for name, c in pending.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^pending\.py {name}( |$)")
                code, lines = quiet_out(pending.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(pending.main, ["help", "--role", role])
                want = [n for n, c in pending.COMMANDS.items() if role in c.roles]
                self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        names = list(pending.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(pending.main, ["help"])[1][: len(names)]], names)
        self.assertEqual(names, ["check", "list", "add", "remove"])  # in the order of the work (X-9 U9)
        for flag in ("-h", "--help"):  # the list of the commands, not `check --help` (rules/common.md 1.14)
            with self.subTest(flag=flag), self.assertRaises(SystemExit) as e:
                quiet_out(pending.main, [flag])
            self.assertEqual(e.exception.code, 0)
        buf = io.StringIO()
        with mock.patch.object(sys, "stdout", buf), self.assertRaises(SystemExit):
            pending.main(["--help"])
        self.assertIn("{" + ",".join(names + ["help"]) + "}", buf.getvalue())
        self.assertNotIn("--gate-steps", buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
