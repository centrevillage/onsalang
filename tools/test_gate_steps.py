#!/usr/bin/env python3
"""Self-tests of tools/gate_steps.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_gate_steps.py
"""
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate  # noqa: E402
import gate_steps  # noqa: E402
import pending  # noqa: E402


class RealSteps(unittest.TestCase):
    # the C items against the rows of onsa_tests::c::ITEMS (W1-06) are the cross-check item's (tools/crosscheck.py)
    @staticmethod
    def c_items():
        return [s.name for s in gate_steps.STEPS if s.argv[: len(gate_steps.C_CHECK)] == gate_steps.C_CHECK]
    def test_required_items(self):
        names = [s.name for s in gate_steps.STEPS]
        self.assertEqual(len(names), len(set(names)))
        required = (
            "fmt", "clippy", "test", "spec-examples", "spec-sections", "pending", "gate-selftest", "golden",
            "diag-registry", "diag-negatives", "gap-marks", "builtin-names", "ignored-files", "fuzz",
            "fmt-props", "vectors", "ignores", "default-inits", "docs", "docs-fmt", "cargo-features",
        )  # fmt: skip
        for r in required + ("spec-coverage",):
            self.assertIn(r, names)
        by_name = {s.name: s for s in gate_steps.STEPS}
        self.assertTrue(by_name["golden"].info)
        # every test binary runs, the ones after a failing one too (X9-70)
        self.assertEqual(by_name["test"].argv, ("cargo", "test", "--workspace", "--no-fail-fast"))
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
        slow = ["save-base", "fuzz", "fuzz-deep", "fix-loop", "gate-selftest"] + self.c_items() + ["vectors-c", "fmt-props", "fmt-cst"]
        self.assertEqual([s.name for s in gate_steps.STEPS if s.slow], slow)
        # the deep fuzzing runs only at a stage end (W3-03)
        self.assertEqual([s.name for s in gate_steps.STEPS if s.stage_end_only], ["fuzz-deep"])
        # the only items that may be listed: the test vectors against the interpreter and the C
        # (W2-02, by case only), the keywords (W3-02, by case only) and the C checks (W1-06)
        self.assertEqual(gate_steps.pendable(), ["vectors-interp", "keywords"] + self.c_items() + ["vectors-c"])
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
             "spec-sections", "default-inits", "docs", "docs-fmt", "docs-due", "cargo-features", "cross-check"]))  # fmt: skip
        self.assertEqual({s.name: s.narrows for s in steps if s.narrows},
                         {"fuzz": ("tools/fuzz.py", "tools/batch.py", "tools/narrowing.py"),
                          **{n: ("tools/fmt_props.py", "tools/batch.py", "tools/narrowing.py")
                             for n in ("fmt-props", "fmt-cst")}})  # fmt: skip
        for s in steps:
            for p in s.narrows:
                self.assertTrue((gate.TOOLS / Path(p).relative_to("tools")).is_file(), p)
        self.assertEqual({s.name: s.touches for s in steps if s.touches}, {"gate-selftest": ("tools/",)})
        # the self-test is not run by a diff of the table of the allowed names alone (X-1 U10)
        self.assertEqual({s.name: s.touches_except for s in steps if s.touches_except},
                         {"gate-selftest": ("tools/builtin_names.toml",)})  # fmt: skip
        for s in steps:
            for p in s.touches_except:
                self.assertTrue((gate.TOOLS / Path(p).relative_to("tools")).is_file(), p)
        self.assertEqual([s.name for s in steps if s.parent], ["docs-due", "gap-marks"])
        # the documents changed after the last docs check (X-9 U1): `--stage-end` makes it fail
        due = next(s for s in steps if s.name == "docs-due")
        self.assertEqual(due.argv[-2:], (str(gate_steps.TOOLS / "docs.py"), "due"))
        self.assertTrue(due.stage_args and not due.pendable and not due.slow)
        sweep = [s.name for s in steps if gate._in_form(s, gate.Form(sweep=(0, 2)), None)]
        self.assertEqual(sweep[0], "save-base")
        self.assertEqual(sorted(sweep), sorted(["save-base", "gate-selftest", "fuzz", "fmt-props", "fmt-cst"]
                                               + gate_steps.static_names()))  # fmt: skip
        for form in (gate.Form(), gate.Form(works=("W3-07",)), gate.Form(stage_end="W3"), gate.Form(quick=True)):
            self.assertEqual([s.name for s in steps if not gate._in_form(s, form, None)], ["save-base"])
        # the narrowed runs keep the cap of the tools: the gate holds no copy of it
        self.assertFalse(hasattr(gate_steps, "CODE_CAP"))
        self.assertEqual(gate_steps.PARENT, 3)


if __name__ == "__main__":
    unittest.main(verbosity=1)
