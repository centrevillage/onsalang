#!/usr/bin/env python3
"""Self-tests of the `vectors` gate item (W2-01): the checks of tools/vectors/gen.py find what they are for.

Run by tools/test_gate.py (the `gate-selftest` item), or alone: python3 -B tools/vectors/test_vectors.py
"""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen  # noqa: E402
import model as M  # noqa: E402
import ops as O  # noqa: E402
import spec_tokens  # noqa: E402


class VectorsTools(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.copy = Path(cls.tmp.name) / "vectors"
        shutil.copytree(gen.DATA, cls.copy)
        cls.spec = gen.SPEC.read_text(encoding="utf-8")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def fresh(self):
        d = Path(self.tmp.name) / "work"
        shutil.rmtree(d, ignore_errors=True)
        shutil.copytree(self.copy, d)
        return d

    def test_committed_data_passes(self):
        self.assertEqual(gen.check(self.copy, quiet=True), [])

    def test_an_edited_expected_value_is_found(self):
        d = self.fresh()
        p = d / "int-i32.tsv"
        text = p.read_text()
        self.assertIn("-2147483648 -1\t0", text)
        p.write_text(text.replace("-2147483648 -1\t0", "-2147483648 -1\tpanic:overflow", 1))
        problems = gen.check(d, quiet=True)
        self.assertTrue(any("int-i32.tsv" in x and "differs" in x for x in problems), problems)

    def test_a_missing_and_an_extra_file_are_found(self):
        d = self.fresh()
        (d / "const.tsv").unlink()
        (d / "extra.tsv").write_text("x\n")
        problems = gen.check(d, quiet=True)
        self.assertTrue(any("const.tsv" in x and "not in" in x for x in problems), problems)
        self.assertTrue(any("extra.tsv" in x and "not generated" in x for x in problems), problems)

    def test_a_broken_model_is_found(self):
        real = M.int_op

        def broken(t, op, args):  # MIN.rem_euclid(-1) panics, as in Rust
            if op == "rem_euclid" and args[1] == -1 and args[0] == M.int_range(t)[0]:
                return ("panic", "overflow")
            return real(t, op, args)
        with mock.patch.object(M, "int_op", broken):
            problems = gen.check(self.copy, quiet=True)
        self.assertTrue(any("int-i32.tsv" in x and "differs" in x for x in problems), problems)

    def test_a_rule_the_known_answers_cover_is_found_at_once(self):
        real = M.int_op

        def broken(t, op, args):  # MIN % -1 panics, as in Rust and in C
            if op == "rem" and args[1] == -1 and args[0] == M.int_range(t)[0]:
                return ("panic", "overflow")
            return real(t, op, args)
        with mock.patch.object(M, "int_op", broken):
            problems = gen.check(self.copy, quiet=True)
        self.assertTrue(any("known-answer" in x for x in problems), problems)

    def test_a_changed_nan_rule_is_found(self):
        real = M.from_bits  # a NaN pattern is a NaN, whatever its bits
        with mock.patch.object(M, "from_bits", lambda t, u: ("v", u)):
            problems = gen.check(self.copy, quiet=True)
        self.assertTrue(any("conv-f32.tsv" in x and "differs" in x for x in problems), problems)
        self.assertEqual(real("f32", 0xFFC00001), M.NAN)
        with mock.patch.object(M, "to_bits", lambda t, bits: bits):  # the hardware's bits, not the normal NaN
            self.assertTrue(any("known-answer" in x for x in gen.check(self.copy, quiet=True)))

    def test_xcheck_must_be_for_this_data(self):
        d = self.fresh()
        p = d / "XCHECK"
        lines = p.read_text().splitlines()
        p.write_text("\n".join("data_sha256 " + "0" * 64 if l.startswith("data_sha256 ") else l for l in lines) + "\n")
        self.assertTrue(any("XCHECK" in x and "another data" in x for x in gen.check(d, quiet=True)))
        (d / "XCHECK").unlink()
        self.assertTrue(any("XCHECK: missing" in x for x in gen.check(d, quiet=True)))

    def test_a_new_spec_token_is_found(self):
        spec = self.spec.replace("`a.checked_add(b)` など", "`a.checked_add(b)` や `a.checked_pow(b)` など", 1)
        self.assertNotEqual(spec, self.spec)
        problems = spec_tokens.check(O.registry(), spec)
        self.assertTrue(any("checked_pow" in x for x in problems), problems)
        self.assertEqual(spec_tokens.check(O.registry(), self.spec), [])

    def test_a_changed_formula_in_11_4_is_found(self):
        spec = self.spec.replace("y  = (1.0 - f) * a + f * b", "y  = a + f * (b - a)", 1)
        self.assertNotEqual(spec, self.spec)
        self.assertTrue(any("11.4" in x for x in spec_tokens.check(O.registry(), spec)))

    def test_a_missing_conversion_is_found(self):
        ops = O.registry()
        short = [o for o in ops if o.id != "i64.narrow_u64"]
        with self.assertRaises(AssertionError):
            O.check_registry(short)
        with self.assertRaises(AssertionError):
            O.check_registry(ops + [ops[0]])

    def test_conversion_forms_follow_the_table_of_3_3(self):
        self.assertEqual(O.conv_forms("i32", "i64"), ["as"])
        self.assertEqual(O.conv_forms("u32", "i64"), ["as"])
        self.assertEqual(O.conv_forms("u32", "i32"), ["narrow"])
        self.assertEqual(O.conv_forms("i64", "i32"), ["narrow"])
        self.assertEqual(O.conv_forms("i16", "f32"), ["as"])
        self.assertEqual(O.conv_forms("i32", "f32"), ["round"])
        self.assertEqual(O.conv_forms("i32", "f64"), ["as"])
        self.assertEqual(O.conv_forms("u64", "f64"), ["round"])
        self.assertEqual(O.conv_forms("f32", "f64"), ["as"])
        self.assertEqual(O.conv_forms("f64", "f32"), ["round"])
        self.assertEqual(O.conv_forms("f32", "u8"), ["trunc", "trunc_sat"])

    def test_the_model_decides_the_gaps_by_holds(self):
        for fn, args, hold in ((M.f_sub, (0x3F800000, 0x3F800000), M.ZERO_SIGN), (M.f_abs, (0x80000000,), M.ABS_ZERO),
                               (M.f_rem, (0x3F800000, 0x7F800000), M.FMOD_INF)):
            M.Ctx.reset()
            fn("f32", *args)
            self.assertEqual(M.Ctx.holds, {hold})
        M.Ctx.reset()
        M.f_neg("f32", 0)  # a rule the spec writes: no hold
        M.f_minmax("f32", 0, 0x80000000, "min")
        self.assertEqual(M.Ctx.holds, set())

    def test_held_rows_have_no_expected_value(self):
        text = (self.copy / "float-f32.tsv").read_text()
        held = False
        for line in text.splitlines():
            if line.startswith("@ "):
                held = line.split()[2].startswith("held-")
            elif held and line and not line.startswith("#"):
                self.assertEqual(line.split("\t")[1], "?")

    def test_the_named_cases_are_in_the_data(self):
        text = (self.copy / "conv-f64.tsv").read_text()
        self.assertIn("0xbfeccccccccccccd\t0\tS-189", text)       # trunc_u64(-0.9) = 0
        self.assertIn("0xbff0000000000000\tpanic:range\tS-189", text)  # trunc_u32(-1.0) panics


if __name__ == "__main__":
    unittest.main(verbosity=1)
