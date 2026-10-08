"""The cases the decisions and the plan name (W2-01 ticket): the generator forces them into
the `edge` sections with a note, and the gate checks they are in the data.

Each entry is (operation id, args, note). The note is the decision or the spec section.
"""
from fractions import Fraction

import model as M
import sets as S
from model import FLOATS, INTS, int_range
import ops as O


def named_cases(by_id):
    out = []

    def add(op_id, args, note):
        if op_id in by_id:
            out.append((op_id, tuple(args), note))

    # S-106: to_bits() of every kind of NaN is the positive quiet NaN; from_bits keeps the pattern
    for ft in FLOATS:
        p = M.fparams(ft)[1]
        w = M.fparams(ft)[0]
        pats = [S.fnan_bits(ft, 0, 1), S.fnan_bits(ft, 1, 1), S.fnan_bits(ft, 0, 1 << (p - 2)),
                S.fnan_bits(ft, 1, 1 << (p - 2)), S.fnan_bits(ft, 1, (1 << (p - 1)) - 1),
                S.fnan_bits(ft, 0, (1 << (p - 1)) - 1)]
        for b in pats:
            add(f"{ft}.to_bits", (b,), "S-106")
            add(f"{ft}.from_bits", (b,), "S-106")
        add(f"{ft}.to_bits", (M.fenc_zero(ft, 1),), "S-106")
        add(f"{ft}.from_bits", (1 << (w - 1),), "S-106")
    # 3.4: MIN % -1 is 0, MIN / -1 and -MIN overflow
    for t, (n, sg) in INTS.items():
        if not sg:
            continue
        lo, _ = int_range(t)
        for name in ("rem", "rem_euclid", "checked_rem", "checked_rem_euclid", "div", "div_euclid",
                     "checked_div", "checked_div_euclid"):
            add(f"{t}.{name}", (lo, -1), "§3.4")
        for name in ("neg", "abs", "checked_neg"):
            add(f"{t}.{name}", (lo,), "§3.4")
    # S-189: the truncated value decides: -0.9 -> 0, -1.0 -> panic for unsigned, MAX + 0.9 fits
    for src in FLOATS:
        for dst in INTS:
            lo, hi = int_range(dst)
            cands = [Fraction(-9, 10), Fraction(-1), Fraction(hi) + Fraction(9, 10), Fraction(lo) - Fraction(9, 10)]
            bits = [M.fq(src, c) for c in cands] + [M.fenc_zero(src, 1)]
            for form in (f"trunc_{dst}", f"trunc_{dst}_sat"):
                for b in bits:
                    add(f"{src}.{form}", (b,), "S-189")
    # 3.3: the ends of the target for every narrow pair
    for src in INTS:
        for dst in INTS:
            if src != dst and "narrow" in O.conv_forms(src, dst):
                slo, shi = int_range(src)
                dlo, dhi = int_range(dst)
                for x in (dlo - 1, dlo, dhi, dhi + 1):
                    if slo <= x <= shi:
                        add(f"{src}.narrow_{dst}", (x,), "§3.3")
    # 3.3: one rounding from a 64-bit integer to F32 (not through F64)
    for src in ("i64", "u64"):
        for k in (54, 58, 62) + ((63,) if src == "u64" else ()):
            x = (1 << k) + (1 << (k - 24)) + 1
            add(f"{src}.round_f32", (x,), "§3.3")
            if src == "i64":
                add(f"{src}.round_f32", (-x,), "§3.3")
    add("u64.round_f64", ((1 << 64) - 1,), "§3.3")
    # 3.3: F64 -> F32 at the overflow edge (ties to even) and the subnormal edge
    w, p, emax, emin = M.fparams("f32")
    maxf = Fraction(2 ** p - 1, 2 ** (p - 1)) * Fraction(2) ** emax
    for q in (maxf, maxf + Fraction(2) ** (emax - p), Fraction(2) ** (emin - (p - 1)) / 2,
              Fraction(2) ** (emin - (p - 1)) * 3 / 2):
        add("f64.round_f32", (M.fq("f64", q),), "§3.3")
    # S-194: the two-multiplication form at the ends; 0 * inf is NaN
    for t in FLOATS:
        w, p, emax, emin = M.fparams(t)
        maxb = S.fmax_bits(t)
        neg_max = maxb ^ (1 << (w - 1))
        for f in (Fraction(0), Fraction(1, 2), Fraction(1)):
            add(f"{t}.expr_interp", (neg_max, maxb, M.fq(t, f)), "S-194")
        one = M.fq(t, Fraction(1))
        add(f"{t}.expr_interp", (one, M.fenc_inf(t, 0), M.fenc_zero(t, 0)), "S-194")
        add(f"{t}.expr_interp", (one, S.fnan_bits(t, 0, 1 << (p - 2)), M.fenc_zero(t, 0)), "S-194")
        add(f"{t}.expr_interp", (M.fenc_inf(t, 0), one, M.fq(t, Fraction(1))), "S-194")
    # S-207 / S-208 / S-209 (3.4): the sign of a zero result, abs(-0.0), finite % infinity
    for t in FLOATS:
        w, p, emax, emin = M.fparams(t)
        pz, nz = M.fenc_zero(t, 0), M.fenc_zero(t, 1)
        inf, ninf = M.fenc_inf(t, 0), M.fenc_inf(t, 1)
        q = lambda x: M.fq(t, Fraction(x))
        one, mone, tiny = q(1), q(-1), q(Fraction(1, 10 ** 30)) if t == "f32" else q(Fraction(1, 10 ** 200))
        for a, b in ((one, mone), (nz, nz), (nz, pz), (pz, nz), (q(Fraction(-7, 2)), q(Fraction(-7, 2)))):
            add(f"{t}.add", (a, b), "S-207")
            add(f"{t}.sub", (a, b), "S-207")
        for a, b in ((pz, mone), (nz, nz), (mone, inf), (tiny, M.fneg_bits(t, tiny))):
            add(f"{t}.mul", (a, b), "S-207")
            add(f"{t}.div", (a, b), "S-207")
        add(f"{t}.mul", (M.fneg_bits(t, tiny), tiny), "S-207")      # a product that rounds to -0.0
        add(f"{t}.sqrt", (nz,), "S-207")
        for name in ("floor", "ceil", "trunc", "round"):
            for x in (pz, nz, q(Fraction(-2, 5)), q(Fraction(-1, 2)), q(Fraction(2, 5)), q(Fraction(1, 2))):
                add(f"{t}.{name}", (x,), "S-207")
        for x in (pz, nz, one, mone):
            add(f"{t}.abs", (x,), "S-208")
        for a in (one, mone, pz, nz, S.fmax_bits(t)):
            for b in (inf, ninf):
                add(f"{t}.rem", (a, b), "S-209")
        add(f"{t}.rem", (q(-4), q(2)), "S-207")                     # the sign of a, 0 left over
        # 11.4: f = dc - k is +0.0 for an integer d; a = -0.0 with f = +0.0 gives +0.0
        add(f"{t}.expr_interp", (nz, one, pz), "S-207")
        add(f"{t}.expr_interp", (nz, nz, pz), "S-207")
        add(f"{t}.expr_interp", (one, mone, q(Fraction(1, 2))), "S-207")
        for d, m in ((q(1), 1), (q(2), 100), (q(3), 100), (q(100), 100), (q(Fraction(3, 2)), 100)):
            add(f"{t}.vdelay_f", (d, m), "S-207")
    for x in (M.fenc_zero("f64", 1), M.fq("f64", -Fraction(1, 10 ** 300)), M.fq("f64", Fraction(1, 10 ** 300))):
        add("f64.round_f32", (x,), "S-207")        # a zero keeps its sign; a value that rounds to zero too
    add("f32.as_f64", (M.fenc_zero("f32", 1),), "S-207")
    for it in INTS:     # an integer 0 is +0.0 as a float, by `as` and by `round_f32` / `round_f64`
        for ft in FLOATS:
            add(f"{it}.{O.conv_forms(it, ft)[0]}_{ft}", (0,), "S-207")
    # S-210: `as` to the same type changes nothing (the sign of a zero, every kind of NaN, the ends of an integer)
    for ft in FLOATS:
        w, p, emax, emin = M.fparams(ft)
        for x in (M.fenc_zero(ft, 1), M.fenc_zero(ft, 0), M.fenc_inf(ft, 1), S.fnan_bits(ft, 1, 1), S.fnan_bits(ft, 0, 1 << (p - 2)),
                  S.fb(ft, 0, 0, 1), S.fmax_bits(ft)):
            add(f"{ft}.as_{ft}", (x,), "S-210")
    for t in INTS:
        lo, hi = int_range(t)
        for x in (lo, hi, 0, 1):
            add(f"{t}.as_{t}", (x,), "S-210")
    # R-04: an unsigned 64-bit product that overflows, and one that does not
    for name in ("mul", "checked_mul", "wmul", "smul"):
        for a, b in ((1 << 32, 1 << 32), ((1 << 32) - 1, (1 << 32) + 1), (1 << 63, 2)):
            add(f"u64.{name}", (a, b), "R-04")
    return out
