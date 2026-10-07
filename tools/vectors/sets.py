"""How the inputs are chosen (W2-01): rules of the type, not hand-written lists.

The random stream is splitmix64 (the same five lines can be written in any language),
seeded per operation: state = SEED xor FNV-1a-64(key). Adding an operation does not
change the values of the others. tests/vectors/FORMAT.md says the same.
"""
from fractions import Fraction
from math import isqrt

from model import (FLOATS, INTS, NUM, fenc_inf, fenc_zero, fparams, fq, int_range, round_to, fdec)

SEED = 0x4F4E5341  # "ONSA"
M64 = (1 << 64) - 1

RAND_INT = 96     # random operand pairs per binary integer operation
RAND_SHIFT = 48
RAND_FLT = 128
RAND_UNARY = 128
RAND_CONV = 48


class Rng:
    def __init__(self, s):
        self.s = s & M64

    def next(self):
        self.s = (self.s + 0x9E3779B97F4A7C15) & M64
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
        return z ^ (z >> 31)

    def below(self, n):
        return self.next() % n

    def bits(self, k):
        return self.next() >> (64 - k) if k else 0


def fnv1a64(s):
    h = 0xCBF29CE484222325
    for ch in s.encode():
        h = ((h ^ ch) * 0x100000001B3) & M64
    return h


def stream(key):
    return Rng(SEED ^ fnv1a64(key))


def dedup(seq):
    seen = set()
    out = []
    for x in seq:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def named_unique(pairs, lo=None, hi=None):
    """[(value, name)] -> sorted by value, one name per value (the first), within [lo, hi]."""
    d = {}
    for v, n in pairs:
        if (lo is None or lo <= v <= hi) and v not in d:
            d[v] = n
    return sorted(d.items())


# ---------------------------------------------------------------- integers
def int_core_named(t):
    n, s = INTS[t]
    lo, hi = int_range(t)
    r = isqrt(hi)
    h = n // 2
    p = [(0, "0"), (1, "1"), (2, "2"), (3, "3"), (hi, "MAX"), (hi - 1, "MAX-1"), (hi - 2, "MAX-2"),
         (hi // 2, "MAX/2"), (hi // 2 + 1, "MAX/2+1"), (r, "isqrt(MAX)"), (r + 1, "isqrt(MAX)+1"),
         ((1 << h) - 1, f"2^{h}-1"), (1 << h, f"2^{h}"), ((1 << h) + 1, f"2^{h}+1")]
    if s:
        p += [(-1, "-1"), (-2, "-2"), (-3, "-3"), (lo, "MIN"), (lo + 1, "MIN+1"), (lo + 2, "MIN+2"),
              (lo // 2, "MIN/2"), (-r, "-isqrt(MAX)"), (-(r + 1), "-(isqrt(MAX)+1)"),
              (-((1 << h) - 1), f"-(2^{h}-1)"), (-(1 << h), f"-2^{h}"), (-((1 << h) + 1), f"-(2^{h}+1)")]
    return named_unique(p, lo, hi)


def int_core(t):
    return [v for v, _ in int_core_named(t)]


def int_wide(t):
    """Unary operations and the sources of conversions: every value of an 8-bit type;
    otherwise the core, +-10, +-100, the ends of every integer type +-1, and 2^k, 2^k - 1."""
    n, _ = INTS[t]
    lo, hi = int_range(t)
    if n == 8:
        return list(range(lo, hi + 1))
    v = set(int_core(t)) | {10, 100, -10, -100}
    for u in INTS:
        ulo, uhi = int_range(u)
        for b in (ulo, uhi):
            for d in (-1, 0, 1):
                v.add(b + d)
    for k in range(n):
        v.add(1 << k)
        v.add((1 << k) - 1)
    return sorted(x for x in v if lo <= x <= hi)


def int_random(t, key, count):
    r = stream(key)
    n, s = INTS[t]
    lo, hi = int_range(t)
    core = int_core(t)
    out = []
    for _ in range(count):
        m = r.below(4)
        if m == 0:
            x = lo + r.next() % (hi - lo + 1)          # uniform over the range
        elif m == 1:
            x = r.bits(r.below(n) + 1)                  # uniform bit length
            if s and r.below(2):
                x = -x
        elif m == 2:
            x = core[r.below(len(core))] + (r.below(5) - 2)   # near a core value
        else:
            x = r.below(200) - (100 if s else 0)        # small
        out.append(max(lo, min(hi, x)))
    return out


def shift_counts(t):
    n = INTS[t][0]
    return sorted({0, 1, 2, n - 2, n - 1, n, n + 1, 2 * n, 31, 32, 33, 63, 64, 65, 255, 1 << 31, (1 << 32) - 1})


# ------------------------------------------------------------------ floats
def fb(t, sign, e, m):
    """Bits from the sign, the biased exponent field and the mantissa field."""
    w, p, _, _ = fparams(t)
    return (sign << (w - 1)) | (e << (p - 1)) | m


def fmax_bits(t):
    w, p, _, _ = fparams(t)
    return fb(t, 0, (1 << (w - p)) - 2, (1 << (p - 1)) - 1)


def fnan_bits(t, sign, mant):
    w, p, _, _ = fparams(t)
    return fb(t, sign, (1 << (w - p)) - 1, mant)


def float_core_named(t):
    w, p, emax, emin = fparams(t)
    maxf = fmax_bits(t)
    sgn = 1 << (w - 1)
    q = lambda x: fq(t, x)
    pairs = [
        (fenc_zero(t, 0), "+0"), (fenc_zero(t, 1), "-0"), (fenc_inf(t, 0), "+inf"), (fenc_inf(t, 1), "-inf"),
        (fnan_bits(t, 0, 1 << (p - 2)), "+qNaN"), (fnan_bits(t, 1, (1 << (p - 2)) | 1), "-qNaN payload 1"),
        (fnan_bits(t, 0, 1), "+sNaN payload 1"), (fnan_bits(t, 1, (1 << (p - 1)) - 1), "-NaN all payload bits"),
        (q(Fraction(1)), "1"), (q(Fraction(-1)), "-1"), (q(Fraction(2)), "2"), (q(Fraction(1, 2)), "1/2"),
        (q(Fraction(3)), "3"), (q(Fraction(-3)), "-3"), (q(Fraction(1, 10)), "nearest 1/10"),
        (q(Fraction(1, 3)), "nearest 1/3"), (q(Fraction(10)), "10"), (q(Fraction(-5, 2)), "-5/2"),
        (q(Fraction(3, 2)), "3/2"), (maxf, "MAX"), (maxf | sgn, "-MAX"), (maxf - 1, "MAX-1ulp"),
        (fb(t, 0, 1, 0), "min normal"), (fb(t, 1, 1, 0), "-min normal"),
        (fb(t, 0, 0, (1 << (p - 1)) - 1), "max subnormal"),
        (fb(t, 0, 0, 1), "min subnormal"), (fb(t, 1, 0, 1), "-min subnormal"),
        (q(1 + Fraction(1, 2 ** (p - 1))), "1+eps"), (q(1 - Fraction(1, 2 ** p)), "1-eps/2"),
        (q(Fraction(2 ** (p - 1))), f"2^{p - 1}"), (q(Fraction(2 ** p)), f"2^{p}"),
        (q(Fraction(2 ** p + 2)), f"2^{p}+2"),
    ]
    return named_unique(pairs)


def float_core(t):
    return [v for v, _ in float_core_named(t)]


def float_wide(t):
    w, p, emax, emin = fparams(t)
    v = set(float_core(t))
    for e in (-300, -126, -24, -2, 2, 7, 15, 24, 31, 32, 53, 63, 64, 100, 126):
        x = Fraction(2) ** e
        v.add(fq(t, x))
        v.add(fq(t, -x))
    for x in (7, 100, 123456, 65535, 65536, 255, 256, 127, 128, 32767, 32768):
        for d in (Fraction(-9, 10), Fraction(0), Fraction(1, 2), Fraction(9, 10)):
            v.add(fq(t, Fraction(x) + d))
            v.add(fq(t, -(Fraction(x) + d)))
    return sorted(v)


def float_random(t, key, count):
    w, p, emax, emin = fparams(t)
    r = stream(key)
    core = float_core(t)
    out = []
    for _ in range(count):
        m = r.below(4)
        if m == 0:
            out.append(r.bits(w))                                   # uniform bits
        elif m == 1:
            out.append(fb(t, r.below(2), r.below(60) + emax - 30, r.bits(p - 1)))  # moderate exponents
        elif m == 2:
            x = core[r.below(len(core))]
            out.append(x if fdec(t, x)[0] == "nan" else x ^ (1 if r.below(2) else 0))  # a neighbour
        else:
            out.append(fq(t, Fraction(r.below(2000) - 1000, 1 + r.below(16))))     # small rationals
    return out


# ------------------------------------------------------ conversion inputs
def conv_ints(src, dst):
    """Integer source: the ends of the target (narrow, trunc is not here) or the rounding
    edges of the target float, with the double-rounding traps for I64 / U64 -> F32."""
    lo, hi = int_range(src)
    v = set()
    if dst in INTS:
        dlo, dhi = int_range(dst)
        for b in (dlo, dhi, 0):
            for d in (-1, 0, 1):
                v.add(b + d)
        v |= {lo, hi, lo + 1, hi - 1}
    else:
        w, p, _, _ = fparams(dst)
        for k in range(p - 2, INTS[src][0] + 1):
            for d in (-1, 0, 1, 2, 3):
                v.add((1 << k) + d)
                v.add((1 << k) - 1 + d)
        for k in (54, 56, 58, 60, 62, 63):  # F64 first, F32 second rounds differently from one rounding
            if k <= INTS[src][0]:
                x = (1 << k) + (1 << (k - 24)) + 1
                v.add(x)
                v.add(x - 2)
        v |= {lo, hi, 0, 1, 2}
    out = {x for x in v if lo <= x <= hi}
    if INTS[src][1]:
        out |= {-x for x in out if lo <= -x <= hi}
    return sorted(out)


def _mask(t, bits):
    return bits & ((1 << fparams(t)[0]) - 1)


def conv_floats(src, dst):
    """Float source: around the ends of the target integer (S-189: -0.9, -1.0, MAX + 0.9),
    or the ties, the overflow edge and the subnormal edge of the target float."""
    v = set(float_wide(src))
    if dst in INTS:
        dlo, dhi = int_range(dst)
        for b in (dlo, dhi + 1, dlo - 1, 0):
            for d in (Fraction(-3, 2), Fraction(-1), Fraction(-9, 10), Fraction(-1, 2), Fraction(0),
                      Fraction(1, 2), Fraction(9, 10), Fraction(1), Fraction(3, 2)):
                bits = fq(src, Fraction(b) + d)
                v.add(bits)
                if fdec(src, bits)[0] == "fin":
                    v.add(_mask(src, bits + 1))
                    v.add(_mask(src, bits - 1))
        v.add(fenc_zero(src, 0))
        v.add(fenc_zero(src, 1))
    else:
        w, p, emax, emin = fparams(dst)
        maxf = Fraction(2 ** p - 1, 2 ** (p - 1)) * Fraction(2) ** emax
        half = maxf + Fraction(2) ** (emax - p)
        mins = Fraction(2) ** (emin - (p - 1))
        tiny = Fraction(2) ** (emax - p - 3)
        for q in (maxf, half, maxf + tiny, half - tiny, mins / 2, mins * 3 / 2, mins / 4, mins * 5 / 2,
                  Fraction(2) ** emin * (1 - Fraction(1, 2 ** p)), Fraction(2) ** emin):
            for sgn in (1, -1):
                bits = fq(src, q * sgn)
                v.add(bits)
                v.add(_mask(src, bits + 1))
    return sorted(v)
