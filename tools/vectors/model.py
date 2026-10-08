"""The reference model of the test vectors (W2-01, Q-02 (a), R-133).

One small function per rule of spec sections 3.3 and 3.4 (and the formulas of
11.4). Only Python integers and Fractions: no Python float, no `random`, no libm.
The exact result is computed first and rounded once, by `round_to`, which is the
roundTiesToEven of the spec. The spec and the data are the norm; this program is
the way to rebuild the data.

A result is one of: ("v", value) | NAN | ("panic", kind) | ("none",) | ("some", value).
A float value is its IEEE bit pattern (an int); an integer value is a Python int.

Where a rule is not written in the spec, the model sets a hold in `Ctx.hold(code)`; the
generator then writes the row with the expected value `?` in a `held-` section. Nothing is
held now: S-207 (the sign of a zero result, 3.4), S-208 (`abs(-0.0)`) and S-209 (finite %
infinity) were decided on 2026-10-08 and the rules are written in 3.4; the holds were
removed in W2-12 and the rows are `edge` / `rand` rows.
"""
from fractions import Fraction
from math import isqrt

INTS = {
    "i8": (8, True), "i16": (16, True), "i32": (32, True), "i64": (64, True),
    "u8": (8, False), "u16": (16, False), "u32": (32, False), "u64": (64, False),
}
FLOATS = {"f32": (32, 24, 127), "f64": (64, 53, 1023)}  # width, precision, emax
NUM = list(INTS) + list(FLOATS)
NAN = ("nan",)

# The holds: S numbers ("S207") of the gaps in the spec that make an expected value undecidable.
# None now. To hold a row, call `Ctx.hold("S<number>")` in the rule that the spec does not give;
# the generator writes the row with `?` in a `held-S<number>` section (tests/vectors/FORMAT.md).


class Ctx:
    holds = set()

    @staticmethod
    def reset():
        Ctx.holds = set()

    @staticmethod
    def hold(code):
        Ctx.holds.add(code)


def decide(fn, args):
    """Evaluate `fn(args)` and say which gaps in the spec the answer depends on: (result, [S number])."""
    Ctx.reset()
    r = fn(args)
    holds = sorted(Ctx.holds)
    Ctx.reset()
    return r, holds


def int_range(t):
    n, s = INTS[t]
    return (-(1 << (n - 1)), (1 << (n - 1)) - 1) if s else (0, (1 << n) - 1)


# ---------------------------------------------------------------- floats
def fparams(t):
    w, p, emax = FLOATS[t]
    return w, p, emax, 1 - emax


def fdec(t, bits):
    """bits -> ('nan', sign, payload) | ('inf', sign) | ('fin', sign, Fraction abs)"""
    w, p, emax, emin = fparams(t)
    ebits = w - p
    sign = bits >> (w - 1)
    e = (bits >> (p - 1)) & ((1 << ebits) - 1)
    m = bits & ((1 << (p - 1)) - 1)
    if e == (1 << ebits) - 1:
        return ("nan", sign, m) if m else ("inf", sign)
    if e == 0:
        return ("fin", sign, Fraction(m) * Fraction(2) ** (emin - (p - 1)))
    return ("fin", sign, Fraction(m | (1 << (p - 1))) * Fraction(2) ** (e - emax - (p - 1)))


def fenc_inf(t, sign):
    w, p, _, _ = fparams(t)
    return (sign << (w - 1)) | (((1 << (w - p)) - 1) << (p - 1))


def fenc_zero(t, sign):
    return sign << (fparams(t)[0] - 1)


def round_to(t, sign, q):
    """Round the positive exact value q to format t (roundTiesToEven); return the bits."""
    w, p, emax, emin = fparams(t)
    assert q > 0
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    assert Fraction(2) ** e <= q < Fraction(2) ** (e + 1)
    if e < emin:
        e = emin
    m = q / Fraction(2) ** (e - (p - 1))  # the significand on the integer grid
    fl = m.numerator // m.denominator
    rem = m - fl
    if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and fl & 1):
        fl += 1
    if fl == 1 << p:
        fl >>= 1
        e += 1
    if e > emax:
        return fenc_inf(t, sign)
    # fl == 0: a nonzero exact value rounded to zero keeps the sign of the exact value (3.4)
    if fl < (1 << (p - 1)):  # subnormal (e == emin)
        return (sign << (w - 1)) | fl
    return (sign << (w - 1)) | ((e + emax) << (p - 1)) | (fl & ((1 << (p - 1)) - 1))


def is_nan(t, bits):
    return fdec(t, bits)[0] == "nan"


def fval(t, bits):
    """The signed exact value of a finite float, or None."""
    d = fdec(t, bits)
    if d[0] != "fin":
        return None
    return -d[2] if d[1] else d[2]


def fq(t, q):
    """The float nearest to the exact value q (a Fraction)."""
    if q == 0:
        return fenc_zero(t, 0)
    return round_to(t, 1 if q < 0 else 0, abs(q))


def fneg_bits(t, a):
    return a ^ (1 << (fparams(t)[0] - 1))


def _zero_result(t, sign):
    return ("v", fenc_zero(t, sign))


def f_add(t, a, b):
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan":
        return NAN
    if da[0] == "inf" or db[0] == "inf":
        if da[0] == "inf" and db[0] == "inf":
            return NAN if da[1] != db[1] else ("v", a)
        return ("v", a if da[0] == "inf" else b)
    x, y = fval(t, a), fval(t, b)
    s = x + y
    if s == 0:
        # 3.4 (S-207): an exact zero sum is -0.0 only when both operands are -0.0, otherwise +0.0
        # (a - b is a + (-b), see f_sub).
        return _zero_result(t, da[1] if (x == 0 and y == 0 and da[1] == db[1]) else 0)
    return ("v", round_to(t, 1 if s < 0 else 0, abs(s)))


def f_sub(t, a, b):
    if is_nan(t, b):
        return NAN
    return f_add(t, a, fneg_bits(t, b))


def f_mul(t, a, b):
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan":
        return NAN
    sign = da[1] ^ db[1]
    za = da[0] == "fin" and da[2] == 0
    zb = db[0] == "fin" and db[2] == 0
    if da[0] == "inf" or db[0] == "inf":
        return NAN if (za or zb) else ("v", fenc_inf(t, sign))
    if za or zb:
        return _zero_result(t, sign)
    return ("v", round_to(t, sign, da[2] * db[2]))


def f_div(t, a, b):
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan":
        return NAN
    sign = da[1] ^ db[1]
    za = da[0] == "fin" and da[2] == 0
    zb = db[0] == "fin" and db[2] == 0
    if da[0] == "inf":
        return NAN if db[0] == "inf" else ("v", fenc_inf(t, sign))
    if db[0] == "inf":
        return _zero_result(t, sign)
    if zb:
        return NAN if za else ("v", fenc_inf(t, sign))  # nonzero / 0: a signed infinity (3.4)
    if za:
        return _zero_result(t, sign)
    return ("v", round_to(t, sign, da[2] / db[2]))


def f_rem(t, a, b):
    """fmod: a - b * trunc(a / b), exact, the sign of a (3.4)."""
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan" or da[0] == "inf":
        return NAN
    if db[0] == "inf":
        return ("v", a)  # 3.4 (S-209): a finite a % an infinity is a, -0.0 kept
    if db[2] == 0:
        return NAN
    x, y = da[2], db[2]
    q = x / y
    r = x - y * (q.numerator // q.denominator)
    if r == 0:
        return ("v", fenc_zero(t, da[1]))
    bits = round_to(t, da[1], r)
    assert fval(t, bits) == (-r if da[1] else r), "fmod must be exact"
    return ("v", bits)


def f_sqrt(t, a):
    w, p, emax, emin = fparams(t)
    d = fdec(t, a)
    if d[0] == "nan":
        return NAN
    if d[0] == "inf":
        return NAN if d[1] else ("v", a)
    if d[2] == 0:
        return _zero_result(t, d[1])  # 3.4 (S-207): sqrt(-0.0) is -0.0
    if d[1]:
        return NAN
    q = d[2]
    s = p + 6
    while True:  # scale so that the integer root has at least p + 3 bits
        n = q.numerator * (1 << (2 * s)) // q.denominator
        r = isqrt(n)
        if r.bit_length() >= p + 3:
            break
        s += 2
    exact = (n * q.denominator == q.numerator * (1 << (2 * s))) and r * r == n
    val = Fraction(r, 1 << s) if exact else Fraction(2 * r + 1, 1 << (s + 1))
    return ("v", round_to(t, 0, val))


def f_cmp(t, a, b):
    """-1, 0, 1, or None when unordered (a NaN)."""
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan":
        return None

    def key(d, bits):
        if d[0] == "inf":
            return Fraction(10 ** 400) * (-1 if d[1] else 1)
        return fval(t, bits)
    ka, kb = key(da, a), key(db, b)
    return (ka > kb) - (ka < kb)


def f_compare_op(t, op, a, b):
    c = f_cmp(t, a, b)
    if c is None:
        return ("v", op == "ne")
    return ("v", {"eq": c == 0, "ne": c != 0, "lt": c < 0, "le": c <= 0, "gt": c > 0, "ge": c >= 0}[op])


def f_floorlike(t, a, mode):
    d = fdec(t, a)
    if d[0] == "nan":
        return NAN
    if d[0] == "inf":
        return ("v", a)
    x = fval(t, a)
    if x == 0:
        return _zero_result(t, d[1])  # 3.4 (S-207): floor ceil trunc round keep the sign of the operand
    fl = x.numerator // x.denominator
    if mode == "floor":
        r = Fraction(fl)
    elif mode == "ceil":
        r = Fraction(fl + (0 if x == fl else 1))
    elif mode == "trunc":
        r = Fraction(fl + (1 if (x < 0 and x != fl) else 0))
    else:  # round: nearest, ties to even
        diff = x - fl
        r = Fraction(fl + 1) if (diff > Fraction(1, 2) or (diff == Fraction(1, 2) and fl & 1)) else Fraction(fl)
    if r == 0:
        return _zero_result(t, d[1])  # 3.4 (S-207): the sign of the operand (ceil(-0.5) is -0.0)
    return ("v", round_to(t, 1 if r < 0 else 0, abs(r)))


def f_abs(t, a):
    d = fdec(t, a)
    if d[0] == "nan":
        return NAN
    if d[0] == "fin" and d[2] == 0:
        return _zero_result(t, 0)  # 3.4 (S-208): the sign bit cleared, abs(-0.0) is +0.0
    return ("v", a & ~(1 << (fparams(t)[0] - 1)))


def f_minmax(t, a, b, which):
    """NaN propagates; -0.0 < 0.0 (3.4)."""
    da, db = fdec(t, a), fdec(t, b)
    if da[0] == "nan" or db[0] == "nan":
        return NAN
    c = f_cmp(t, a, b)
    if c == 0:
        if da[0] == "fin" and da[2] == 0 and da[1] != db[1]:
            neg, pos = (a, b) if da[1] else (b, a)
            return ("v", neg if which == "min" else pos)
        return ("v", a)
    return ("v", a if (c < 0) == (which == "min") else b)


def f_neg(t, a):
    return NAN if is_nan(t, a) else ("v", fneg_bits(t, a))


def float_op(t, op, args):
    if op in ("eq", "ne", "lt", "le", "gt", "ge"):
        return f_compare_op(t, op, *args)
    if op in ("add", "sub", "mul", "div", "rem"):
        return {"add": f_add, "sub": f_sub, "mul": f_mul, "div": f_div, "rem": f_rem}[op](t, *args)
    if op in ("min", "max"):
        return f_minmax(t, args[0], args[1], op)
    a = args[0]
    if op == "neg":
        return f_neg(t, a)
    if op == "sqrt":
        return f_sqrt(t, a)
    if op in ("floor", "ceil", "trunc", "round"):
        return f_floorlike(t, a, op)
    if op == "abs":
        return f_abs(t, a)
    if op == "is_nan":
        return ("v", is_nan(t, a))
    if op == "is_finite":
        return ("v", fdec(t, a)[0] == "fin")
    raise KeyError(op)


# ------------------------------------------------------------ conversions
def int_to_float(t, x):
    if x == 0:
        return ("v", fenc_zero(t, 0))
    return ("v", round_to(t, 1 if x < 0 else 0, Fraction(abs(x))))


def float_to_int(t, bits, it, sat):
    """trunc_<it>() / trunc_<it>_sat(): toward zero; out of range and NaN panic, or saturate (3.3, S-189)."""
    lo, hi = int_range(it)
    d = fdec(t, bits)
    if d[0] == "nan":
        return ("v", 0) if sat else ("panic", "nan")
    if d[0] == "inf":
        return ("v", lo if d[1] else hi) if sat else ("panic", "range")
    x = fval(t, bits)
    tr = x.numerator // x.denominator if x >= 0 else -((-x).numerator // (-x).denominator)
    if lo <= tr <= hi:  # judged after the truncation: -0.9 -> 0 fits an unsigned type
        return ("v", tr)
    if sat:
        return ("v", lo if tr < lo else hi)
    return ("panic", "range")


def float_to_float(src, dst, bits):
    d = fdec(src, bits)
    if d[0] == "nan":
        return NAN
    if d[0] == "inf":
        return ("v", fenc_inf(dst, d[1]))
    if d[2] == 0:
        return _zero_result(dst, d[1])
    return ("v", round_to(dst, d[1], d[2]))


def float_widen(src, dst, bits):
    """`as` F32 -> F64: the value does not change, the zero keeps its sign (3.3)."""
    d = fdec(src, bits)
    if d[0] == "nan":
        return NAN
    if d[0] == "inf":
        return ("v", fenc_inf(dst, d[1]))
    if d[2] == 0:
        return ("v", fenc_zero(dst, d[1]))
    return ("v", round_to(dst, d[1], d[2]))


def to_bits(t, bits):
    """to_bits() of a NaN is the positive quiet NaN as an integer (3.4, S-106)."""
    if is_nan(t, bits):
        return 0x7FC00000 if t == "f32" else 0x7FF8000000000000
    return bits


def from_bits(t, u):
    return NAN if is_nan(t, u) else ("v", u)


# ------------------------------------------------------------------ ints
def wrap(t, x):
    n, s = INTS[t]
    x &= (1 << n) - 1
    if s and x >> (n - 1):
        x -= 1 << n
    return x


def trunc_div(a, b):
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


def int_op(t, op, args):
    n, s = INTS[t]
    lo, hi = int_range(t)
    a = args[0]
    b = args[1] if len(args) > 1 else None
    mask = (1 << n) - 1

    def chk(x, kind="overflow"):
        return ("v", x) if lo <= x <= hi else ("panic", kind)

    if op == "add": return chk(a + b)
    if op == "sub": return chk(a - b)
    if op == "mul": return chk(a * b)
    if op == "div":
        if b == 0: return ("panic", "div-zero")
        return chk(trunc_div(a, b))
    if op == "rem":
        if b == 0: return ("panic", "div-zero")
        return ("v", a - trunc_div(a, b) * b)  # MIN % -1 is 0 (3.4)
    if op == "neg": return chk(-a)
    if op == "shl":
        if b >= n: return ("panic", "shift")
        return ("v", wrap(t, a << b))
    if op == "shr":
        if b >= n: return ("panic", "shift")
        return ("v", a >> b)
    if op == "wadd": return ("v", wrap(t, a + b))
    if op == "wsub": return ("v", wrap(t, a - b))
    if op == "wmul": return ("v", wrap(t, a * b))
    if op == "sadd": return ("v", min(max(a + b, lo), hi))
    if op == "ssub": return ("v", min(max(a - b, lo), hi))
    if op == "smul": return ("v", min(max(a * b, lo), hi))
    if op == "div_euclid":
        if b == 0: return ("panic", "div-zero")
        m = abs(b)
        r = a % m
        q = (a - r) // b
        assert a == q * b + r and 0 <= r < m
        return chk(q)
    if op == "rem_euclid":
        if b == 0: return ("panic", "div-zero")
        return ("v", a % abs(b))  # MIN.rem_euclid(-1) is 0 (3.4)
    if op == "and": return ("v", wrap(t, (a & mask) & (b & mask)))
    if op == "or": return ("v", wrap(t, (a & mask) | (b & mask)))
    if op == "xor": return ("v", wrap(t, (a & mask) ^ (b & mask)))
    if op == "not": return ("v", wrap(t, ~(a & mask)))
    if op in ("eq", "ne", "lt", "le", "gt", "ge"):
        return ("v", {"eq": a == b, "ne": a != b, "lt": a < b, "le": a <= b, "gt": a > b, "ge": a >= b}[op])
    if op == "abs": return chk(abs(a))
    if op == "min": return ("v", b if b < a else a)  # the std body: if b < a { b } else { a }
    if op == "max": return ("v", b if a < b else a)
    if op.startswith("checked_"):
        r = int_op(t, op[8:], args)
        return ("none",) if r[0] == "panic" else ("some", r[1])
    raise KeyError(op)


def int_narrow(dst, x):
    lo, hi = int_range(dst)
    return ("some", x) if lo <= x <= hi else ("none",)


# ------------------------------------------------ 11.4: interpolation, index
def f_one(t):
    return fq(t, Fraction(1))


def _chain(fn1, fn2, t, x, y, z):
    """fn2(fn1(x, y), z) with NaN propagation."""
    r = fn1(t, x, y)
    return NAN if r == NAN else fn2(t, r[1], z)


def expr_muladd(t, a, b, c):
    return _chain(f_mul, f_add, t, a, b, c)


def expr_mulsub(t, a, b, c):
    return _chain(f_mul, f_sub, t, a, b, c)


def expr_add3_l(t, a, b, c):
    return _chain(f_add, f_add, t, a, b, c)


def expr_add3_r(t, a, b, c):
    r = f_add(t, b, c)
    return NAN if r == NAN else f_add(t, a, r[1])


def expr_interp(t, a, b, f):
    """y = (1.0 - f) * a + f * b (11.4, S-194)."""
    om = f_sub(t, f_one(t), f)
    if om == NAN:
        return NAN
    l = f_mul(t, om[1], a)
    r = f_mul(t, f, b)
    if l == NAN or r == NAN:
        return NAN
    return f_add(t, l[1], r[1])


def fused_muladd(t, a, b, c):
    """a * b + c rounded once. Only to pick inputs that tell a fused result from the two roundings."""
    if any(fdec(t, x)[0] != "fin" for x in (a, b, c)):
        return None
    x = fval(t, a) * fval(t, b) + fval(t, c)
    return round_to(t, 1 if x < 0 else 0, abs(x)) if x != 0 else None


def vdelay_kf(t, d, maxv):
    """dc, k, f of 11.4. Returns (k, f_result)."""
    maxb = fq(t, Fraction(maxv))
    c1 = f_cmp(t, d, f_one(t))
    if c1 is not None and c1 >= 0:
        le = f_cmp(t, d, maxb)
        dc = d if (le is not None and le <= 0) else maxb
    else:
        dc = f_one(t)  # d < 1, and a NaN
    k = float_to_int(t, dc, "u32", False)
    assert k[0] == "v" and 1 <= k[1] <= maxv
    return k[1], f_sub(t, dc, int_to_float(t, k[1])[1])


def selftest():
    """Known answers. Run on every generation."""
    t = "f32"
    assert f_add(t, 0x3F800000, 0x3F800000) == ("v", 0x40000000)
    assert f_sqrt(t, 0x40000000) == ("v", 0x3FB504F3)
    assert f_sqrt("f64", 0x4000000000000000) == ("v", 0x3FF6A09E667F3BCD)
    assert round_to("f32", 0, Fraction(1, 3)) == 0x3EAAAAAB
    assert round_to("f64", 0, Fraction(1, 3)) == 0x3FD5555555555555
    assert round_to("f32", 0, Fraction(2) ** 128) == 0x7F800000
    assert int_op("i32", "rem", (-2 ** 31, -1)) == ("v", 0)
    assert int_op("i32", "div", (-2 ** 31, -1)) == ("panic", "overflow")
    assert float_to_int("f64", 0xBFECCCCCCCCCCCCD, "u64", False) == ("v", 0)
    assert float_to_int("f64", 0xBFF0000000000000, "u32", False) == ("panic", "range")
    assert to_bits("f32", 0xFFC00001) == 0x7FC00000
    # 3.4, the sign of a zero result (S-207), abs (S-208), finite % infinity (S-209): the answers written
    # by hand from the rules in the spec, so that a change of the model cannot move the expected values.
    pz, nz, inf, ninf = 0x00000000, 0x80000000, 0x7F800000, 0xFF800000
    one, mone, half, mhalf = 0x3F800000, 0xBF800000, 0x3F000000, 0xBF000000
    assert f_add(t, one, mone) == ("v", pz)                    # an exact zero sum is +0.0 ...
    assert f_add(t, nz, nz) == ("v", nz)                       # ... unless both are -0.0
    assert f_add(t, nz, pz) == ("v", pz) and f_add(t, pz, nz) == ("v", pz)
    assert f_sub(t, nz, pz) == ("v", nz)                       # a - b is a + (-b)
    assert f_sub(t, pz, pz) == ("v", pz) and f_sub(t, 0x40600000, 0x40600000) == ("v", pz)
    assert f_mul(t, pz, mone) == ("v", nz) and f_mul(t, nz, nz) == ("v", pz)     # the xor of the signs
    assert f_div(t, pz, mone) == ("v", nz) and f_div(t, mone, inf) == ("v", nz)
    tiny = fq(t, Fraction(1, 10 ** 30))
    assert f_mul(t, fneg_bits(t, tiny), tiny) == ("v", nz) and f_mul(t, tiny, tiny) == ("v", pz)  # rounds to zero
    assert f_sqrt(t, nz) == ("v", nz) and f_sqrt(t, pz) == ("v", pz)
    assert f_floorlike(t, nz, "floor") == ("v", nz) and f_floorlike(t, pz, "floor") == ("v", pz)
    assert f_floorlike(t, mhalf, "ceil") == ("v", nz) and f_floorlike(t, mhalf, "trunc") == ("v", nz)
    assert f_floorlike(t, mhalf, "round") == ("v", nz) and f_floorlike(t, half, "round") == ("v", pz)
    assert f_floorlike(t, half, "floor") == ("v", pz) and f_floorlike(t, half, "trunc") == ("v", pz)
    assert float_to_float("f64", "f32", 0x8000000000000000) == ("v", nz)   # F64 -> F32 keeps the sign of a zero
    assert float_to_float("f64", "f32", fq("f64", -Fraction(1, 10 ** 300))) == ("v", nz)  # and of a rounded-to-zero
    assert float_widen("f32", "f64", nz) == ("v", 0x8000000000000000)
    assert int_to_float("f32", 0) == ("v", pz)
    assert f_abs(t, nz) == ("v", pz) and f_abs(t, pz) == ("v", pz) and f_abs(t, mone) == ("v", one)
    assert f_rem(t, one, inf) == ("v", one) and f_rem(t, mone, ninf) == ("v", mone)
    assert f_rem(t, nz, inf) == ("v", nz) and f_rem(t, 0xC0800000, 0x40000000) == ("v", nz)   # -4.0 % 2.0 has the sign of a
    assert f_rem(t, 0x7F7FFFFF, inf) == ("v", 0x7F7FFFFF)
    assert f_rem(t, inf, one) == NAN and f_rem(t, one, pz) == NAN
    # 11.4 consequences of the rules above: an integer d gives f = dc - k = +0.0; a = -0.0, f = +0.0 gives +0.0
    k, f = vdelay_kf(t, 0x40000000, 100)
    assert (k, f) == (2, ("v", pz))
    assert expr_interp(t, nz, one, pz) == ("v", pz)
    # S-211: PI is checked in ops.py
    Ctx.reset()
