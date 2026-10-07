"""The registry of the operations (W2-01): the single source of the operation list.

Everything that depends on the list reads it here: the generator, OPS.tsv, the Onsa
fixture, the checks of tools/vectors/gen.py. The conversions are derived from the table
of spec 3.3 by `conv_forms`, not listed by hand; `check_registry` asserts that every
ordered pair of distinct numeric types has exactly the forms the table gives.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import model as M
import sets as S
from model import FLOATS, INTS, NUM, Ctx

# ---- the operation names by group (spec 3.4 tables)
INT_BIN = ["add", "sub", "mul", "div", "rem", "wadd", "wsub", "wmul", "sadd", "ssub", "smul",
           "div_euclid", "rem_euclid", "and", "or", "xor", "eq", "ne", "lt", "le", "gt", "ge", "min", "max"]
INT_SHIFT = ["shl", "shr"]
INT_CHECKED_BIN = ["checked_add", "checked_sub", "checked_mul", "checked_div", "checked_rem",
                   "checked_div_euclid", "checked_rem_euclid"]
INT_CHECKED_SHIFT = ["checked_shl", "checked_shr"]
INT_UN = ["not"]
INT_UN_SIGNED = ["neg", "abs", "checked_neg"]
FLT_BIN = ["add", "sub", "mul", "div", "rem", "eq", "ne", "lt", "le", "gt", "ge", "min", "max"]
FLT_UN = ["neg", "sqrt", "floor", "ceil", "trunc", "round", "abs", "is_nan", "is_finite"]
EXPR = ["expr_muladd", "expr_mulsub", "expr_add3_l", "expr_add3_r", "expr_interp", "vdelay_k", "vdelay_f"]
CMP = ("eq", "ne", "lt", "le", "gt", "ge")

# ---- the Onsa form and the spec tokens of an operation
BINOP = {"add": "+", "sub": "-", "mul": "*", "div": "/", "rem": "%", "wadd": "+%", "wsub": "-%", "wmul": "*%",
         "sadd": "+|", "ssub": "-|", "smul": "*|", "and": "&", "or": "|", "xor": "^", "shl": "<<", "shr": ">>",
         "eq": "==", "ne": "!=", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}
STD_MATH = {"abs", "min", "max", "sqrt", "floor", "ceil", "trunc", "round", "is_nan", "is_finite"}
CONSTS_INT = ["ZERO", "ONE", "MIN", "MAX", "BITS"]
CONSTS_FLT = ["ZERO", "ONE", "MAX", "EPSILON", "INFINITY", "NAN"]


# The fixture packages. `scalar` holds every operation `onsa check` accepts. The others hold the
# operations it does not accept yet, one package per cause, so that each package is one test case that
# waits for one work (tests/pending.toml) and the rest of the vectors run now. When the work is done,
# delete the rule: the operations fall back to `scalar` on the next generation (the function names do
# not change). Found by W2-01 on 2026-10-08.
PENDING_PACKAGES = [
    # E0010: `a * b + c` mixes the multiplicative and the additive group, which spec 3.1 allows (W3-07)
    ("mixed", lambda o: o.name in ("expr_muladd", "expr_mulsub", "expr_interp")),
    # E0413: the checked methods after `checked_div` do not exist yet (W5-02)
    ("checked", lambda o: o.group == "int" and o.name in (
        "checked_rem", "checked_div_euclid", "checked_rem_euclid", "checked_shl", "checked_shr", "checked_neg")),
    # E0302: `T.ZERO` and `T.ONE` do not exist yet (W5-05)
    ("zero_one", lambda o: o.group == "const" and o.name in ("ZERO", "ONE")),
    # E0302: std.math has no `is_nan` and `is_finite` yet (W5-02)
    ("predicates", lambda o: o.group == "float" and o.name in ("is_nan", "is_finite")),
]


def package_of(o):
    for name, rule in PENDING_PACKAGES:
        if rule(o):
            return name
    return "scalar"


def onsa_type(t):
    return {"bool": "Bool"}.get(t, t.upper())


@dataclass
class Op:
    id: str                 # "i32.add"
    ty: str                 # the type prefix of the id
    name: str
    group: str              # int | float | conv | expr | const
    args: tuple             # argument types: i8..u64, f32, f64
    ret: str                # a type, "bool", or "opt:<type>"
    spec: str               # where the rule is written
    tokens: tuple           # the spec tokens it covers (tools/vectors/spec_tokens.py)
    onsa: str               # the Onsa expression in a, b, c ("" when `body` is used)
    model: Callable         # args tuple -> result
    inputs: Callable        # () -> [(tier, args)]
    pkg: str = "scalar"     # the fixture package
    body: str = ""          # the multi-line Onsa body (vdelay)

    @property
    def fn(self):
        if self.group == "const":
            return f"const_{self.ty}_{self.name.lower()}"
        return self.id.replace(".", "_")

    @property
    def file(self):
        return "const" if self.group == "const" else f"{self.group}-{self.ty}"


# ------------------------------------------------------------ conversions
def conv_forms(src, dst):
    """The forms of spec 3.3 for the ordered pair (src, dst), src != dst. The table:
    as: same-sign widening, unsigned to a wider signed, F32 -> F64, I8 I16 U8 U16 -> F32,
        I8..I32 U8..U32 -> F64; narrow: the other integer pairs; trunc and trunc_sat:
        float -> integer; round: F64 -> F32 and the rest of integer -> float."""
    assert src != dst
    si, di = src in INTS, dst in INTS
    if si and di:
        sn, ss = INTS[src]
        dn, ds = INTS[dst]
        if dn > sn and (ss == ds or (not ss and ds)):
            return ["as"]
        return ["narrow"]
    if not si and di:
        return ["trunc", "trunc_sat"]
    if si and not di:
        sn = INTS[src][0]
        return ["as"] if sn <= (16 if dst == "f32" else 32) else ["round"]
    return ["as"] if src == "f32" else ["round"]


def check_registry(ops):
    """The registry covers the table: every ordered pair of distinct numeric types has exactly the
    forms of 3.3 (one, or two for float -> integer), and no operation id is repeated."""
    ids = [o.id for o in ops]
    assert len(ids) == len(set(ids)), "an operation id is repeated"
    assert len({o.fn for o in ops}) == len(ops), "two operations have the same fixture function"
    have = {}
    for o in ops:
        if o.group == "conv" and o.name.split("_")[0] in ("as", "narrow", "trunc", "round"):
            have.setdefault((o.ty, o.name), True)
    for src in NUM:
        for dst in NUM:
            if src == dst:
                continue
            for form in conv_forms(src, dst):
                name = {"as": f"as_{dst}", "narrow": f"narrow_{dst}", "trunc": f"trunc_{dst}",
                        "trunc_sat": f"trunc_{dst}_sat", "round": f"round_{dst}"}[form]
                assert (src, name) in have, f"missing conversion {src}.{name}"
                del have[(src, name)]
    assert not have, f"conversions outside the table: {sorted(have)}"


# --------------------------------------------------------------- inputs
def _with_rand(edge, rand):
    seen = set(edge)
    return [("edge", a) for a in edge] + [("rand", a) for a in S.dedup(rand) if a not in seen]


def int_bin_inputs(t, op):
    core = S.int_core(t)
    pairs = [(a, b) for a in core for b in core]
    ra = S.int_random(t, f"{t}.{op}.a", S.RAND_INT)
    rb = S.int_random(t, f"{t}.{op}.b", S.RAND_INT)
    return _with_rand(pairs, list(zip(ra, rb)))


def int_shift_inputs(t, op):
    n = INTS[t][0]
    core = S.int_core(t)
    pairs = [(a, c) for a in core for c in S.shift_counts(t)]
    r = S.stream(f"{t}.{op}.n")
    rnd = [(a, r.below(2 * n + 4)) for a in S.int_random(t, f"{t}.{op}.a", S.RAND_SHIFT)]
    return _with_rand(pairs, rnd)


def int_unary_inputs(t, op):
    return [("edge", (a,)) for a in S.int_wide(t)]


def float_bin_inputs(t, op):
    core = S.float_core(t)
    pairs = [(a, b) for a in core for b in core]
    ra = S.float_random(t, f"{t}.{op}.a", S.RAND_FLT)
    rb = S.float_random(t, f"{t}.{op}.b", S.RAND_FLT)
    return _with_rand(pairs, list(zip(ra, rb)))


def float_unary_inputs(t, op):
    edge = [(a,) for a in S.float_wide(t)]
    rnd = [(a,) for a in S.float_random(t, f"{t}.{op}.r", S.RAND_UNARY)]
    return _with_rand(edge, rnd)


def conv_inputs(src, dst, key):
    if src in INTS:
        edge = [(x,) for x in S.conv_ints(src, dst)]
        rnd = [(x,) for x in S.int_random(src, key + ".r", S.RAND_CONV)]
    else:
        edge = [(x,) for x in S.conv_floats(src, dst)]
        rnd = [(x,) for x in S.float_random(src, key + ".r", S.RAND_CONV)]
    return _with_rand(edge, rnd)


def bits_inputs(ft):
    """to_bits / from_bits: every kind of NaN (sign, quiet or signaling, payload) and the wide set."""
    w, p, _, _ = M.fparams(ft)
    nans = [S.fnan_bits(ft, s, m) for s in (0, 1) for m in (1, 2, 1 << (p - 2), (1 << (p - 2)) | 1, (1 << (p - 1)) - 1)]
    return S.dedup(S.float_wide(ft) + nans)


def search(key, count, want, draw, limit=400000):
    """Deterministic search: draw candidates from the stream until `count` satisfy `want`."""
    r = S.stream(key)
    out = []
    for _ in range(limit):
        if len(out) >= count:
            break
        c = draw(r)
        if want(c) and c not in out:
            out.append(c)
    assert len(out) == count, f"{key}: the search found {len(out)} of {count}"
    return out


def expr_inputs(t, name):
    w, p, emax, emin = M.fparams(t)
    if name in ("expr_muladd", "expr_mulsub", "expr_add3_l", "expr_add3_r"):
        def draw(r):
            e = r.below(8) + emax - 4
            a = S.fb(t, r.below(2), e, r.bits(p - 1))
            b = S.fb(t, r.below(2), emax + r.below(8) - 4, r.bits(p - 1))
            c = S.fb(t, r.below(2), emax + r.below(16) - 8, r.bits(p - 1))
            return (a, b, c)

        def want(c):
            a, b, cc = c
            if name in ("expr_muladd", "expr_mulsub"):
                cs = cc if name == "expr_muladd" else M.fneg_bits(t, cc)
                fused = M.fused_muladd(t, a, b, cs)
                two = getattr(M, name)(t, a, b, cc)
                return fused is not None and two != M.NAN and two[1] != fused  # tells fused from two roundings
            other = M.expr_add3_r if name == "expr_add3_l" else M.expr_add3_l
            x, y = getattr(M, name)(t, *c), other(t, *c)
            return x != M.NAN and y != M.NAN and x != y  # tells the other association
        rows = search(f"{t}.{name}", 128, want, draw)
        return [("edge", c) for c in rows]
    if name == "expr_interp":
        maxf = S.fmax_bits(t)
        inf = M.fenc_inf(t, 0)
        nan = S.fnan_bits(t, 0, 1 << (p - 2))
        one = lambda q: M.fq(t, Fraction(q))
        fs = [one(0), one(Fraction(1, 2)), one(1), one(Fraction(1, 4)), M.fq(t, 1 - Fraction(1, 2 ** p)), one(Fraction(1, 3))]
        vals = [maxf ^ (1 << (w - 1)), maxf, one(0), M.fenc_zero(t, 1), one(1), one(-3), inf,
                inf ^ (1 << (w - 1)), nan, one(Fraction(1, 10))]
        edge = [(a, b, f) for a in vals for b in vals for f in fs]
        r = S.stream(f"{t}.interp")
        rnd = []
        for _ in range(128):
            a = S.fb(t, r.below(2), emax + r.below(40) - 20, r.bits(p - 1))
            b = S.fb(t, r.below(2), emax + r.below(40) - 20, r.bits(p - 1))
            rnd.append((a, b, M.fq(t, Fraction(r.below(1 << 20), 1 << 20))))
        return _with_rand(edge, rnd)
    # vdelay_k, vdelay_f: (d, MAX)
    inf = M.fenc_inf(t, 0)
    nan = S.fnan_bits(t, 0, 1 << (p - 2))
    one = lambda q: M.fq(t, Fraction(q))
    maxes = [1, 2, 3, 100, 1 << 12, (1 << 24) - 1, (1 << 24) if t == "f32" else (1 << 32) - 1]  # F32: MAX <= 2^24 (E0808)
    ds = [M.fenc_zero(t, 0), M.fenc_zero(t, 1), nan, S.fnan_bits(t, 1, 1), inf, inf ^ (1 << (w - 1)), one(1),
          one(Fraction(9, 10)), M.fq(t, 1 - Fraction(1, 2 ** p)), one(Fraction(3, 2)), one(2), one(Fraction(5, 2)),
          S.fb(t, 0, 0, 1), S.fmax_bits(t), one(3)]
    rows = []
    for m in maxes:
        for d in ds + [one(m), one(m + 1), M.fq(t, Fraction(m) - Fraction(1, 2)), M.fq(t, Fraction(m) + Fraction(1, 2))]:
            rows.append((d, m))
    return [("edge", a) for a in S.dedup(rows)]


# --------------------------------------------------------------- registry
def _vdelay_body(t, name):
    T = onsa_type(t)
    mx = "top.round_f32()" if t == "f32" else "top as F64"
    ki = "k.round_f32()" if t == "f32" else "(k as F64)"
    lets = [("m", mx), ("dc", "if d >= 1.0 { if d <= m { d } else { m } } else { 1.0 }")]
    if name == "vdelay_f":
        lets.append(("k", "dc.trunc_u32()"))
    width = max(len(n) for n, _ in lets)  # `onsa fmt` aligns the `=` of consecutive lets
    head = f"pub fn {t}_{name}(d: {T}, top: U32) -> {'U32' if name == 'vdelay_k' else T} {{\n"
    body = "".join(f"  let {n.ljust(width)} = {v}\n" for n, v in lets)
    return head + body + ("  dc.trunc_u32()\n}" if name == "vdelay_k" else f"  dc - {ki}\n}}")


def registry():
    ops = []

    def add(**kw):
        ops.append(Op(**kw))

    for t in INTS:
        sg = INTS[t][1]
        T = onsa_type(t)
        names = INT_BIN + INT_CHECKED_BIN + INT_SHIFT + INT_CHECKED_SHIFT + INT_UN + (INT_UN_SIGNED if sg else [])
        for name in names:
            base = name[8:] if name.startswith("checked_") else name
            unary = name in INT_UN or name in INT_UN_SIGNED
            shift = base in INT_SHIFT
            args = (t,) if unary else ((t, "u32") if shift else (t, t))
            if name.startswith("checked_"):
                ret, tok = f"opt:{t}", (name,)
                onsa = f"a.{name}()" if unary else f"a.{name}(b)"
            elif base in CMP:
                ret, tok = "bool", (BINOP[base],)
                onsa = f"a {BINOP[base]} b"
            else:
                ret = t
                if base in BINOP:
                    tok = (BINOP[base],)
                    onsa = f"a {BINOP[base]} b"
                elif base in ("div_euclid", "rem_euclid"):
                    tok, onsa = (base,), f"a.{base}(b)"
                elif base == "not":
                    tok, onsa = ("!",), "!a"
                elif base == "neg":
                    tok, onsa = ("-",), "-a"
                else:  # abs min max (std.math)
                    tok = (base,)
                    onsa = f"{base}(a)" if unary else f"{base}(a, b)"
            spec = ("§3.4 整数の表" if base not in STD_MATH else "§3.4 std.math") + (" 検査付き" if name.startswith("checked_") else "")
            inputs = (lambda t=t, name=name: int_unary_inputs(t, name)) if unary else \
                     ((lambda t=t, name=name: int_shift_inputs(t, name)) if shift else (lambda t=t, name=name: int_bin_inputs(t, name)))
            add(id=f"{t}.{name}", ty=t, name=name, group="int", args=args, ret=ret, spec=spec, tokens=tok,
                onsa=onsa, model=(lambda a, t=t, name=name: M.int_op(t, name, a)), inputs=inputs)
    for t in FLOATS:
        for name in FLT_BIN + FLT_UN:
            unary = name in FLT_UN
            ret = "bool" if (name in CMP or name in ("is_nan", "is_finite")) else t
            if name in BINOP:
                onsa, tok = f"a {BINOP[name]} b", (BINOP[name],)
            elif name == "neg":
                onsa, tok = "-a", ("-",)
            else:
                onsa = f"{name}(a)" if unary else f"{name}(a, b)"
                tok = (name,)
            spec = "§3.4 浮動小数の表" if name in ("add", "sub", "mul", "div", "rem", "neg", "sqrt") or name in CMP else "§3.4 std.math"
            add(id=f"{t}.{name}", ty=t, name=name, group="float", args=(t,) if unary else (t, t), ret=ret, spec=spec,
                tokens=tok, onsa=onsa, model=(lambda a, t=t, name=name: M.float_op(t, name, a)),
                inputs=(lambda t=t, name=name: float_unary_inputs(t, name)) if unary else (lambda t=t, name=name: float_bin_inputs(t, name)))
    # conversions (3.3)
    for src in NUM:
        for dst in NUM:
            if src == dst:
                continue
            for form in conv_forms(src, dst):
                D = onsa_type(dst)
                if form == "as":
                    name, onsa, tok, ret = f"as_{dst}", f"a as {D}", ("as",), dst
                    if src in INTS and dst in INTS:
                        model = lambda a: ("v", a[0])
                    elif src in INTS:
                        model = lambda a, dst=dst: M.int_to_float(dst, a[0])
                    else:
                        model = lambda a, src=src, dst=dst: M.float_widen(src, dst, a[0])
                elif form == "narrow":
                    name, onsa, tok, ret = f"narrow_{dst}", f"a.narrow_{dst}()", ("narrow_<型>",), f"opt:{dst}"
                    model = lambda a, dst=dst: M.int_narrow(dst, a[0])
                elif form in ("trunc", "trunc_sat"):
                    sat = form == "trunc_sat"
                    name = f"trunc_{dst}" + ("_sat" if sat else "")
                    onsa, tok, ret = f"a.{name}()", ("trunc_<型>_sat" if sat else "trunc_<型>",), dst
                    model = lambda a, src=src, dst=dst, sat=sat: M.float_to_int(src, a[0], dst, sat)
                else:
                    name, onsa, tok, ret = f"round_{dst}", f"a.round_{dst}()", (f"round_{dst}",), dst
                    if src in INTS:
                        model = lambda a, dst=dst: M.int_to_float(dst, a[0])
                    else:
                        model = lambda a, src=src, dst=dst: M.float_to_float(src, dst, a[0])
                add(id=f"{src}.{name}", ty=src, name=name, group="conv", args=(src,), ret=ret, spec="§3.3 変換の表",
                    tokens=tok, onsa=onsa, model=model, inputs=(lambda src=src, dst=dst, name=name: conv_inputs(src, dst, f"{src}.{name}")))
    for ft, it in (("f32", "u32"), ("f64", "u64")):
        F, U = onsa_type(ft), onsa_type(it)
        add(id=f"{ft}.to_bits", ty=ft, name="to_bits", group="conv", args=(ft,), ret=it, spec="§3.3 ビット表現 / §3.4 NaN",
            tokens=("to_bits",), onsa="a.to_bits()", model=(lambda a, ft=ft: ("v", M.to_bits(ft, a[0]))),
            inputs=(lambda ft=ft: [("edge", (x,)) for x in bits_inputs(ft)]))
        add(id=f"{ft}.from_bits", ty=ft, name="from_bits", group="conv", args=(it,), ret=ft, spec="§3.3 ビット表現",
            tokens=("from_bits",), onsa=f"{F}.from_bits(a)", model=(lambda a, ft=ft: M.from_bits(ft, a[0])),
            inputs=(lambda ft=ft: [("edge", (x,)) for x in bits_inputs(ft)]))
    # expressions (3.4: no contraction, no reassociation; 11.4)
    for t in FLOATS:
        F = onsa_type(t)
        defs = {
            "expr_muladd": ("a * b + c", M.expr_muladd), "expr_mulsub": ("a * b - c", M.expr_mulsub),
            "expr_add3_l": ("(a + b) + c", M.expr_add3_l), "expr_add3_r": ("a + (b + c)", M.expr_add3_r),
            "expr_interp": ("(1.0 - c) * a + c * b", M.expr_interp),
        }
        for name, (onsa, fn) in defs.items():
            add(id=f"{t}.{name}", ty=t, name=name, group="expr", args=(t, t, t), ret=t,
                spec="§11.4 補間の式" if name == "expr_interp" else "§3.4 縮約と再結合をしない", tokens=(),
                onsa=onsa, model=(lambda a, t=t, fn=fn: fn(t, *a)), inputs=(lambda t=t, name=name: expr_inputs(t, name)))
        for name in ("vdelay_k", "vdelay_f"):
            def vmodel(a, t=t, name=name):
                k, f = M.vdelay_kf(t, a[0], a[1])
                return ("v", k) if name == "vdelay_k" else f
            add(id=f"{t}.{name}", ty=t, name=name, group="expr", args=(t, "u32"), ret="u32" if name == "vdelay_k" else t,
                spec="§11.4 vdelay の dc、k、f", tokens=(), onsa="", model=vmodel,
                inputs=(lambda t=t, name=name: expr_inputs(t, name)), body=_vdelay_body(t, name))
    # constants (6.6)
    for t in INTS:
        lo, hi = M.int_range(t)
        vals = {"ZERO": 0, "ONE": 1, "MIN": lo, "MAX": hi, "BITS": INTS[t][0]}
        for c in CONSTS_INT:
            add(id=f"{t}.{c}", ty=t, name=c, group="const", args=(), ret="u32" if c == "BITS" else t, spec="§6.6 関連定数の表",
                tokens=(c,), onsa=f"{onsa_type(t)}.{c}", model=(lambda a, v=vals[c]: ("v", v)), inputs=(lambda: [("edge", ())]))
    for t in FLOATS:
        w, p, emax, emin = M.fparams(t)
        vals = {"ZERO": M.fenc_zero(t, 0), "ONE": M.f_one(t), "MAX": S.fmax_bits(t), "EPSILON": M.fq(t, Fraction(1, 2 ** (p - 1))),
                "INFINITY": M.fenc_inf(t, 0), "NAN": None}
        for c in CONSTS_FLT:
            add(id=f"{t}.{c}", ty=t, name=c, group="const", args=(), ret=t, spec="§6.6 関連定数の表", tokens=(c,),
                onsa=f"{onsa_type(t)}.{c}",
                model=(lambda a, v=vals[c]: M.NAN if v is None else ("v", v)), inputs=(lambda: [("edge", ())]))
    for op in ops:
        op.pkg = package_of(op)
    check_registry(ops)
    return ops


# ------------------------------------------------- formatting values and rows
def fmt_val(t, v):
    if t == "bool":
        return "true" if v else "false"
    if t in INTS:
        return str(v)
    return "0x%0*x" % (M.fparams(t)[0] // 4, v)


def fmt_args(op, args):
    return " ".join(fmt_val(t, v) for t, v in zip(op.args, args)) if op.args else "()"


def fmt_result(op, r):
    if r == M.NAN:
        return "nan"
    if r[0] == "panic":
        return "panic:" + r[1]
    if r[0] == "none":
        return "none"
    if op.ret.startswith("opt:"):
        return "some:" + fmt_val(op.ret[4:], r[1])
    return fmt_val(op.ret, r[1])
