"""The registry against the spec's operation tokens (W2-01): one to one, mechanically.

The tokens are read from the inline code of sections 3.3 and 3.4 of the spec (operators,
method and function names), the constants table of 6.6, and the formula of 11.4. A token
the spec has and the registry does not cover (a new method, a new operator) fails, and so
does a registry token the spec does not have. What the vectors leave out on purpose is a
closed list with its reason; it is the only place that says so.
"""
import re

import ops as O

# Spans of 3.3 / 3.4 that are not operations of the vectors.
NOT_OPERATIONS = {
    "a": "a name in an example", "b": "a name in an example", "n": "a name in an example",
    "at": "the clock of a flow (11.3)", "process": "the host function (14.2)",
    "fmod": "the name of the meaning of `%` on floats",
    "std.math": "a module path", "rem_s": "the WASM instruction, named as a comparison",
}
# Constants of the table of 6.6 that the vectors leave out (none: S-211 wrote the value of PI, W2-12).
CONSTANTS_LEFT_OUT = {}

COMPARISONS = {"==", "!=", "<", "<=", ">", ">="}
OPERATOR = re.compile(r"[-+*/%&|^<>]+")


def section(text, start, end):
    a = text.index(start)
    return text[a:text.index(end, a + 1)]


def spans(text):
    return [s.replace("\\|", "|") for s in re.findall(r"`([^`\n]+)`", text)]


def spec_tokens(spec):
    s = section(spec, "### 3.3 変換", "### 3.5 評価順")
    toks = set()
    for sp in spans(s):
        m = re.fullmatch(r"a (\S+) (?:b|n)", sp)
        if m and OPERATOR.fullmatch(m.group(1)):
            toks.add(m.group(1))
            continue
        if sp in COMPARISONS:
            toks.add(sp)
            continue
        if sp in ("-a", "!a"):
            toks.add(sp[0])
            continue
        m = re.fullmatch(r"(?:[A-Za-z0-9]+\.)*([a-z_][a-z_0-9]*(?:_<型>(?:_sat)?)?)\(.*\)", sp)
        if not m:
            m = re.fullmatch(r"([a-z_][a-z_0-9]*(?:_<型>(?:_sat)?)?)", sp)
        if m:
            name = m.group(1)
            name = re.sub(r"^narrow_[iu]\d+$", "narrow_<型>", name)
            name = re.sub(r"^trunc_[iu]\d+(_sat)?$", lambda m: "trunc_<型>" + (m.group(1) or ""), name)
            toks.add(name)
    return toks - set(NOT_OPERATIONS)


def spec_constants(spec):
    s = section(spec, "### 6.6 コンパイル時定数", "\n---")
    out = set()
    for line in s.splitlines():
        if line.startswith(("| 整数 |", "| 浮動小数 |")):
            out |= set(re.findall(r"`([A-Z_]+)`", line.split("|")[2]))
    return out


def check(ops, spec):
    problems = []
    reg = {t for o in ops if o.group != "const" for t in o.tokens}
    have = spec_tokens(spec)
    for t in sorted(have - reg):
        problems.append(f"spec token {t!r} (3.3 / 3.4) is covered by no operation of the registry")
    for t in sorted(reg - have):
        problems.append(f"registry token {t!r} is not in the inline code of 3.3 / 3.4")
    consts = {o.name for o in ops if o.group == "const"}
    sc = spec_constants(spec)
    for c in sorted(sc - consts - set(CONSTANTS_LEFT_OUT)):
        problems.append(f"constant {c!r} (6.6) is covered by no operation of the registry")
    for c in sorted(consts - sc):
        problems.append(f"registry constant {c!r} is not in the table of 6.6")
    for c in sorted(set(CONSTANTS_LEFT_OUT) - sc):
        problems.append(f"the left-out constant {c!r} is no longer in the table of 6.6: remove it from CONSTANTS_LEFT_OUT")
    # 11.4: the formulas the registry writes out
    f114 = section(spec, "### 11.4 組込み", "### 11.5 呼び出しと複製")
    for line in ("dc = if d >= 1.0 { if d <= MAX { d } else { MAX } } else { 1.0 }", "k  = dc.trunc_u32()",
                 "f  = dc - k  ", "y  = (1.0 - f) * a + f * b"):  # S-212: `k` is the value of `T`
        if line not in f114:
            problems.append(f"11.4 no longer has the line {line!r} that the vdelay vectors are built on")
    for o in ops:
        if o.name == "expr_interp" and o.onsa.replace("c", "f") != "(1.0 - f) * a + f * b":
            problems.append(f"{o.id}: the Onsa form is not the formula of 11.4")
    return problems
