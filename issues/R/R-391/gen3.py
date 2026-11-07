"""gen3.py <out> <form> <levels> <lets>
form=fork_small: fork of (T,U8)/(U8,T) from T=U32 (no b chain); <lets> `let e = x` per body, each used by `f0(e)`.
form=fork_big: as gen2 with base 2047 (b chain of 10) and <lets> lets.
form=chain: no fork, f_k calls f_{k-1}((x,u)) once; <levels> levels; root T=U32.
form=self: one polymorphic recursion g[T] calling g((x,u)) until E0422 (depth).
form=bal: one polymorphic recursion g[T] calling g((x,x)) (balanced; size doubles) until E0422 (size).
"""
import sys
out, form, n, lets = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
extra = "".join(f"  let e{i} = x\n" for i in range(lets))
uses = "".join(f" + f0(e{i})" for i in range(lets))
s = "fn f0[T: Copy](x: T) -> U32 { 0 }\nfn b[T: Copy](x: T) -> (T, T) { (x, x) }\n"
if form in ("fork_small", "fork_big"):
    for k in range(1, n + 1):
        s += f"fn f{k}[T: Copy](x: T) -> U32 {{\n  let u: U8 = 1\n{extra}  let a = f{k-1}((x, u))\n  a + f{k-1}((u, x)){uses}\n}}\n"
    def wrapped(k):
        return "1" if k == 0 else f"b({wrapped(k - 1)})"
    arg = wrapped(10) if form == "fork_big" else "1"
    s += f'test "t" {{\n  assert(f{n}({arg}) == 0)\n}}\n'
elif form == "chain":
    for k in range(1, n + 1):
        s += f"fn f{k}[T: Copy](x: T) -> U32 {{\n  let u: U8 = 1\n{extra}  f{k-1}((x, u)){uses}\n}}\n"
    s += f'test "t" {{\n  assert(f{n}(1) == 0)\n}}\n'
elif form in ("self", "bal"):
    arg = "(x, u)" if form == "self" else "(x, x)"
    s += f"fn g[T: Copy](x: T, d: U32) -> U32 {{\n  let u: U8 = 1\n{extra}  if d == 0 {{ 0 }} else {{ g({arg}, d - 1){uses} }}\n}}\n"
    s += f'test "t" {{\n  assert(g(1, {n}) == 0)\n}}\n'
open(out, "w").write(s)
