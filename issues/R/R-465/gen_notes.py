import sys
n = int(sys.argv[1]); out = sys.argv[2]; kind = sys.argv[3]
L = []
if kind == "closure_discard":
    # n anonymous functions, each drops its `move _` parameter: one E0601 per scope, each scans the heads
    L.append("pub fn f() -> U32 {\n")
    for i in range(n):
        L.append(f"  let g{i} = fn(move _: Str) -> U32 {{ 0 }}\n")
    L.append("  0\n}\n")
elif kind == "closure_interp":
    # control: n anonymous functions, each an interpolation (no heads scan)
    L.append("pub fn f(x: U32) -> U32 {\n")
    for i in range(n):
        L.append(f"  let g{i} = fn(y: U32) -> U32 {{ let _ = \"{{y}}\"\n    y }}\n")
    L.append("  x\n}\n")
elif kind == "closure_calls":
    # n closures in one body, each with k = 1 call: Closures::around depth 1
    L.append("fn h(x: U32) -> U32 uses {Alloc} { x }\npub fn f(x: U32) -> U32 {\n")
    for i in range(n):
        L.append(f"  let g{i} = fn(y: U32) -> U32 {{ h(y) }}\n")
    L.append("  x\n}\n")
open(out, "w").write("".join(L))
