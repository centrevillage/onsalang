import sys
kind, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
PRE = "fn make[T]() -> T { make() }\nfn need[T: Num](x: T) -> T { x }\n"
L = [PRE, "pub fn f() -> I32 {\n  let v = make()\n"]
for i in range(n):
    if kind == 'req_bind':
        L.append("  let _ = need(v)\n  let _: I32 = 1\n")
    elif kind == 'op_bind':
        L.append("  let _ = v + v\n  let _: I32 = 1\n")
L.append("  let r: I32 = v\n  r\n}\n")
open(out, 'w').write(''.join(L))
