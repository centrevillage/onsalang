# t409.py N...: time old/new check on bracket forms, and compare the output (exit code, stdout) for equality
import sys, subprocess, time
P2 = "/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/ef2f288b-d5bb-46c5-84b6-d10ee96bb8a4/scratchpad"
GUARD = "/Users/centrevillage/projects/onsalang/tools/guard.py"
def stmt(s): return "fn f() -> I32 {\n  let y = " + s + "\n}\n"
forms = {
 "A_paren_rbr":   lambda n: stmt("( ] " * n),
 "B_brk_paren_rbrace": lambda n: stmt("[ ( } " * n),
 "C_deep_wrong":  lambda n: stmt("(" * n + "]" * n),
 "D_unclosed_then_rbrace": lambda n: stmt("(" * n + " }" * n),
 "E_struct_body": lambda n: "struct S {\n  a: " + "{ ] " * n + "\n}\nfn g() {}\n",
 "F_alt_then_rbrace": lambda n: stmt("([" * n + " }" * n),
 "G_brace_unclosed_top": lambda n: "fn f() {\n" * n + ") ] " * n,
 "H_rbrace_only": lambda n: stmt("} " * n),
 "I_openers_then_mixed": lambda n: stmt("{(" * n + "] ) " * n),
 "J_items": lambda n: "".join(f"fn f{i}() {{ ( ] \n" for i in range(n)),
 "K_extern": lambda n: "extern \"C\" {\n  fn f(" + "( ] " * n + "\n}\nfn g() {}\n",
 "L_attr": lambda n: "@x(" + "( ] " * n + ")\nfn f() {}\n",
}
def run(v, p):
    t = time.perf_counter()
    r = subprocess.run(["python3","-B",GUARD,"run","4","120","--",f"{P2}/bin/onsa-{v}","check","--json",p], capture_output=True, text=True)
    o = "\n".join(l for l in r.stdout.splitlines() if not l.startswith("guard: exit"))
    return time.perf_counter() - t, r.returncode, o
import os
for name, mk in [(k,v) for k,v in forms.items() if k[0] in os.environ.get("ONLY","ABCDEFGHIJKL")]:
    for n in map(int, sys.argv[1:]):
        p = f"{P2}/w513/u7c/b/t409_{name}.onsa"; open(p, "w").write(mk(n))
        a = [run("aba52f8", p) for _ in range(1)]; b = [run("u7c", p) for _ in range(2)]
        ta, tb = min(x[0] for x in a), min(x[0] for x in b)
        same = a[0][1:] == b[0][1:]
        print(f"{name:28} n={n:6} old {ta:6.2f}s new {tb:6.2f}s exit {a[0][1]}/{b[0][1]} {'SAME' if same else 'DIFF'} outlen {len(a[0][2])}", flush=True)
