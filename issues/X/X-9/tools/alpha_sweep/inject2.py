#!/usr/bin/env python3
"""inject2.py <outdir> <srcroot>...: mutants P' of programs P with errors: one fn head gets `pub(crate)` (E0020, Failed::Unit),
or an `@fp(relaxed, x)` attribute line (E0005)."""
import os, re, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
head_plain = re.compile(r"^((rt\s+)?fn\s)")
head_any = re.compile(r"^((pub\s+)?(rt\s+)?fn\s)")
lst = []
n = 0
for root in sys.argv[2:]:
    for dp, dn, fns in os.walk(root):
        for f in sorted(fns):
            if not f.endswith(".onsa"):
                continue
            p = os.path.join(dp, f)
            if os.path.getsize(p) > 20000 or "deep" in p:
                continue
            text = open(p, encoding="utf-8").read()
            if "//~" not in text or (text.startswith("// onsa.toml") and "[package]" in text):
                continue
            lines = text.split("\n")
            k = 0
            for i, l in enumerate(lines):
                if "//~" in l:
                    continue
                if head_plain.match(l):
                    m = lines[:]
                    m[i] = "pub(crate) " + l
                    q = os.path.join(out, f"vis{k}_{f}")
                    open(q, "w", encoding="utf-8").write("\n".join(m))
                    lst.append(q)
                    k += 1
                if head_any.match(l):
                    m = lines[:]
                    m[i] = "@fp(relaxed, x)\n" + l
                    q = os.path.join(out, f"attr{k}_{f}")
                    open(q, "w", encoding="utf-8").write("\n".join(m))
                    lst.append(q)
                    k += 1
            n += k
print(n)
