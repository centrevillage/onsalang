#!/usr/bin/env python3
"""inject.py <outdir> <srcroot>...: for every .onsa with a //~ marker (a program P with errors), write P' = P with a stray `;`
appended to one statement of a function unit (E0020, candidate: remove it), one mutant per function unit.
After the candidate, the text is P again: every diagnostic it shows in a unit that held none in P' was hidden by the injection."""
import os, re, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
head = re.compile(r"^(pub\s+)?(rt\s+)?fn\s")
n = 0
lst = []
for root in sys.argv[2:]:
    for dp, dn, fns in os.walk(root):
        for f in sorted(fns):
            if not f.endswith(".onsa"):
                continue
            p = os.path.join(dp, f)
            if os.path.getsize(p) > 20000 or "deep" in p:
                continue
            text = open(p, encoding="utf-8").read()
            if "//~" not in text or text.startswith("// onsa.toml") and "[package]" in text:
                continue
            lines = text.split("\n")
            i = 0
            k = 0
            while i < len(lines):
                if head.match(lines[i]) and lines[i].rstrip().endswith("{") and "//~" not in lines[i]:
                    # the body: until a line that is `}` at column 0
                    j = i + 1
                    while j < len(lines) and lines[j].rstrip() != "}":
                        j += 1
                    body = range(i + 1, j)
                    # first plain statement line of the body (indent 2, no marker, no `{`/`,` end)
                    for b in body:
                        l = lines[b]
                        if re.match(r"^  \S", l) and "//" not in l and not l.rstrip().endswith(("{", ",", "(", "->", "=>")):
                            m = lines[:]
                            m[b] = l.rstrip() + ";"
                            q = os.path.join(out, f"{k}_{f}")
                            open(q, "w", encoding="utf-8").write("\n".join(m))
                            lst.append(q)
                            k += 1
                            n += 1
                            break
                    i = j
                i += 1
open(os.path.join(out, "LIST.txt"), "w").write("\n".join(lst) + "\n")
print(n)
