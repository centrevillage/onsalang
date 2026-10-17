import sys, os, json, subprocess, re, collections
root = sys.argv[1]; onsa = sys.argv[2]
cases = []
for d, _, fs in os.walk(os.path.join(root, "tests")):
    for f in fs:
        if f.endswith(".onsa.fix1"):
            cases.append(os.path.join(d, f[:-5]))
cases.sort()
tok = re.compile(r"\s+|//[^\n]*|/\*.*?\*/|[A-Za-z_][A-Za-z0-9_]*|\d[\w.]*|\S", re.S)
def toks(s): return [t for t in tok.findall(s) if not t.isspace()]
def off(lines, line, col):
    return sum(len(l) + 1 for l in lines[:line-1]) + (col-1)
stats = collections.Counter(); outside = []; shrink = []; n_cand = 0; n_diag = 0; failed = 0
for c in cases:
    try:
        p = subprocess.run([onsa, "check", "--json", c], capture_output=True, text=True, timeout=20)
        j = json.loads(p.stdout)
    except Exception as e:
        failed += 1; continue
    text = open(c, encoding="utf-8").read(); lines = text.split("\n")
    for d in j.get("diagnostics", []):
        n_diag += 1
        sp = d["span"]; s0 = off(lines, sp["line"], sp["col"]); s1 = off(lines, sp["end_line"], sp["end_col"])
        for k, fx in enumerate(d.get("fixes", []), 1):
            n_cand += 1
            ok = True
            for e in fx["edits"]:
                es = e["span"]
                if es.get("file") != sp.get("file"): ok = False; continue
                e0 = off(lines, es["line"], es["col"]); e1 = off(lines, es["end_line"], es["end_col"])
                if e0 < s0 or e1 > s1: ok = False
                old = toks(text[e0:e1]); new = toks(e["replace"])
                if old and new and (old[0] == new[0] or old[-1] == new[-1]):
                    shrink.append((os.path.relpath(c, root), d["code"], k, text[e0:e1], e["replace"]))
            stats[(d["code"], ok)] += 1
            if not ok: outside.append((os.path.relpath(c, root), d["code"], k, fx["title"]))
print("cases", len(cases), "failed", failed, "diags", n_diag, "candidates", n_cand)
inside = sum(v for (c, ok), v in stats.items() if ok); print("edits inside the diagnostic span:", inside, "outside:", n_cand - inside)
bycode = collections.Counter(); 
for (c, ok), v in stats.items():
    if not ok: bycode[c] += v
print("outside by code:", dict(bycode))
for o in outside[:25]: print("  ", o)
print("shrinkable edits (first/last token kept):", len(shrink))
for s in shrink[:25]: print("  ", s)
