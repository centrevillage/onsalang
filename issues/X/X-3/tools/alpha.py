import sys, os, json, subprocess, re, collections, tempfile
root = sys.argv[1]; onsa = sys.argv[2]
cases = []
for d, _, fs in os.walk(os.path.join(root, "tests/spec")):
    for f in fs:
        if f.endswith(".onsa") and os.path.exists(os.path.join(d, f + ".fix1")):
            cases.append(os.path.join(d, f))
cases.sort()
item_re = re.compile(r"^[A-Za-z@_]")
def items(text):
    starts = []
    for i, l in enumerate(text.split("\n")):
        if item_re.match(l) and not l.startswith("//"): starts.append(i + 1)
    return starts
def item_of(starts, line):
    k = 0
    for i, s in enumerate(starts):
        if s <= line: k = i + 1
    return k
def off(lines, line, col): return sum(len(l) + 1 for l in lines[:line-1]) + (col-1)
def check(path):
    p = subprocess.run([onsa, "check", "--json", path], capture_output=True, text=True, timeout=20)
    return json.loads(p.stdout).get("diagnostics", [])
tmpd = tempfile.mkdtemp(prefix="alpha_")
n_cand = 0; viol = []; touched_viol = 0; untouched_viol = 0; later_only = 0
for c in cases:
    text = open(c, encoding="utf-8").read(); lines = text.split("\n"); st = items(text)
    before = check(c)
    had = set(item_of(st, d["span"]["line"]) for d in before)
    for d in before:
        for k, fx in enumerate(d.get("fixes", []), 1):
            n_cand += 1
            eds = []
            for e in fx["edits"]:
                es = e["span"]
                if es.get("file") != d["span"].get("file"): eds = None; break
                eds.append((off(lines, es["line"], es["col"]), off(lines, es["end_line"], es["end_col"]), e["replace"]))
            if not eds: continue
            eds.sort(); out = ""; pos = 0
            for s, t, r in eds: out += text[pos:s] + r; pos = t
            out += text[pos:]
            tp = os.path.join(tmpd, os.path.basename(c)); open(tp, "w", encoding="utf-8").write(out)
            after = check(tp); st2 = items(out)
            touched = set(item_of(st, text[:s].count("\n") + 1) for s, t, r in eds)
            bad = [(item_of(st2, a["span"]["line"]), a["code"], a["span"]["line"]) for a in after if item_of(st2, a["span"]["line"]) not in had]
            if bad:
                viol.append((os.path.relpath(c, root), d["code"], k, fx["title"], bad[:3]))
                if any(b[0] in touched for b in bad): touched_viol += 1
                else: untouched_viol += 1
print("cases", len(cases), "candidates", n_cand, "alpha violations", len(viol), "(in a touched item:", touched_viol, ", only untouched items:", untouched_viol, ")")
codes = collections.Counter(v[1] for v in viol); print("by original code:", dict(codes))
after_codes = collections.Counter(b[1] for v in viol for b in v[4]); print("codes appearing:", dict(after_codes))
for v in viol[:30]: print("  ", v)
