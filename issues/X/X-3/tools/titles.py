import sys, os, json, subprocess, collections
root = sys.argv[1]; onsa = sys.argv[2]
files = []
for d, _, fs in os.walk(os.path.join(root, "tests")):
    if "/golden" in d or "/fuzz" in d or "review-phase1" in d: continue
    for f in fs:
        if f.endswith(".onsa"): files.append(os.path.join(d, f))
files.sort()
lens = collections.Counter(); bycode_max = {}; e0010 = []; longest = []; n = 0; fail = 0
for c in files:
    try:
        p = subprocess.run([onsa, "check", "--json", c], capture_output=True, text=True, timeout=20)
        j = json.loads(p.stdout)
    except Exception: fail += 1; continue
    for d in j.get("diagnostics", []):
        for fx in d.get("fixes", []):
            n += 1; t = fx["title"]; L = len(t)
            lens[(L // 10) * 10] += 1
            bycode_max[d["code"]] = max(bycode_max.get(d["code"], 0), L)
            longest.append((L, d["code"], t))
            if d["code"] == "E0010":
                found = d.get("found", "")
                e0010.append((t.startswith("reading "), len(found), "\n" in found, os.path.relpath(c, root)))
print("files", len(files), "failed", fail, "candidates", n)
print("title length histogram (bucket of 10):", sorted(lens.items()))
print("max title length by code:", sorted(bycode_max.items(), key=lambda x: -x[1])[:15])
longest.sort(reverse=True); print("longest titles:"); [print("  ", x) for x in longest[:8]]
fb = [e for e in e0010 if e[0]]
print("E0010 candidates:", len(e0010), "fallback 'reading i of n':", len(fb))
print("  fallback found lengths:", sorted((e[1], e[2]) for e in fb)[:40])
print("  fallback files:", sorted(set(e[3] for e in fb)))
