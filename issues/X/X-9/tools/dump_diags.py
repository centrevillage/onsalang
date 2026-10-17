# Dump (file, code, message, titles) of `onsa check --json` for every .onsa under tests/.
import sys, os, json, subprocess
root, onsa, out = sys.argv[1], sys.argv[2], sys.argv[3]
skip = {"constcyc.onsa", "constcyc2.onsa", "constcyc3.onsa", "rec.onsa", "rec2.onsa"}
files = []
for d, _, fs in os.walk(os.path.join(root, "tests")):
    for f in fs:
        if f.endswith(".onsa") and not ("review-phase1/types" in d and f in skip):
            files.append(os.path.join(d, f))
files.sort()
codes = {}; ndiag = 0; nfix = 0; bad = 0
with open(out, "w") as o:
    for c in files:
        rel = os.path.relpath(c, root)
        p = subprocess.run([onsa, "check", "--json", c], capture_output=True, text=True, timeout=30, cwd=os.path.dirname(c))
        if p.returncode not in (0, 1, 2):
            bad += 1; o.write(f"{rel}\tEXIT {p.returncode}\n"); continue
        try: j = json.loads(p.stdout)
        except Exception: o.write(f"{rel}\tNOJSON {p.returncode}\n"); bad += 1; continue
        for d in j.get("diagnostics", []):
            ndiag += 1; codes[d["code"]] = codes.get(d["code"], 0) + 1
            titles = [fx["title"] for fx in d.get("fixes", [])]; nfix += len(titles)
            o.write(json.dumps([rel, d["code"], d.get("message"), titles], ensure_ascii=False) + "\n")
print("files", len(files), "diagnostics", ndiag, "candidates", nfix, "E0010", codes.get("E0010", 0), "bad", bad)
