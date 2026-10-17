"""Add the gate summaries found in log files (scratchpads) to runs.json, deduplicated by the step rows.
usage: python3 -I files_runs.py <runs.json> <list of files> <base dir> <out.json>"""
import json, os, sys, time, importlib.util
from pathlib import Path
spec = importlib.util.spec_from_file_location("g", Path(__file__).with_name("gate_runs.py"))
src = Path(__file__).with_name("gate_runs.py").read_text().replace("\nmain()\n", "\n")
g = {}; exec(compile(src, "gate_runs", "exec"), g)
runs = json.load(open(sys.argv[1]))
seen = {tuple(tuple(s) for s in r["steps"]) for r in runs}
base = Path(sys.argv[3])
added = 0
for rel in Path(sys.argv[2]).read_text().split():
    if rel.endswith(".py"):
        continue
    p = base / rel
    t = p.read_text(errors="replace")
    for rows, verdict, before in g["parse"](t):
        key = tuple(tuple(r) for r in rows)
        if key in seen:
            continue
        seen.add(key)
        secs = g["sections"](before)
        names = {n for _, n, _, _ in rows}
        mode = "quick" if "fuzz" not in names else ("stage-end" if any(n == "fuzz-deep" and s != "SKIPPED" for s, n, _, _ in rows) else "full")
        parts = Path(rel).parts
        runs.append({"time": time.strftime("%Y-%m-%dT%H:%M:%S.000Z", time.gmtime(p.stat().st_mtime)),
                     "session": parts[0], "agent": "file:" + "/".join(parts[2:]), "type": "file", "desc": "",
                     "cwd": "", "cmd": "", "mode": mode, "verdict": verdict,
                     "total": round(sum(r[2] for r in rows), 1), "steps": [list(r) for r in rows],
                     "fails": {n: secs.get(n, "")[-1500:] for s, n, _, _ in rows if s == "FAIL"}})
        added += 1
runs.sort(key=lambda r: r["time"])
json.dump(runs, open(sys.argv[4], "w"), ensure_ascii=False, indent=1)
print(f"added {added}, total {len(runs)}")
