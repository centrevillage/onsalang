"""Requests that wrote a large part of the context to the cache again (a miss after a wait).
usage: python3 -I cache_miss.py <projects dir> <since YYYY-MM-DD>"""
import json, sys, collections
from datetime import datetime
from pathlib import Path
root, since = Path(sys.argv[1]), sys.argv[2]
rows = []
def ts(s): return datetime.fromisoformat(s.replace("Z", "+00:00"))
for f in sorted(root.glob("*/subagents/*.jsonl")) + sorted(root.glob("*.jsonl")):
    kind = "agent" if f.parent.name == "subagents" else "parent"
    prev_t = None; seen = set(); first = True
    for line in f.open(errors="replace"):
        try: d = json.loads(line)
        except json.JSONDecodeError: continue
        t = d.get("timestamp")
        if not t or t < since: continue
        m = d.get("message") or {}
        u = m.get("usage") if d.get("type") == "assistant" else None
        if u and m.get("id") not in seen:
            seen.add(m.get("id"))
            cc = (u.get("cache_creation_input_tokens") or 0); cr = u.get("cache_read_input_tokens") or 0
            gap = (ts(t) - prev_t).total_seconds() if prev_t else 0
            if not first and cc > 50000 and cc > cr:
                rows.append((kind, f.stem[:20], t[:16], round(gap), cc, cr))
            first = False
        if u: prev_t = ts(t)
print(len(rows), "misses (cache write > 50k and > read)")
c = collections.Counter(); tok = collections.Counter()
for k, _, _, gap, cc, _ in rows:
    b = "<5m" if gap < 300 else "5-60m" if gap < 3600 else ">60m"
    c[(k, b)] += 1; tok[(k, b)] += cc
for key in sorted(c): print(key, c[key], "tokens", tok[key])
for r in rows[-12:]: print(r)
