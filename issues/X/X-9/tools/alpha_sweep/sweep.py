#!/usr/bin/env python3
"""sweep.py <ws> <outfile> <root-dir>...: alpha-type problems of the single-file contract over all .onsa files."""
import os, subprocess, sys

ws, outfile = sys.argv[1], sys.argv[2]
files = []
for root in sys.argv[3:]:
    for dp, dn, fn in os.walk(root):
        for f in sorted(fn):
            if not f.endswith(".onsa"):
                continue
            p = os.path.join(dp, f)
            if os.path.getsize(p) > 20000 or "deep" in p or f.startswith(("constcyc", "rec")):
                continue
            files.append(p)
lst = outfile + ".list"
open(lst, "w").write("\n".join(files) + "\n")
env = dict(os.environ, SWEEP_LIST=lst)
r = subprocess.run(["cargo", "test", "-p", "onsa_tests", "--test", "sweep", "--", "--nocapture"],
                   cwd=ws, env=env, capture_output=True, text=True, timeout=900)
open(outfile, "w").write(r.stdout)
print(len(files), "files;", [l for l in r.stdout.splitlines() if l.startswith("SWEEP")], r.returncode)
if r.returncode:
    print(r.stderr[-2000:])
