import subprocess, sys, time, glob, json, resource
P78 = "/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/4945602c-a0a4-48b9-8fbb-e70e5c822003/scratchpad"
for f in sorted(sys.argv[1:]):
    row = [f.split("/")[-1]]
    for b in ("onsa-7560d6e", "onsa-u9"):
        t = time.time()
        try:
            r = subprocess.run([f"{P78}/bin/{b}", "check", "--json", f], capture_output=True, timeout=120)
            dt = time.time() - t
            try:
                ds = json.loads(r.stdout)["diagnostics"]
                nf = sum(len(d["fixes"]) for d in ds); ne = sum(len(fx["edits"]) for d in ds for fx in d["fixes"])
                info = f"rc={r.returncode} {dt:.2f}s out={len(r.stdout)//1024}KB diags={len(ds)} fixes={nf} edits={ne}"
            except Exception:
                info = f"rc={r.returncode} {dt:.2f}s out={len(r.stdout)//1024}KB NOJSON err={r.stderr[:150]}"
        except subprocess.TimeoutExpired:
            info = "TIMEOUT"
        row.append(f"{b[5:]}: {info}")
    print(" | ".join(row))
