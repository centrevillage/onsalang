"""seeds.py ROOT: run a few `graph` commands under several PYTHONHASHSEED values; print whether each output is the same."""
import hashlib, os, subprocess, sys

root = sys.argv[1]
for argv in (["D-15", "--back", "--depth", "3"], ["S-239", "--depth", "5"], ["W1-01", "--back", "--typed", "--depth", "5"]):
    digests = set()
    for seed in ("0", "1", "2", "3", "random"):
        env = dict(os.environ, PYTHONHASHSEED=seed)
        r = subprocess.run(["python3", "-B", "tools/docs.py", "graph", *argv], cwd=root, env=env, capture_output=True, text=True, timeout=60)
        digests.add(hashlib.sha1((r.stdout + r.stderr + str(r.returncode)).encode()).hexdigest())
    print(" ".join(argv), "same" if len(digests) == 1 else f"DIFFERENT ({len(digests)})", r.stdout.splitlines()[-1])
