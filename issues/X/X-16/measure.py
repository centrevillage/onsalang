"""measure.py LABEL -- CMD...: run CMD in the main tree and print the bytes the disk wrote meanwhile.

The counter is the first nonzero "Bytes (Write)" of IOBlockStorageDriver (ioreg): the whole disk,
so nothing else should run at the same time. LABEL "idle:N" sleeps N seconds instead (the noise).
"""
import re
import subprocess
import sys
import time

ROOT = "/Users/centrevillage/projects/onsalang"


def written():
    out = subprocess.run(["ioreg", "-c", "IOBlockStorageDriver", "-r", "-w0"], capture_output=True, text=True).stdout
    vals = [int(v) for v in re.findall(r'"Bytes \(Write\)"=(\d+)', out)]
    return next(v for v in vals if v)


def main():
    label = sys.argv[1]
    cmd = sys.argv[3:] if len(sys.argv) > 3 and sys.argv[2] == "--" else []
    w0, t0 = written(), time.monotonic()
    if label.startswith("idle:"):
        time.sleep(float(label.split(":")[1]))
        code = 0
    else:
        code = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode
    w1, t1 = written(), time.monotonic()
    mb = (w1 - w0) / 2**20
    secs = t1 - t0
    print(f"{label}\texit {code}\t{secs:.0f} s\t{mb:.0f} MB written\t{mb / secs:.1f} MB/s")


main()
