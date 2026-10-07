#!/usr/bin/env python3
"""The cross-check of tests/vectors against independent implementations (W2-01, Q-02 (a), R-133).

    tools/vectors/xcheck.py [--out tests/vectors]

Run after every generation (the gate item `vectors` fails when tests/vectors/XCHECK was written for other data).
It builds tools/vectors/xcheck/xcheck.rs (rustc) and xcheck.c (clang, gcc-15, x86_64 under Rosetta) in a temporary
directory, runs them on the committed data, and on data that is not kept: every input of the 8-bit integer
operations, and a sweep of the floats (spread bit patterns and random operand pairs, from the model). Then it
writes tests/vectors/XCHECK. Nothing it runs is a norm: a disagreement is classified by hand (model error, a known
divergence of the other implementation, a gap in the spec, an environment error) and is never fixed by copying the answer.
The C programs cannot trap: they decide a division, a shift, a cast before doing it, and report by exit code.
"""
import argparse
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model as M  # noqa: E402
import ops as O  # noqa: E402
import sets as S  # noqa: E402

DATA = HERE.parent.parent / "tests" / "vectors"
SWEEP = 16384
CFLAGS = ["-std=gnu11", "-O2", "-ffp-contract=off", "-fno-fast-math"]
BINARY_SWEEP = ("add", "sub", "mul", "div", "rem", "min", "max", "lt", "eq")


def run(argv, **kw):
    return subprocess.run(argv, capture_output=True, text=True, **kw)


def version(argv):
    r = run(argv)
    return (r.stdout or r.stderr).splitlines()[0].strip()


def write_rows(path, ops_rows):
    """ops_rows: [(op, [args])]: the rows in the data format, computed by the model."""
    with open(path, "w") as fh:
        for o, rows in ops_rows:
            fh.write(f"@ {o.id} sweep\n")
            for args in rows:
                r, holds = M.decide(o.model, args)
                e = "?" if holds else O.fmt_result(o, r)
                fh.write(f"{O.fmt_args(o, args)}\t{e}\n")


def exhaustive_8bit(ops, path):
    out = []
    for o in ops:
        if o.ty not in ("i8", "u8") or o.group not in ("int", "conv"):
            continue
        lo, hi = M.int_range(o.ty)
        xs = range(lo, hi + 1)
        if len(o.args) == 1:
            rows = [(x,) for x in xs]
        elif o.args[1] == "u32":
            rows = [(x, c) for x in xs for c in range(12)]
        else:
            rows = [(x, y) for x in xs for y in xs]
        out.append((o, rows))
    write_rows(path, out)
    return sum(len(r) for _, r in out)


def float_sweep(ops, path):
    out = []
    for o in ops:
        if o.ty not in ("f32", "f64") or o.group not in ("float", "conv") or o.name == "from_bits":
            continue
        t = o.ty
        if len(o.args) == 1:
            if M.fparams(t)[0] == 32:
                pats = [(k * 262147) & 0xFFFFFFFF for k in range(SWEEP)]  # spread over all 2^32 patterns
            else:
                r = S.stream(f"sweep.{t}")
                pats = [r.bits(64) for _ in range(SWEEP)]
            rows = [(p,) for p in pats]
        elif o.name in BINARY_SWEEP:
            ra = S.float_random(t, f"sweep.{t}.{o.name}.a", SWEEP)
            rb = S.float_random(t, f"sweep.{t}.{o.name}.b", SWEEP)
            rows = list(zip(ra, rb))
        else:
            continue
        out.append((o, rows))
    write_rows(path, out)
    return sum(len(r) for _, r in out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", type=Path, default=DATA)
    root = ap.parse_args(argv).out
    files = sorted(p for p in root.glob("*.tsv") if p.name != "OPS.tsv")
    h = hashlib.sha256()
    for p in sorted(root.glob("*.tsv")):
        h.update(f"{p.name} {hashlib.sha256(p.read_bytes()).hexdigest()}\n".encode())
    data_hash = h.hexdigest()
    manifest = (root / "MANIFEST").read_text().split("data_sha256 ")[1].split()[0]
    if manifest != data_hash:
        print(f"FAIL MANIFEST is for other data ({manifest}): run tools/vectors/gen.py --out tests/vectors first")
        return 1
    ops = O.registry()
    results, failed = [], False
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        n8 = exhaustive_8bit(ops, td / "exh8.tsv")
        nf = float_sweep(ops, td / "sweep.tsv")
        print(f"sweeps: {n8} rows of the 8-bit integers, {nf} rows of the float sweep")
        src = HERE / "xcheck"
        builds = [("rust", ["rustc", "--edition", "2021", "-O", "-o", str(td / "xc-rust"), str(src / "xcheck.rs")],
                   td / "xc-rust", version(["rustc", "--version"]))]
        for name, cc, extra in (("c-clang-arm64", "clang", []), ("c-gcc-15", "gcc-15", []), ("c-clang-x86_64", "clang", ["-arch", "x86_64"])):
            builds.append((name, [cc, *extra, *CFLAGS, "-o", str(td / f"xc-{name}"), str(src / "xcheck.c"), "-lm"], td / f"xc-{name}",
                           version([cc, "--version"]) + (" (x86_64 under Rosetta)" if extra else "")))
        # the control: with contraction allowed, the expression rows must disagree (they tell fused from unfused)
        builds.append(("control-gcc-15-contract", ["gcc-15", "-std=gnu11", "-O2", "-o", str(td / "xc-control"), str(src / "xcheck.c"), "-lm"],
                       td / "xc-control", "gcc-15 -std=gnu11 -O2 (contraction allowed)"))
        for name, cmd, exe, ver in builds:
            r = run(cmd)
            if r.returncode != 0:
                print(f"FAIL build {name}: {r.stderr[:400]}")
                return 1
            control = name.startswith("control")
            for label, inputs in (("data", [str(p) for p in files]), ("exhaustive-8bit", [str(td / "exh8.tsv")]),
                                  ("float-sweep", [str(td / "sweep.tsv")])):
                if control and label != "data":
                    continue
                r = run([str(exe), *inputs])
                summary = [l for l in r.stdout.splitlines() if l.startswith("rows ")]
                if r.returncode not in (0, 1) or not summary:
                    print(f"FAIL run {name} {label}: exit {r.returncode} {r.stderr[:300]} {r.stdout[:300]}")
                    return 1
                line = summary[-1]
                mism, rows = int(line.split("mismatches ")[1].split()[0]), int(line.split()[1])
                if rows == 0 or (mism and not control):
                    failed = True
                    print(f"FAIL {name} {label}: {line}")
                    print("\n".join(r.stdout.splitlines()[:40]))
                results.append((name, label, ver, line))
                print(f"{name:26s} {label:16s} {line}")
    if failed:
        print("the cross-check found a disagreement: XCHECK is not written")
        return 1
    ctl = [l for n, lab, v, l in results if n.startswith("control")][0]
    out = [
        "# Written by tools/vectors/xcheck.py after generating the vectors. Not a norm (R-133): a record that the data was",
        "# recomputed by independent implementations. `rows` are the rows compared; `held` rows have no expected value.",
        "# Known divergences of Rust, counted (xcheck.rs): D1 MIN % -1 family, D2 min/max with a NaN, D3 to_bits of a NaN.",
        f"data_sha256 {data_hash}",
    ]
    for name, label, ver, line in results:
        out.append(f"run {name} {label} :: {line} :: {ver}")
    out.append("# the control: the same rows with contraction allowed must disagree (the expression rows tell fused from unfused):")
    out.append(f"# {ctl}")
    (root / "XCHECK").write_text("\n".join(out) + "\n")
    print("wrote", root / "XCHECK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
