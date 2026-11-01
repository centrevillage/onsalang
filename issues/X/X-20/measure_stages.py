"""measure_stages.py: the time of each phase of the compiler (X-20/U1), with `onsa_cases --phases`.

  measure_stages.py corpus BIN OUT.jsonl   the cases of tests/spec, the files of std, examples/
  measure_stages.py scale BIN OUT.jsonl    a usual file (tests/spec/examples/voice.onsa) times 1 to 16
  measure_stages.py quad BIN OUT.jsonl [NAME...]  the quadratic forms left to X-20 by W4-05 to W4-10
  measure_stages.py report OUT.jsonl...    the sums, the slowest inputs, the growth by family

BIN is an `onsa_cases` (debug or release). Each input is checked (and lowered to Core when the
check reports nothing, `--lower`) in its own process, ROUNDS times (default 3, `--rounds`); a line
keeps the least of each phase and of the whole, with the wall clock and the cpu (user + sys) of
the process and its largest resident memory. Run it on a quiet machine, one at a time (no
parallel runs: the memory is measured too). A generated family stops growing past 10 s
(rules/common.md 3). Generated inputs go to OUT's directory, under gen/.
"""
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
TIMEOUT = 120
GROW_LIMIT = 10.0


def run_once(binary, path, lower=True):
    """One process: the line of onsa_cases with the process's wall, cpu and memory."""
    args = [binary, "--phases", "--rounds", "1"] + (["--lower"] if lower else []) + [path]
    t0 = time.monotonic()
    p = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    timer = threading.Timer(TIMEOUT, lambda: os.kill(p.pid, signal.SIGKILL))
    timer.start()
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    timer.cancel()
    wall = time.monotonic() - t0
    rec = {"path": path, "status": status}
    try:
        rec.update(json.loads(out.decode().strip().splitlines()[-1]))
    except (ValueError, IndexError):
        rec["error"] = f"no line (status {status})"
    rec.update(wall=wall, cpu=ru.ru_utime + ru.ru_stime, rss_mb=ru.ru_maxrss / 2**20)
    return rec


def measure(binary, path, rounds, extra=None):
    recs = [run_once(binary, path) for _ in range(rounds)]
    best = dict(recs[0])
    for r in recs[1:]:
        for k in ("wall", "cpu", "total_us"):
            if k in r and k in best:
                best[k] = min(best[k], r[k])
        if "phases_us" in r and "phases_us" in best:
            best["phases_us"] = {p: min(v, r["phases_us"][p]) for p, v in best["phases_us"].items()}
    best["rss_mb"] = max(r["rss_mb"] for r in recs)
    best["rounds"] = rounds
    best.update(extra or {})
    return best


def corpus_inputs(binary):
    cases = json.loads(subprocess.run([binary], cwd=ROOT, capture_output=True, text=True, check=True).stdout)
    paths = [c["path"] for c in cases if c["path"].startswith("tests/spec/")]
    paths += sorted(os.path.join("std", f) for f in os.listdir(os.path.join(ROOT, "std")) if f.endswith(".onsa"))
    for e in sorted(os.listdir(os.path.join(ROOT, "examples"))):
        p = os.path.join("examples", e)
        if e.endswith(".onsa") or os.path.exists(os.path.join(ROOT, p, "onsa.toml")):
            paths.append(p)
    return [(p, {"set": "corpus"}) for p in paths]


# ---------------------------------------------------------------- generated families


def voice_times(k):
    """tests/spec/examples/voice.onsa (without its fragment), k copies with renamed declarations."""
    text = open(os.path.join(ROOT, "tests/spec/examples/voice.onsa")).read()
    lines = [l for l in text.splitlines() if not l.startswith("//")]
    uses = sorted({l for l in lines if l.startswith("use ")})
    body = "\n".join(l for l in lines if not l.startswith("use "))
    names = sorted(set(re.findall(r"^(?:pub )?(?:rt )?(?:flow|fn|struct|const) (\w+)", body, re.M)))
    def renamed(name, i):
        if name.isupper():
            return f"{name}_V{i}"
        return f"{name}V{i}" if name[0].isupper() else f"{name}_v{i}"
    out = []
    for i in range(k):
        out.append(re.sub(r"\b(" + "|".join(names) + r")\b", lambda m: renamed(m.group(1), i), body))
    return "\n".join(uses) + "\n\n" + "\n\n".join(out) + "\n"


def w407_manylocals(m, n):
    """W4-07 (genperf.py manylocals): m locals moved, then n control nodes (M x N)."""
    h = ("pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(1) }\n"
         "pub fn take(move b: Buf[F32]) uses {Alloc} {}\n")
    body = [f"  let b{i} = mk()" for i in range(m)] + [f"  take(move b{i})" for i in range(m)]
    body += ["  if c { }"] * n
    return h + "pub fn t(c: Bool) uses {Alloc} {\n" + "\n".join(body) + "\n}\n"


def w409_held(f, w):
    """W4-09 (perf/distinct_F_W): F nested borrowing `for`s over distinct arrays, W writes inside."""
    s = "fn t() -> U32 {\n"
    s += "".join(f"  var v{i}: [U32; 3] = [1, 2, 3]\n" for i in range(f))
    s += "  var xs: [U32; 3] = [1, 2, 3]\n  var z: [U32; 3] = [1, 2, 3]\n"
    for i in range(f):
        s += " " * (i + 2) + f"for _ in v{i} {{\n"
    s += "".join(" " * (f + 2) + f"z[{j % 3}] = {j}\n" for j in range(w))
    for i in reversed(range(f)):
        s += " " * (i + 2) + "}\n"
    return s + "  z[0] + xs[0]\n}\n"


def w409_same(depth, writes):
    """W4-09 (perf/same_S_W): `depth` nested borrowing `for`s over one array, `writes` writes to it inside
    (each an E0715: the places share their root)."""
    s = "fn t() -> U32 {\n  var xs: [U32; 3] = [1, 2, 3]\n"
    for i in range(depth):
        s += " " * (i + 2) + "for _ in xs {\n"
    s += "".join(" " * (depth + 2) + f"xs[{j % 3}] = {j}\n" for j in range(writes))
    for i in reversed(range(depth)):
        s += " " * (i + 2) + "}\n"
    return s + "  xs[0]\n}\n"


def w410_guards(depth, writes):
    """W4-10 (speed2.py mk_b): `depth` nested matches with a guard, `writes` writes in the inner guard."""
    s = "pub struct S {\n  a: U32,\n  b: U32,\n}\npub fn f() -> U32 {\n  var s = S { a: 0, b: 0 }\n"
    s += "".join(("(" if d else "  ") + "match s.a {\n    _ if " for d in range(depth))
    s += "{\n" + "".join(f"      s.b = {j}\n" for j in range(writes)) + "      true\n    }"
    for d in range(depth):
        s += " => 1,\n    _ => 0,\n  }" + (") > 0" if d < depth - 1 else "")
    return s + "\n}\n"


def w410_chain(chain, writes):
    """W4-10 (speed3.py mk, match): a derived chain of `chain` steps under a guard with `writes` writes."""
    s = ("pub struct S {\n  o: Option[Buf[F32]],\n  c: U32,\n  p: Option[Buf[F32]],\n}\n"
         "pub fn f(c: Bool) -> U32 uses {Alloc} {\n  var s = S { o: Some(Buf.zeroed(2)), c: 0, p: None }\n"
         "  match s.o {\n    Some(x0) => {\n    let y0 = x0\n")
    for i in range(chain):
        s += f"  let x{i+1} = if c {{ x{i} }} else {{ y{i} }}\n"
        s += f"  let y{i+1} = if c {{ y{i} }} else {{ x{i} }}\n" if i < chain - 1 else ""
    w = "".join(f"      s.c = {j}\n" for j in range(writes))
    s += f"  match x{chain} {{\n    v if {{\n{w}      v.len() > 0\n    }} => 1,\n    _ => 0,\n  }}\n"
    return s + "},\n None => 0,\n}\n}\n"


def w405_nested(fields, depth):
    """W4-05 U2/b B-4 (stress.py b): `fields` fields, each `W[W[...[I32]...]]` `depth` deep."""
    ty = "W[" * depth + "I32" + "]" * depth
    return ("struct W[T] {\n  v: T,\n}\n\nstruct S {\n"
            + "".join(f"  f{i}: {ty},\n" for i in range(fields)) + "}\n")


SCALE = [("voice", "decls x", voice_times, [(k,) for k in (1, 2, 4, 8, 16)])]

QUAD = [
    ("w407_manylocals", "M=N=n", w407_manylocals, [(n, n) for n in (1000, 2000, 4000, 8000, 16000)]),
    ("w407_manylocals_n", "M=1000, N", w407_manylocals, [(1000, n) for n in (1000, 2000, 4000, 8000)]),
    ("w407_manylocals_m", "N=1000, M", w407_manylocals, [(m, 1000) for m in (1000, 2000, 4000, 8000)]),
    ("w409_held_w", "F=120, W", w409_held, [(120, w) for w in (1500, 3000, 6000, 12000)]),
    ("w409_held_f", "W=6000, F", w409_held, [(f, 6000) for f in (15, 30, 60, 120)]),
    ("w409_same_w", "S=100, W", w409_same, [(100, w) for w in (750, 1500, 3000, 6000)]),
    ("w409_same_s", "W=3000, S", w409_same, [(d, 3000) for d in (12, 25, 50, 100)]),
    ("w410_guards_w", "depth=60, writes", w410_guards, [(60, w) for w in (25, 50, 100, 200)]),
    ("w410_guards_d", "writes=100, depth", w410_guards, [(d, 100) for d in (8, 15, 30, 60)]),
    ("w410_chain", "writes=100, chain", w410_chain, [(c, 100) for c in (125, 250, 500, 1000)]),
    ("w405_nested_f", "depth=250, fields", w405_nested, [(f, 250) for f in (250, 500, 1000, 2000)]),
    ("w405_nested_d", "fields=1000, depth", w405_nested, [(1000, d) for d in (30, 60, 120, 240)]),
]


def run_families(binary, out, families, rounds, names):
    families = [f for f in families if not names or f[0] in names]
    def axis_of(sizes):
        return next((i for i in range(len(sizes[0])) if len({s[i] for s in sizes}) > 1), 0)
    gen = os.path.join(os.path.dirname(os.path.abspath(out)), "gen")
    os.makedirs(gen, exist_ok=True)
    with open(out, "w") as f:
        for name, axis, make, sizes in families:
            at = axis_of(sizes)
            for args in sizes:
                path = os.path.join(gen, f"{name}_{'_'.join(map(str, args))}.onsa")
                with open(path, "w") as g:
                    g.write(make(*args))
                rec = measure(binary, path, rounds, {"set": name, "axis": axis, "size": args[at]})
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(f"{name} {args}: {rec.get('total_us', 0) / 1e6:.2f} s {rec.get('outcome', rec.get('error'))}",
                      flush=True)
                if rec.get("total_us", 0) / 1e6 > GROW_LIMIT or "error" in rec:
                    break


def run_corpus(binary, out, rounds):
    with open(out, "w") as f:
        for path, extra in corpus_inputs(binary):
            f.write(json.dumps(measure(binary, path, rounds, extra)) + "\n")


# ---------------------------------------------------------------- report


def heaviest(rec):
    return max(rec["phases_us"].items(), key=lambda kv: kv[1])[0]


def report(files):
    recs = [json.loads(l) for f in files for l in open(f)]
    bad = [r for r in recs if "phases_us" not in r or r.get("status")]
    timed = [r for r in recs if r.get("phases_us")]
    print(f"inputs {len(recs)}, timed {len(timed)}, without a line or ending badly {len(bad)}")
    for r in bad[:10]:
        print("  ", r["path"], r.get("status"), r.get("error"))
    outcomes = {}
    for r in timed:
        outcomes[r["outcome"]] = outcomes.get(r["outcome"], 0) + 1
    print("outcomes", outcomes)
    for name in sorted({r.get("set") for r in timed}):
        rs = [r for r in timed if r.get("set") == name]
        if name == "corpus":
            corpus_report(rs)
        else:
            family_report(name, rs)


def corpus_report(rs):
    total = sum(r["total_us"] for r in rs)
    sums = {p: sum(r["phases_us"][p] for r in rs) for p in rs[0]["phases_us"]}
    print(f"\ncorpus: {len(rs)} inputs, in-process total {total / 1e6:.2f} s, "
          f"process wall {sum(r['wall'] for r in rs):.2f} s, cpu {sum(r['cpu'] for r in rs):.2f} s")
    for p, v in sorted(sums.items(), key=lambda kv: -kv[1]):
        print(f"  {p:<11} {v / 1e6:8.3f} s {100 * v / total:5.1f} %")
    rest = total - sum(sums.values())
    print(f"  {'(rest)':<11} {rest / 1e6:8.3f} s {100 * rest / total:5.1f} %")
    print("  slowest 20 (in-process total; process wall, cpu, rss; heaviest phase):")
    for r in sorted(rs, key=lambda r: -r["total_us"])[:20]:
        h = heaviest(r)
        print(f"    {r['total_us'] / 1e3:8.1f} ms  wall {r['wall'] * 1e3:7.1f} cpu {r['cpu'] * 1e3:7.1f} "
              f"rss {r['rss_mb']:6.1f} MB  {h} {r['phases_us'][h] / 1e3:.1f} ms  {r['path']}")


def family_report(name, rs):
    rs = sorted(rs, key=lambda r: r["size"])
    phases = [p for p in rs[0]["phases_us"] if any(r["phases_us"][p] > r["total_us"] / 20 for r in rs)]
    print(f"\n{name} ({rs[0]['axis']}): ms by phase (those over 5 % somewhere); slope = log(t2/t1)/log(n2/n1) "
          "of the last two sizes with the outcome of the first")
    print("  " + f"{'size':>6} {'total':>9} {'wall':>8} {'cpu':>8} {'rss MB':>7} " + " ".join(f"{p[:8]:>8}" for p in phases))
    for r in rs:
        print("  " + f"{r['size']:>6} {r['total_us'] / 1e3:9.1f} {r['wall'] * 1e3:8.1f} {r['cpu'] * 1e3:8.1f} "
              f"{r['rss_mb']:7.1f} " + " ".join(f"{r['phases_us'][p] / 1e3:8.1f}" for p in phases)
              + f"  {r['outcome']}")
    same = [r for r in rs if r["outcome"] == rs[0]["outcome"]]
    if len(same) >= 2:
        import math
        a, b = same[-2], same[-1]
        k = math.log(b["size"] / a["size"])
        def slope(x, y):
            return f"{math.log(y / x) / k:4.1f}" if x > 0 and y > 0 else "   -"
        print("  slope " + f"{'':>6} {slope(a['total_us'], b['total_us']):>9} {'':>8} {'':>8} "
              f"{slope(a['rss_mb'], b['rss_mb']):>7} "
              + " ".join(f"{slope(a['phases_us'][p], b['phases_us'][p]):>8}" for p in phases))


def main():
    argv = sys.argv[1:]
    rounds = 3
    if "--rounds" in argv:
        i = argv.index("--rounds")
        rounds = int(argv[i + 1])
        del argv[i:i + 2]
    if not argv:
        sys.exit(__doc__)
    cmd, rest = argv[0], argv[1:]
    if cmd == "report":
        report(rest)
    elif cmd in ("corpus", "scale", "quad") and len(rest) >= 2:
        binary = os.path.abspath(rest[0])
        if cmd == "corpus":
            run_corpus(binary, rest[1], rounds)
        else:
            run_families(binary, rest[1], SCALE if cmd == "scale" else QUAD, rounds, rest[2:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
