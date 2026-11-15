"""measure_stages.py: the time of each phase of the compiler (X-20/U1), with `onsa_cases --phases`.

  measure_stages.py corpus BIN OUT.jsonl   the cases of tests/spec, the files of std, examples/
  measure_stages.py scale BIN OUT.jsonl    a usual file (tests/spec/examples/voice.onsa) times 1 to 16
  measure_stages.py quad BIN OUT.jsonl [NAME...]  the quadratic forms left to X-20 by W4-05 to W4-10, and R-386
  measure_stages.py report OUT.jsonl...    the sums, the slowest inputs, the growth by family
  measure_stages.py corpus|scale|quad BIN OUT.jsonl --vs BIN2 OUT2.jsonl [NAME...]  two binaries in turn
      (W6-04 U17): each input is timed by BIN and BIN2 one after the other, the first of the two turned round
      from input to input and from round to round, into OUT and OUT2 (the same inputs in the same order; a
      family stops at the same size in both when either passes 10 s or fails); read them with `compare`
  measure_stages.py compare A.jsonl B.jsonl... [--phases P,Q]  versions side by side (W6-04 U11): per set and
      size (a corpus: the sum of the inputs every version timed, then its 20 slowest), each version's ms of the
      total and of the phases (P,Q, else those over 5 % somewhere; nan where a version has not the phase),
      rss MB and wall ms; with two, B/A

BIN is an `onsa_cases` (debug or release). Each input is checked (and lowered to Core when the
check reports nothing, `--lower`) in its own process, ROUNDS times (default 1, `--rounds`); a line
keeps the least of each phase and of the whole, with the wall clock and the cpu (user + sys) of
the process and its largest resident memory. Run it on a quiet machine, one at a time (no
parallel runs: the memory is measured too). A generated family stops growing past 10 s
(rules/common.md 3). Generated inputs go to OUT's directory, under gen/.
"""
import contextlib
import itertools
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
NAN = float("nan")  # `compare`: a phase a version does not have (shown as nan, not 0)


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


def measure(binaries, path, rounds, extra=None, turn=0):
    """A line of each of `binaries`, the least of ROUNDS runs; in each round they run one after the other, in
    their order when `turn` + the round is even, else the other way round (as `compare.py speed`'s `turn`)."""
    recs = [[] for _ in binaries]
    for r in range(rounds):
        for i in (range(len(binaries)) if (turn + r) % 2 == 0 else reversed(range(len(binaries)))):
            recs[i].append(run_once(binaries[i], path))
    return [least(rs, rounds, extra) for rs in recs]


def least(recs, rounds, extra):
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


def w602_breaks(n):
    """W6-02 U1b (memo 1.6): in a loop, n locals declared, then each moved and followed by a `break` under
    an `if` (each `break` joins the changes since the loop's head, n x n)."""
    h = ("pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(1) }\n"
         "pub fn take(move b: Buf[F32]) uses {Alloc} {}\n")
    body = [f"    let b{i} = mk()" for i in range(n)]
    body += [x for i in range(n) for x in (f"    take(move b{i})", "    if c { break }")]
    return h + "pub fn t(c: Bool) uses {Alloc} {\n  while c {\n" + "\n".join(body) + "\n  }\n}\n"



def w602_shape(form, k):
    """W6-02 U1d (the break side of U1c, `shapes.py`), each of k: `w1`, in a loop, `a` assigned again and a
    `continue` under an `if`; `w12`, a loop with a local; `w8`, in a `while true`, `a` assigned, a `continue`,
    `a` moved to a local and refilled, a `break`."""
    h = ("pub fn mk() -> Buf[F32] uses {Alloc} { Buf.zeroed(1) }\n"
         "pub fn take(move b: Buf[F32]) -> U32 uses {Alloc} { 0 }\n")
    if form == "w1":
        body = ["  for _ in 0..<n {"] + ["    a = mk()\n    if c { continue }"] * k + ["  }"]
    elif form == "w12":
        body = [f"  for i{j} in 0..<n {{\n    let u{j} = i{j} + 1\n    s = s + u{j}\n  }}" for j in range(k)]
    else:
        body = ["  while true {"] + [f"    a = mk()\n    if c {{ continue }}\n    let t{j} = take(move a)\n"
                                     f"    a = mk()\n    s = s + t{j}\n    if c {{ break }}" for j in range(k)] + ["  }"]
    return (h + "pub fn t(c: Bool, n: U32) -> U32 uses {Alloc} {\n  var a = mk()\n  var s = 0\n"
            + "\n".join(body) + "\n  s + take(move a)\n}\n")

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


def r464_fail_readers(n):
    """R-464 fix (W6-04 U5/b M-1): n structs with a field in error, each before a user that asks the kind of a
    chain of n structs (the answers kept while the fields in error are read as the error type)."""
    chain = "".join(f"pub struct C{i} {{ f: C{i + 1}, g: I32 }}\n" for i in range(n)) + f"pub struct C{n} {{ g: I32 }}\n"
    pairs = "".join(f"pub struct F{i}[T1: ?Dup] {{ a: I32, w: Array[T1] }}\npub struct U{i} {{ h: OC[C0] }}\n"
                    for i in range(n))
    return "pub struct OC[T: Copy] { t: T }\n" + pairs + chain


def r386_arms(form, n):
    """R-386 (W5-13 U6b): a match of n arms and a `_`: `Some(i)`, the first n of the 5 columns of an enum of
    8 variants (rows of one head, which an arm passes by), or `(i, _)` and `(_, i)` in turn (rows a `_` of
    the arm meets, still n x n), or n arms `(i, 0, ..)` of 8 columns, a `_` and n arms `(_, 0, ..)` (each
    of the last meets all of the first under its `_`, as many rows as nodes of the tree before)."""
    if form == "table":
        rows = itertools.islice(itertools.product(range(8), repeat=5), n)
        arms = ["(%s)" % ", ".join(f"E.V{v}" for v in t) for t in rows]
        head, ty = "pub enum E { %s }\n" % ", ".join(f"V{i}" for i in range(8)), "(E, E, E, E, E)"
    elif form == "tail":
        zeros = ", 0" * 7
        arms = [f"({i}{zeros})" for i in range(n)] + ["_"] + [f"(_{zeros})"] * n
        head, ty = "", "(%s)" % ", ".join(["I32"] * 8)
    else:
        arms = [f"Some({i})" for i in range(n)] if form == "some" else [
            f"({i}, _)" if i % 2 else f"(_, {i})" for i in range(n)]
        head, ty = "", "Option[I32]" if form == "some" else "(I32, I32)"
    body = "".join(f"    {a} => 0,\n" for a in arms + ["_"])
    return f"{head}pub fn f(x: {ty}) -> I32 {{\n  match x {{\n{body}  }}\n}}\n"


def w602_guards(n):
    """W6-02 U2b: one owned `match` with n guarded arms, each binding three owned values (a guard that is false
    gives them back to the head; after U2a and before U2b, the paths an arm is tried at kept the bindings of
    every arm before it, n x n)."""
    h = "pub fn len_of(b: Buf[F32]) -> U32 { b.len() }\n"
    arms = [f"    ({i}, b, c, d) if len_of(b) > {i} && len_of(c) > 0 && len_of(d) > 0 => len_of(b) + len_of(c),"
            for i in range(n)]
    return (h + "pub fn t(move o: (U32, Buf[F32], Buf[F32], Buf[F32])) -> U32 uses {Alloc} {\n  match move o {\n"
            + "\n".join(arms) + "\n    _ => 0,\n  }\n}\n")

def w602_guard_moves(n):
    """W6-02 U2b, the break side (L1): one owned `match` with n guarded arms, each guard moving a distinct
    outer local (each arm is tried at the paths of every guard before it, n x n; to W6-04)."""
    h = ("pub fn eat(move b: Buf[F32]) -> Bool uses {Alloc} { true }\n")
    ps = ", ".join(f"move z{i}: Buf[F32]" for i in range(n))
    arms = "".join(f"    Some(b{i}) if eat(move z{i}) => {i},\n" for i in range(n))
    return (h + f"pub fn t(move o: Option[Buf[F32]], {ps}) -> U32 uses {{Alloc}} {{\n  match move o {{\n{arms}"
            + "    _ => 0,\n  }\n}\n")

def w602_try_copy(n):
    """W6-02 U3: n Copy locals, each made by a `?`: each `?` walks the items of the scopes it leaves (memo 1.6,
    O(sum of S_k)) though none of them drops (n x n with no output; the walk past Copy and dead items is W6-04's)."""
    body = [f"  let k{i}: U32 = r? + {i}\n  s = s + k{i}" for i in range(n)]
    return "pub fn t(r: Option[U32]) -> Option[U32] {\n  var s: U32 = 0\n" + "\n".join(body) + "\n  Some(s)\n}\n"

def w602_releases(form, n):
    """W6-02 U4a (D12): one owned `Str` released in n branches (S-1030, R-255): `ret`, each branch returns its
    release (sets of one); `arms`, the n arms of a `match` release it and it is used after their join (one set
    of n, restored once); `seq`, n `if`s each release it after the release before is used (each join meets
    the set of the ifs before, n x n with the sets of the releases a join copies). W6-02 U4a2: `loop`, the n arms
    of a `match` in a loop release it, used by each arm as the loop's head (the set of n each arm meets, n x n
    if copied by each use); `exits`, the n arms release it, then n `if`s return (the set of n each exit's drop
    point keeps, n x n if copied by each). The lowering of these forms is n x n before U4a too (4000 `if`s:
    about 12 to 20 s, the check about 0.05 s), so the sizes stop at 4000."""
    h = "pub fn eat(move s: Str) -> U32 uses {Alloc} { s.len() }\n"
    eats = "".join(f"    {i} => {{ a = a + eat(s) }},\n" for i in range(n))
    if form == "loop":
        body = f"  var a: U32 = 0\n  while c {{\n  match k {{\n{eats}    _ => {{ a = a + s.len() }},\n  }}\n  }}\n  a\n"
    elif form == "exits":
        body = f"  var a: U32 = 0\n  match k {{\n{eats}    _ => {{ a = a + eat(s) }},\n  }}\n"
        body += "  if c { return a }\n" * n + "  a\n"
    elif form == "ret":
        body = "".join(f"  if k == {i} {{ return eat(s) }}\n" for i in range(n)) + "  0\n"
    elif form == "arms":
        arms = "".join(f"    {i} => eat(s),\n" for i in range(n))
        body = f"  let a = match k {{\n{arms}    _ => 0,\n  }}\n  a + s.len()\n"
    else:
        body = "  var a: U32 = 0\n" + "".join(f"  if k == {i} {{ a = a + eat(s) }}\n" for i in range(n))
        body += "  a + s.len()\n"
    c = ", c: Bool" if form in ("loop", "exits") else ""
    return h + f"pub fn t(move s: Str, k: U32{c}) -> U32 uses {{Alloc}} {{\n" + body + "}\n"

SCALE = [("voice", "decls x", voice_times, [(k,) for k in (1, 2, 4, 8, 16)])]

QUAD = [
    ("w407_manylocals", "M=N=n", w407_manylocals, [(n, n) for n in (1000, 2000, 4000, 8000, 16000)]),
    ("w407_manylocals_n", "M=1000, N", w407_manylocals, [(1000, n) for n in (1000, 2000, 4000, 8000)]),
    ("w407_manylocals_m", "N=1000, M", w407_manylocals, [(m, 1000) for m in (1000, 2000, 4000, 8000)]),
    ("w602_breaks", "moves and breaks", w602_breaks, [(n,) for n in (1000, 2000, 4000, 8000)]),
    ("w602_reassign_continue", "continues", w602_shape, [("w1", n) for n in (1000, 2000, 4000, 8000)]),
    ("w602_loops_only", "loops", w602_shape, [("w12", n) for n in (2000, 4000, 8000, 16000)]),
    ("w602_continue_moves", "moves, continues and breaks", w602_shape, [("w8", n) for n in (250, 500, 1000, 2000)]),
    ("w602_guards", "guarded arms", w602_guards, [(n,) for n in (1000, 2000, 4000, 8000)]),
    ("w602_guard_moves", "guards moving outer locals", w602_guard_moves, [(n,) for n in (500, 1000, 2000, 4000)]),
    ("w602_try_copy", "Copy locals and ?", w602_try_copy, [(n,) for n in (1000, 2000, 4000, 8000)]),
    ("w602_releases", "returned releases", w602_releases, [("ret", n) for n in (500, 1000, 2000, 4000)]),
    ("w602_release_arms", "releases joined", w602_releases, [("arms", n) for n in (500, 1000, 2000, 4000)]),
    ("w602_release_seq", "releases used after", w602_releases, [("seq", n) for n in (500, 1000, 2000, 4000)]),
    ("w602_release_loop_arms", "releases at a loop's head", w602_releases, [("loop", n) for n in (500, 1000, 2000, 4000)]),
    ("w602_release_exits", "releases, then exits", w602_releases, [("exits", n) for n in (500, 1000, 2000, 4000)]),
    ("w409_held_w", "F=120, W", w409_held, [(120, w) for w in (1500, 3000, 6000, 12000)]),
    ("w409_held_f", "W=6000, F", w409_held, [(f, 6000) for f in (15, 30, 60, 120)]),
    ("w409_same_w", "S=100, W", w409_same, [(100, w) for w in (750, 1500, 3000, 6000)]),
    ("w409_same_s", "W=3000, S", w409_same, [(d, 3000) for d in (12, 25, 50, 100)]),
    ("w410_guards_w", "depth=60, writes", w410_guards, [(60, w) for w in (25, 50, 100, 200)]),
    ("w410_guards_d", "writes=100, depth", w410_guards, [(d, 100) for d in (8, 15, 30, 60)]),
    ("w410_chain", "writes=100, chain", w410_chain, [(c, 100) for c in (125, 250, 500, 1000)]),
    ("w405_nested_f", "depth=250, fields", w405_nested, [(f, 250) for f in (250, 500, 1000, 2000)]),
    ("w405_nested_d", "fields=1000, depth", w405_nested, [(1000, d) for d in (30, 60, 120, 240)]),
    ("r464_fail_readers", "fields in error and chain", r464_fail_readers, [(n,) for n in (250, 500, 1000, 2000)]),
    ("r386_some", "arms", r386_arms, [("some", n) for n in (5000, 10000, 20000, 40000)]),
    ("r386_table", "arms", r386_arms, [("table", n) for n in (4000, 8000, 16000, 32000)]),
    ("r386_cross", "arms", r386_arms, [("cross", n) for n in (2500, 5000, 10000, 20000)]),
    ("r386_tail", "arms", r386_arms, [("tail", n) for n in (1000, 2000, 4000, 8000)]),
]


def run_families(binaries, outs, families, rounds, names):
    families = [f for f in families if not names or f[0] in names]
    def axis_of(sizes):
        return next((i for i in range(len(sizes[0])) if len({s[i] for s in sizes}) > 1), 0)
    gen = os.path.join(os.path.dirname(os.path.abspath(outs[0])), "gen")
    os.makedirs(gen, exist_ok=True)
    with contextlib.ExitStack() as stack:
        fs = [stack.enter_context(open(out, "w")) for out in outs]
        for name, axis, make, sizes in families:
            at = axis_of(sizes)
            for k, args in enumerate(sizes):
                path = os.path.join(gen, f"{name}_{'_'.join(map(str, args))}.onsa")
                with open(path, "w") as g:
                    g.write(make(*args))
                recs = measure(binaries, path, rounds, {"set": name, "axis": axis, "size": args[at]}, k)
                for f, rec, tag in zip(fs, recs, ["", " (--vs)"] if len(recs) > 1 else [""]):
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    print(f"{name} {args}{tag}: {rec.get('total_us', 0) / 1e6:.2f} s "
                          f"{rec.get('outcome', rec.get('error'))}", flush=True)
                if any(rec.get("total_us", 0) / 1e6 > GROW_LIMIT or "error" in rec for rec in recs):
                    break  # both stop at this size


def run_corpus(binaries, outs, rounds):
    with contextlib.ExitStack() as stack:
        fs = [stack.enter_context(open(out, "w")) for out in outs]
        for k, (path, extra) in enumerate(corpus_inputs(binaries[0])):
            for f, rec in zip(fs, measure(binaries, path, rounds, extra, k)):
                f.write(json.dumps(rec) + "\n")


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


def compare(files, chosen):
    vs = [[json.loads(l) for l in open(f)] for f in files]
    names = [chr(ord("A") + i) for i in range(len(files))]
    print("versions: " + ", ".join(f"{n} {f} ({sum(not r.get('phases_us') for r in v)} without a line)"
                                   for n, f, v in zip(names, files, vs)))
    for s in sorted({r.get("set") for v in vs for r in v}, key=str):
        by = [{r.get("size", r["path"]): r for r in v if r.get("set") == s and r.get("phases_us")} for v in vs]
        rs = [r for b in by for r in b.values()]
        phases = chosen or sorted({p for r in rs for p, us in r["phases_us"].items() if us > r["total_us"] / 20})
        cols = lambda r: [r["total_us"] / 1e3] + [r["phases_us"].get(p, NAN) / 1e3 for p in phases] + [
            r["rss_mb"], r["wall"] * 1e3]  # noqa: E731
        keys = sorted({k for b in by for k in b}, key=lambda k: (str(type(k)), k))
        rows = [(k, [cols(b[k]) if k in b else None for b in by]) for k in keys]
        if s == "corpus":
            both = [k for k in keys if all(k in b for b in by)]
            total = [[(max if i == len(phases) + 1 else sum)(x) for i, x in enumerate(zip(*map(cols, map(b.get, both))))] for b in by]
            rows = [(f"(sum of {len(both)}; rss: max)", total)] + sorted(rows, key=lambda kr: -max(c[0] for c in kr[1] if c))[:20]
        print(f"\n{s} (ms, rss MB)\n  {'':>48} " + " ".join(f"{h[:9]:>9}" for h in ["total", *phases, "rss MB", "wall"]))
        for k, vals in rows:
            for n, v in zip(names, vals):
                print(f"  {str(k)[-44:]:>44} {n:>3} " + (" ".join(f"{x:9.1f}" for x in v) if v else "  -"))
            if len(vals) == 2 and all(vals):
                print(f"  {'':>44} B/A " + " ".join(f"{y / x:9.2f}" if x else "        -" for x, y in zip(*vals)))


def main():
    argv = sys.argv[1:]
    rounds = 1  # the user, 2026-11-02: once is enough; the noise is the machine's load, which more rounds do not take away
    if "--rounds" in argv:
        i = argv.index("--rounds")
        rounds = int(argv[i + 1])
        del argv[i:i + 2]
    phases = []
    if "--phases" in argv:
        i = argv.index("--phases")
        phases = argv[i + 1].split(",")
        del argv[i:i + 2]
    vs = []
    if "--vs" in argv:
        i = argv.index("--vs")
        vs = argv[i + 1:i + 3]
        del argv[i:i + 3]
        if len(vs) < 2:
            sys.exit("--vs BIN2 OUT2.jsonl: a second binary and its output")
    if not argv:
        sys.exit(__doc__)
    cmd, rest = argv[0], argv[1:]
    if cmd == "report":
        report(rest)
    elif cmd == "compare" and rest:
        compare(rest, phases)
    elif cmd in ("corpus", "scale", "quad") and len(rest) >= 2:
        binaries, outs = [os.path.abspath(rest[0]), *map(os.path.abspath, vs[:1])], [rest[1], *vs[1:]]
        if len({os.path.abspath(o) for o in outs}) < len(outs):
            sys.exit("--vs: OUT2.jsonl is OUT.jsonl")
        if cmd == "corpus":
            run_corpus(binaries, outs, rounds)
        else:
            run_families(binaries, outs, SCALE if cmd == "scale" else QUAD, rounds, rest[2:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
