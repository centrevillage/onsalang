#!/usr/bin/env python3
"""The `#[ignore]` marks of the Rust tests: list them, take them off, set them.

    tools/ignores.py list <path>... [--reason TEXT]
    tools/ignores.py remove <file> <test>...
    tools/ignores.py set <file> <test> <reason>
    tools/ignores.py passing -p <crate> [--test <binary>] [--reason TEXT] [--list] [--timeout S]
    tools/ignores.py stale [<path>...] [--stage-end STAGE] [--root DIR]

`list` prints `file:line<TAB>name<TAB>reason` for every ignored test of the
files (a directory is searched for `.rs` files, build outputs left out);
`--reason` keeps those whose reason contains TEXT. `remove` and `set` rewrite
one file and write it only when every named test is found and can be changed
(the rest of the file stays byte for byte). `passing` runs
`cargo test -p <crate> [--test …] --no-fail-fast -- --ignored` and prints, for
each ignored test of `crates/<crate>`, `pass`, `fail` or `not run`; with
`--list` it runs `-- --ignored --list` instead and only compares the names.
Both report a test cargo ran that the files do not show. It writes nothing.

`stale` (the gate item `ignores`, R-224) reads the ignored tests of the paths
(default `<root>/crates`) as `list` does, and fails on each whose reason starts
with a work ID (`W3-11`) that the files of `tasks/W/` (`tools/pending.py`) mark done
(take the ignore off: `passing` tells whether it passes now) or do not have (a
typo, or a T (of the history), which is no work). With `--stage-end W3` (as `tools/pending.py`), it also fails on each
whose work is of that stage, done or not. A reason that does not start with a
work ID is only counted. It also fails on a form not read, a path that does not
exist, and when it finds no `.rs` file.

The forms read:
- a test function: `#[test]`, then (on lines of their own, in any order, doc
  comments between) `#[ignore]` or `#[ignore = "…"]`, then `fn name(`;
- a test made by a `macro_rules!` of the same file: an arm whose transcriber has
  `#[test]` and `#[ignore]`, `#[ignore = "…"]` or `#[ignore = $reason]` before
  `fn $name(`, and whose matcher is a comma-separated list of `$var:frag`, each
  with an optional prefix of tokens (`reports: $work:expr`). An invocation picks
  the first arm whose parameters it fits (count, prefixes, `ident`). `remove`
  and `set` change an invocation to the arm that gives the wanted marks, when
  the reason is the arm's last parameter: the reason argument is taken off,
  put after the last argument, or rewritten.
Any other `#[ignore` outside the comments (a repetition `$(…)*` in the matcher,
an invocation no arm fits, a reason that is not a string literal, …) is
printed as a form this tool does not read, and the command fails.

Exit 0 on success, 1 when something is not found, cannot be read or changed,
or is stale, or cargo fails; 2 on a usage error.
"""
import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
STR = r'"(?:[^"\\]|\\.)*"'
IGNORE = re.compile(rf"#\[ignore(?:\s*=\s*(\$[A-Za-z_]\w*|{STR}))?\]")
FN = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+([A-Za-z_]\w*)\s*[(<]", re.M)
MACRO_DEF = re.compile(r"\bmacro_rules!\s*([A-Za-z_]\w*)\s*[({\[]")
ARM_TEST = re.compile(r"((?:#\[[^\]]*\]\s*)+)fn\s+(\$?[A-Za-z_]\w*)\s*\(")
PARAM = re.compile(r"(.*?)\$([A-Za-z_]\w*)\s*:\s*(\w+)", re.S)
IDENT = re.compile(r"[A-Za-z_]\w*")
CLOSE = {"(": ")", "[": "]", "{": "}"}
RAW_STR = re.compile(r'b?r(#*)"')
CHAR = re.compile(r"b?'(?:\\[^']+|[^\\'\n])'")
# A reason that names the work it waits for starts with its ID (`W3-11 U3c: …`): the form of a work of a
# stage, so that an ID of another form (a T of the history, which is no work of the list) fails as no work.
WORK_AT_START = re.compile(rf"{repo.STAGE_NAME.pattern}-\d+(?!\d)")


class Unreadable(Exception):
    pass


def mask(s):
    """`s` with the comments and the insides of the string and char literals blanked (same offsets)."""
    out, i, n = list(s), 0, len(s)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        ident_before = i > 0 and (s[i - 1].isalnum() or s[i - 1] == "_")
        raw = None if ident_before else RAW_STR.match(s, i)
        if s.startswith("//", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
        elif s.startswith("/*", i):
            j = s.find("*/", i + 2)
            j = n if j < 0 else j + 2
        elif raw:
            j = s.find('"' + raw.group(1), raw.end())
            j = n if j < 0 else j + 1 + len(raw.group(1))
            blank(raw.end(), j - 1 - len(raw.group(1)))
            i = j
            continue
        elif s[i] == '"' or (s.startswith('b"', i) and not ident_before):
            j = i + 1 + (s[i] == "b")
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            blank(i + 1 + (s[i] == "b"), j)
            i = j + 1
            continue
        elif (m := CHAR.match(s, i)) and not ident_before:
            blank(m.start() + 1, m.end() - 1)
            i = m.end()
            continue
        else:
            i += 1
            continue
        blank(i, j)
        i = j
    return "".join(out)


def close_of(m, i):
    """The index of the bracket closing the one at `i` of the masked text."""
    stack = []
    for j in range(i, len(m)):
        if m[j] in CLOSE:
            stack.append(CLOSE[m[j]])
        elif m[j] in ")]}":
            if not stack or stack.pop() != m[j]:
                raise Unreadable("unbalanced brackets")
            if not stack:
                return j
    raise Unreadable("unbalanced brackets")


def split_args(s, m, a, b):
    """The comma-separated parts of s[a:b] at depth 0, as stripped (start, end) spans."""
    parts, depth, start = [], 0, a
    for j in range(a, b + 1):
        c = m[j] if j < b else ","
        depth += (c in "([{") - (c in ")]}")
        if c == "," and depth == 0:
            lo, hi = start, j
            while lo < hi and s[lo].isspace():
                lo += 1
            while hi > lo and s[hi - 1].isspace():
                hi -= 1
            parts.append((lo, hi))
            start = j + 1
    return parts[:-1] if parts and parts[-1][0] == parts[-1][1] else parts


@dataclass
class Arm:
    params: list  # (prefix tokens, var, frag)
    tests: list  # (name var or name, ignore: None | "" (bare) | "$var" | '"lit"')

    def reason_index(self):
        vars_ = {t[1] for t in self.tests if t[1]}
        if any(not v.startswith("$") for v in vars_) or len(vars_) > 1:
            return None
        names = [p[1] for p in self.params]
        return names.index(vars_.pop()[1:]) if vars_ else None


@dataclass
class Test:
    name: str
    line: int
    reason: str = None
    ignored: bool = False
    span: tuple = None  # direct: the ignore attribute's span, or the `#[test]` line's start
    call: object = None  # macro: (arms, arm index, the argument spans, the close index)


def _arms(s, m, a, b):
    arms, i = [], a
    while True:
        while i < b and m[i].isspace():
            i += 1
        if i >= b:
            return arms
        if m[i] not in CLOSE:
            raise Unreadable("an arm that does not start with a bracket")
        j = close_of(m, i)
        k = re.compile(r"\s*=>\s*").match(m, j + 1)
        if not k or m[k.end()] not in CLOSE:
            raise Unreadable("an arm without `=>`")
        t0, t1 = k.end(), close_of(m, k.end())
        params = []
        for lo, hi in split_args(s, m, i + 1, j):
            p = PARAM.fullmatch(s[lo:hi])
            if not p or "$(" in s[lo:hi]:
                raise Unreadable(f"the parameter `{s[lo:hi]}`")
            params.append((p.group(1).split(), p.group(2), p.group(3)))
        tests, seen = [], 0
        for t in ARM_TEST.finditer(m, t0 + 1, t1):
            attrs = s[t.start(1):t.end(1)]
            ig = IGNORE.search(attrs)
            if "#[test]" in attrs:
                tests.append((t.group(2), None if not ig else (ig.group(1) or "")))
            seen += bool(ig) and "#[test]" in attrs
        if m.count("#[ignore", t0, t1) != seen:
            raise Unreadable("an `#[ignore` of the transcriber not right before `fn $name(` of a test")
        arms.append(Arm(params, tests))
        i = t1 + 1
        if i < b and m[i] == ";":
            i += 1


def _fits(s, arm, args):
    if len(arm.params) != len(args):
        return None
    bind = {}
    for (prefix, var, frag), (lo, hi) in zip(arm.params, args):
        p = re.compile(r"\s*".join(map(re.escape, prefix)) + (r"\s*" if prefix else "")).match(s, lo, hi)
        if not p or p.end() == hi or (frag == "ident" and not IDENT.fullmatch(s[p.end():hi])):
            return None
        bind[var] = (p.end(), hi)
    return bind


def _line(s, i):
    return s.count("\n", 0, i) + 1


def scan(s):
    """The tests of a Rust source and the `#[ignore` it cannot read: (tests, problems)."""
    m = mask(s)
    tests, problems, read_at, macro_spans = [], [], set(), []
    for d in MACRO_DEF.finditer(m):
        end = close_of(m, d.end() - 1)
        macro_spans.append((d.start(), end))
        if "#[ignore" not in m[d.start():end]:
            continue
        try:
            arms = _arms(s, m, d.end(), end)
        except Unreadable as e:
            problems.append(f"{_line(s, d.start())}: the macro `{d.group(1)}`: {e}")
            continue
        read_at.update(k for k in range(d.start(), end) if m.startswith("#[ignore", k))
        if not any(t[1] is not None for a in arms for t in a.tests):
            continue
        for c in re.finditer(rf"\b{d.group(1)}!\s*[(\[{{]", m):
            if any(lo <= c.start() < hi for lo, hi in macro_spans):
                continue
            close = close_of(m, c.end() - 1)
            args = split_args(s, m, c.end(), close)
            fit = next(((k, b) for k, a in enumerate(arms) if (b := _fits(s, a, args))), None)
            if fit is None:
                problems.append(f"{_line(s, c.start())}: no arm of `{d.group(1)}!` fits this invocation")
                continue
            k, bind = fit
            call = (arms, k, args, close)
            for var, ig in arms[k].tests:
                name = s[slice(*bind[var[1:]])] if var.startswith("$") else var
                reason = None
                if ig and ig.startswith("$"):
                    reason = s[slice(*bind[ig[1:]])]
                elif ig:
                    reason = ig
                if reason is not None and not re.fullmatch(STR, reason):
                    problems.append(f"{_line(s, c.start())}: `{name}`: the reason `{reason}` is not a string literal")
                    continue
                at = bind[var[1:]][0] if var.startswith("$") else c.start()
                tests.append(Test(name, _line(s, at), reason and unescape(reason), ig is not None,
                                  call=call))
    for f in FN.finditer(m):
        if any(lo <= f.start() < hi for lo, hi in macro_spans):
            continue
        lines, at = [], f.start()
        while at > 0:
            prev = s.rfind("\n", 0, at - 1) + 1
            text = s[prev:at - 1].strip()
            if not (text.startswith("///") or (text.startswith("#[") and text.endswith("]"))):
                break
            lines.append(prev)
            at = prev
        test_line = next((p for p in lines if s[p:s.find("\n", p)].strip().startswith("#[test]")), None)
        ig = [g for p in lines for g in IGNORE.finditer(s, p, s.find("\n", p))]
        if test_line is None or len(ig) > 1:
            continue
        read_at.update(g.start() for g in ig)
        reason = unescape(ig[0].group(1)) if ig and ig[0].group(1) else None
        tests.append(Test(f.group(1), _line(s, f.start()), reason, bool(ig), span=(ig[0].span() if ig else test_line)))
    for k in (k for k in range(len(m)) if m.startswith("#[ignore", k) and k not in read_at):
        problems.append(f"{_line(s, k)}: an `#[ignore` of a form this tool does not read")
    return tests, problems


def unescape(lit):
    """The value of a Rust string literal (the simple escapes)."""
    table = {"n": "\n", "t": "\t", "r": "\r", "0": "\0"}
    return re.sub(r"\\(.)", lambda m: table.get(m.group(1), m.group(1)), lit[1:-1])


def rust_str(text):
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def _edit_call(s, t, ignored, reason, tests):
    arms, k, args, _ = t.call
    a = arms[k]
    ra = a.reason_index()
    if ra is not None and ra != len(a.params) - 1:
        raise Unreadable("the reason is not the last parameter of the arm")
    base = args[:-1] if ra is not None else args
    mates = [u for u in tests if u.call is t.call]
    want = {u.name for u in mates if u.ignored and u is not t} | ({t.name} if ignored else set())
    cur = next((u.reason for u in mates if u.ignored and u.reason is not None), None)
    reason = reason if reason is not None else cur
    for b in arms:
        rb = b.reason_index()
        if (rb is not None and rb != len(b.params) - 1) or len(b.params) - (rb is not None) != len(base):
            continue
        bind = _fits(s, Arm(b.params[:len(base)], []), base)
        if bind is None:
            continue
        names = {s[slice(*bind[v[1:]])] if v.startswith("$") else v for v, ig in b.tests if ig is not None}
        if names != want or (want and rb is None):
            continue
        new = " ".join(b.params[-1][0]) + (" " if b.params[-1][0] else "") + rust_str(reason) if rb is not None else None
        if ra is not None and new is not None:
            return args[-1][0], args[-1][1], new
        if ra is not None:
            return args[-2][1], args[-1][1], ""
        sep = s[args[-2][1]:args[-1][0]] if len(args) > 1 else ", "
        return args[-1][1], args[-1][1], sep + new
    raise Unreadable("no arm of the macro gives these marks")


def edit(s, name, ignored, reason=None):
    """`s` with the test `name` ignored (with `reason`) or not. Raises Unreadable."""
    tests, problems = scan(s)
    if problems:
        raise Unreadable("the file has forms this tool does not read: " + "; ".join(problems))
    found = [t for t in tests if t.name == name]
    if len(found) != 1:
        raise Unreadable(f"`{name}`: {'no test' if not found else 'more than one test'} of this name")
    t = found[0]
    if t.ignored == ignored and (not ignored or reason in (None, t.reason)):
        return s
    if t.call:
        a, b, new = _edit_call(s, t, ignored, reason, tests)
    elif t.ignored and ignored:
        a, b, new = *t.span, f"#[ignore = {rust_str(reason)}]"
    elif t.ignored:
        a = s.rfind("\n", 0, t.span[0]) + 1
        b = s.find("\n", t.span[1]) + 1 or len(s)
        if s[a:t.span[0]].strip() or s[t.span[1]:b].strip():
            a, b = t.span[0], t.span[1] + len(s[t.span[1]:]) - len(s[t.span[1]:].lstrip(" "))
        new = ""
    else:
        line = s[t.span:s.find("\n", t.span)]
        indent = line[:len(line) - len(line.lstrip())]
        a = b = s.find("\n", t.span) + 1
        new = f"{indent}#[ignore = {rust_str(reason)}]\n"
    out = s[:a] + new + s[b:]
    after = {u.name: (u.ignored, u.reason) for u in scan(out)[0]}
    shared = {u.name for u in tests if t.call and u.call is t.call}
    if after.get(name, (None,))[:1] != (ignored,) or (ignored and reason is not None and after[name][1] != reason) or any(
        after.get(u.name) != (u.ignored, u.reason) for u in tests if u.name != name and u.name not in shared
    ):
        raise Unreadable(f"`{name}`: the change did not give the wanted marks")
    return out


def rs_files(paths):
    for p in paths:
        p = Path(p)
        if p.is_dir():
            yield from sorted(f for f in p.rglob("*.rs") if not repo.is_build_output(p, f.relative_to(p).as_posix()))
        else:
            yield p


def collect(paths, reason=None):
    found, problems = [], []
    for f in rs_files(paths):
        tests, probs = scan(f.read_text(encoding="utf-8"))
        problems += [f"{f}:{p}" for p in probs]
        found += [(f, t) for t in tests if t.ignored and (reason is None or reason in (t.reason or ""))]
    return found, problems


def show(f, t):
    return f"{f}:{t.line}\t{t.name}\t{t.reason if t.reason is not None else '-'}"


def run_cargo(crate, binary, listing, timeout, cwd=ROOT):
    """{(group, name): status} of the ignored tests cargo runs or lists (group: `tests/x.rs`, or `src`)."""
    cmd = ["cargo", "test", "-p", crate, *(["--test", binary] if binary else []), "--no-fail-fast", "--", "--ignored"]
    r = subprocess.run(cmd + (["--list"] if listing else []), cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True, timeout=timeout)
    out, group, binaries = {}, None, 0
    for line in r.stdout.splitlines():
        if run := re.match(r"\s*Running (?:unittests )?(\S+) \(", line):
            group = run.group(1) if run.group(1).startswith("tests/") else "src"
            binaries += 1
        elif res := re.match(r"test (\S+) \.\.\. (ok|FAILED)$" if not listing else r"(\S+): test$", line):
            out[(group, res.group(1).rsplit("::", 1)[-1])] = "listed" if listing else res.group(2)
    return out, r.returncode if binaries else f"{r.returncode}, and no `Running` line", r.stdout


def passing(args):
    crate_dir = ROOT / "crates" / args.p
    if not crate_dir.is_dir():
        print(f"no crate directory {crate_dir}", file=sys.stderr)
        return 1
    found, problems = collect([crate_dir])
    try:
        ran, code, text = run_cargo(args.p, args.test, args.list, args.timeout)
    except subprocess.TimeoutExpired:
        print(f"cargo did not finish in {args.timeout} s")
        return 1
    if not ran and code != 0 or isinstance(code, str):
        print(text[-3000:])
        print(f"cargo failed (exit {code}) and ran no ignored test")
        return 1
    seen = set()
    for f, t in found:
        rel = f.relative_to(crate_dir).as_posix()
        key = (rel if rel.startswith("tests/") else "src", t.name)
        seen.add(key)
        if args.test and key[0] != f"tests/{args.test}.rs":
            continue
        if args.reason is None or args.reason in (t.reason or ""):
            status = {"ok": "pass", "FAILED": "fail"}.get(ran.get(key), ran.get(key, "not run"))
            print(f"{status}\t{show(f.relative_to(ROOT) if f.is_relative_to(ROOT) else f, t)}")
    unknown = sorted(k for k in ran if k not in seen)
    for g, n in unknown:
        print(f"cargo ran `{n}` of {g}, which the files do not show as ignored")
    for p in problems:
        print(p)
    return 1 if unknown or problems else 0


def stale(args):
    root = Path(args.root)
    paths = [Path(p) for p in args.paths] or [root / "crates"]
    try:
        docs = pending.load_docs(root)
    except pending.DocsError as e:
        print(f"cannot read the IDs: {e}")
        return 1
    if args.stage_end is not None and (problem := pending.stage_problem(args.stage_end, docs)):
        print(problem, file=sys.stderr)
        return 2
    missing = [p for p in paths if not p.exists()]
    files = list(rs_files(p for p in paths if p.exists()))
    found, problems = collect(files)
    problems += [f"{p}: no such file or directory" for p in missing]
    if not files:
        problems.append("no `.rs` file found in " + ", ".join(map(str, paths)))
    failures, others = [], 0
    for f, t in found:
        work = WORK_AT_START.match(t.reason or "")
        if not work:
            others += 1
            continue
        w, end = work.group(0), args.stage_end
        why = (f"is no work of {docs.works_at}" if w not in docs.works
               else "is done: take the ignore off (`passing` tells whether the test passes)" if w in docs.done
               else f"is of {end}, which ends here" if end and pending.left_at_end(w, end, docs.stages)
               else None)  # fmt: skip
        if why:
            failures.append(f"{show(pending.show_path(f, root), t)}\n    the work {w} {why}")
    for line in failures + problems:
        print(line)
    counts = f"{len(found) - others} by a work, {others} for another reason"
    bad = f"; {len(failures)} failing, {len(problems)} problem(s)" if failures or problems else ""
    print(f"{len(found)} ignored test(s) in {len(files)} file(s): {counts}{bad}")
    return 1 if failures or problems else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("list")
    p.add_argument("paths", nargs="+")
    p.add_argument("--reason")
    p = sub.add_parser("remove")
    p.add_argument("file")
    p.add_argument("names", nargs="+")
    p = sub.add_parser("set")
    p.add_argument("file")
    p.add_argument("name")
    p.add_argument("reason")
    p = sub.add_parser("passing")
    p.add_argument("-p", required=True, metavar="CRATE")
    p.add_argument("--test")
    p.add_argument("--reason")
    p.add_argument("--list", action="store_true")
    p.add_argument("--timeout", type=float, default=540)
    p = sub.add_parser("stale")
    p.add_argument("paths", nargs="*")
    p.add_argument("--stage-end", metavar="STAGE")
    p.add_argument("--root", default=ROOT)
    args = ap.parse_args(argv)
    if args.cmd == "passing":
        return passing(args)
    if args.cmd == "stale":
        return stale(args)
    if args.cmd == "list":
        found, problems = collect(args.paths, args.reason)
        for f, t in found:
            print(show(f, t))
        for p in problems:
            print(p)
        print(f"{len(found)} ignored test(s)" + (f", {len(problems)} form(s) not read" if problems else ""))
        return 1 if problems else 0
    path = Path(args.file)
    s = text = path.read_text(encoding="utf-8")
    failed = []
    for name in args.names if args.cmd == "remove" else [args.name]:
        try:
            s = edit(s, name, args.cmd == "set", getattr(args, "reason", None))
        except Unreadable as e:
            failed.append(str(e))
    for f in failed:
        print(f"{path}: {f}")
    if failed:
        print(f"{path}: not written")
        return 1
    if s != text:
        path.write_text(s, encoding="utf-8")
    print(f"{path}: {'written' if s != text else 'unchanged'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
