#!/usr/bin/env python3
"""Self-tests of tools/compare.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_compare.py
"""
import ast
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import compare  # noqa: E402
import fuzz  # noqa: E402
import repo  # noqa: E402
from selftest_support import git_in, quiet_out  # noqa: E402


# A made-up `onsa` of `Compare`: what its spec says for the whole command (`check tests/a.onsa`), else for the case,
# else for "*"; it logs its name to `log` and its name and command to `calls`.
FAKE_DIAGS = """#!{exe}
import json, os, signal, sys
here, name = os.path.split(sys.argv[0])
with open(os.path.join(here, "log"), "a") as f:
    f.write(name + "\\n")
with open(os.path.join(here, "calls"), "a") as f:
    f.write(" ".join([name, *sys.argv[1:]]) + "\\n")
spec = json.load(open(os.path.join(here, "spec.json"))).get(name, {{}})
code, out, *more = spec.get(" ".join(sys.argv[1:]), spec.get(sys.argv[-1], spec.get("*", [0, {{"diagnostics": []}}])))
if code == "kill":
    os.kill(os.getpid(), signal.SIGKILL)
out = out if isinstance(out, str) or out is None else json.dumps(out)
if sys.argv[1:-1] == ["fmt"]:  # `fmt <file>` writes the file (None removes it), then prints more[0], leaves more[1]
    if out is None:
        os.remove(sys.argv[-1])
    else:
        open(sys.argv[-1], "w").write(out)
    sys.stdout.write(more[0] if more else "")
    if more[1:]:
        open(more[1], "w").close()
else:
    sys.stdout.write(out)
sys.exit(code)
"""


# A made-up `onsa` of `Compare.test_probe`: E0302 on each file of the package with `bad` (the one named `new`: with
# `new` too), as JSON with `--json`, else as text (`new` adds to the message); `kill` in main.onsa kills it.
FAKE_PROBE = """#!{exe}
import json, os, signal, sys
d, new = sys.argv[-1], os.path.basename(sys.argv[0]) == "new"
files = sorted(os.path.relpath(os.path.join(r, f), d) for r, _, fs in os.walk(d) for f in fs)
text = {{f: open(os.path.join(d, f)).read() for f in files}}
if "kill" in text.get("main.onsa", ""):
    os.kill(os.getpid(), signal.SIGKILL)
bad = [f for f in files if "bad" in text[f] or (new and "new" in text[f])]
if "--json" in sys.argv:
    print(json.dumps({{"diagnostics": [{{"code": "E0302", "span": {{"file": f, "line": 1, "col": 2}}}} for f in bad]}}))
else:
    print("\\n".join(f"{{d}}/{{f}}:1:2: error[E0302]: m" + " (new)" * new for f in bad) or " ".join(sys.argv[1:-1]))
sys.exit(1 if bad else 0)
"""

# A made-up `onsa build --target T --out O PKG` of `Compare.test_c`: [exit code, the C] of `build.json[its name][T]`
# (else [0, "int a;"]); on 0 it writes the C, an archive of other bytes each time and the out directory, and says so.
FAKE_BUILD = """#!{exe}
import json, os, sys
here, name = os.path.split(sys.argv[0])
target, out, pkg = sys.argv[3], sys.argv[5], sys.argv[6]
code, c = json.load(open(os.path.join(here, "build.json")))[name].get(target, [0, "int a;\\n"])
if code == 0:
    os.makedirs(out)
    open(os.path.join(out, "m.c"), "w").write(c)
    open(os.path.join(out, "m.a"), "wb").write(os.urandom(8))
    open(os.path.join(out, "onsa_build.json"), "w").write(json.dumps({{"out_dir": out}}))
print(f"built {{target}} in {{out}} from {{pkg}}" if code == 0 else "m.onsa:1:2: error[E0200]: m")
sys.exit(code)
"""

CASES = """
=== a
pub fn f() {}
=== b

--- main.onsa
bad
--- sub/x.onsa
new
=== c
--- onsa.toml
[package]
name = "own"
=== d
bad
=== k
kill
"""


class Compare(unittest.TestCase):
    """tools/compare.py diags / speed / probe (X-9 U15, W4-03): the differences of the diagnostics, the cases of the
    fuzz's seeds, the order of the binaries turned round every other round, the cases of a file, and the help."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for rel in ("a", "b", "c", "d", "fuzz/z", "p/x", "p/sub/y"):
            (self.root / "tests" / f"{rel}.onsa").parent.mkdir(parents=True, exist_ok=True)
            (self.root / "tests" / f"{rel}.onsa").write_text("pub fn f() {}\n")
        (self.root / "tests/p/onsa.toml").write_text("[package]\n")
        self.bin = self.root / "bin"
        self.bin.mkdir()

    def fakes(self, spec, *names):
        """Made-up `onsa`s in bin/: each prints what `spec[its name][the case]` says ([exit code or "kill", stdout]),
        or `spec[its name]["*"]`, or no diagnostics, and logs its name."""
        (self.bin / "spec.json").write_text(json.dumps(spec))
        for n in names:
            (self.bin / n).write_text(FAKE_DIAGS.format(exe=sys.executable))
            (self.bin / n).chmod(0o755)
        return [str(self.bin / n) for n in names]

    def diags(self, spec):
        before, after = self.fakes(spec, "before", "after")
        return quiet_out(compare.main, ["diags", before, after, "--root", str(self.root), "--jobs", "2"])

    def test_cases(self):
        # The fuzz's seeds (tests/fuzz goes), a package's files as its directory.
        self.assertEqual(compare.cases(self.root),
                         ["tests/a.onsa", "tests/b.onsa", "tests/c.onsa", "tests/d.onsa", "tests/p"])
        with mock.patch.object(fuzz, "seeds", return_value=[("tests/q.onsa", "")]) as seeds:
            self.assertEqual(compare.cases(self.root), ["tests/q.onsa"])
        seeds.assert_called_once_with(self.root)

    def test_diags(self):
        span = {"file": "f", "line": 1, "col": 2, "end_line": 1, "end_col": 3}

        def out(message="m", edits="x", notes=({"message": "opened here", "span": span},)):
            fix = {"title": "t", "edits": [{"span": span, "replace": edits}]}
            d = {"code": "E0001", "message": message, "span": span, "fixes": [fix], "notes": list(notes)}
            return [1, {"diagnostics": [d]}]

        same = {f"tests/{c}": out() for c in ("a.onsa", "b.onsa", "c.onsa", "d.onsa", "p")}
        self.assertEqual(self.diags({"before": same, "after": same}),
                         (0, ["5 cases, 0 differ, 0 fell in one binary only, 0 fell in both"]))
        after = {**same, "tests/b.onsa": out(message="n"), "tests/c.onsa": out(edits="y"), "tests/d.onsa": ["kill", ""],
                 "tests/p": out(notes=[{"message": "opened here"}])}  # the note's place only
        self.assertEqual(self.diags({"before": same, "after": after}), (1, [
            "tests/b.onsa", "  ~ E0001 f:1:2-1:3: message 'm' -> 'n'",
            "tests/c.onsa", "  ~ E0001 f:1:2-1:3: fix edits",
            "tests/d.onsa", "  before: 1 diagnostic(s)", "  after:  signal 9",
            "tests/p", "  ~ E0001 f:1:2-1:3: notes",
            "5 cases, 4 differ, 1 fell in one binary only, 0 fell in both"]))  # fmt: skip
        # A fall on both sides is listed; when every case fell, nothing was compared, which is no pass.
        broken = {"*": [2, "no manifest"]}
        code, lines = self.diags({"before": broken, "after": broken})
        self.assertEqual((code, lines[:3], lines[-1]), (1, [
            "tests/a.onsa", "  before: not JSON (exit 2): no manifest", "  after:  not JSON (exit 2): no manifest"],
            "5 cases, 0 differ, 0 fell in one binary only, 5 fell in both"))  # fmt: skip

    def test_fmt(self):
        # A file at a time (a package's files too), each run in its own directory; the tree is not written. The exit
        # code, the file written (gone is a fall), stdout and the names of the files left are compared.
        before, after = self.fakes({"before": {"*": [0, "x\n"]}, "after": {
            "*": [0, "x\n"], "tests/a.onsa": [0, "x\n", "", "x.tmp"], "tests/b.onsa": [0, "x\ny\n"],
            "tests/c.onsa": [0, "x\n", "hi"], "tests/d.onsa": ["kill", ""], "tests/p/sub/y.onsa": [0, None],
            "tests/p/x.onsa": [1, "x\n"]}}, "before", "after")  # fmt: skip
        run = lambda b, a: quiet_out(compare.main, ["fmt", b, a, "--root", str(self.root), "--jobs", "2"])  # noqa: E731
        self.assertEqual(run(before, before), (0, ["6 cases, 0 differ, 0 fell in one binary only, 0 fell in both"]))
        self.assertEqual(run(before, after), (1, [
            "tests/a.onsa", "  before: exit 0, 2 lines", "  after:  exit 0, 2 lines", "  files: +x.tmp",
            "tests/b.onsa", "  before: exit 0, 2 lines", "  after:  exit 0, 3 lines", "  line 2: '' -> 'y'",
            "tests/c.onsa", "  before: exit 0, 2 lines", "  after:  exit 0, 2 lines", "  stdout line 1: '' -> 'hi'",
            "tests/d.onsa", "  before: exit 0", "  after:  signal 9",
            "tests/p/sub/y.onsa", "  before: exit 0",
            "  after:  exit 0, the file not readable: No such file or directory",
            "tests/p/x.onsa", "  before: exit 0, 2 lines", "  after:  exit 1, 2 lines",
            "6 cases, 6 differ, 2 fell in one binary only, 0 fell in both"]))  # fmt: skip
        self.assertEqual((self.root / "tests/b.onsa").read_text(), "pub fn f() {}\n")
        # No file formatted to exit 0 on both sides is no pass.
        before, after = self.fakes({"before": {"*": [2, "x\n"]}, "after": {"*": [2, "x\n"]}}, "before", "after")
        self.assertEqual(run(before, after), (1, ["6 cases, 0 differ, 0 fell in one binary only, 0 fell in both",
                                                  "fmt: no case ran to exit 0 in both binaries"]))

    def test_core(self):
        # The cases of `diags` but tests/review-phase1 and tests/heavy, then examples (std is not taken); the exit
        # code tells.
        for rel in ("tests/review-phase1/r.onsa", "tests/heavy/h.onsa", "tests/spec/s.onsa", "std/s.onsa", "examples/e/m.onsa",
                    "examples/e/onsa.toml", "examples/f.onsa"):  # fmt: skip
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text("")
        want = ["tests/a.onsa", "tests/b.onsa", "tests/c.onsa", "tests/d.onsa", "tests/p", "tests/spec/s.onsa",
                "examples/e", "examples/f.onsa"]  # fmt: skip
        self.assertEqual(compare.core_cases(self.root), want)
        out = {c: [0, "a\nb\n"] for c in want}
        before, after = self.fakes({"before": out, "after": {**out, "examples/f.onsa": [0, "a\nc\n"]}}, "before", "after")
        argv = ["core", before, after, "--root", str(self.root)]
        self.assertEqual(quiet_out(compare.main, argv), (1, [
            "examples/f.onsa", "  before: exit 0, 3 lines", "  after:  exit 0, 3 lines", "  line 2: 'b' -> 'c'",
            "8 cases, 1 differ, 0 fell in one binary only, 0 fell in both"]))  # fmt: skip
        self.assertEqual(quiet_out(compare.main, ["core", before, before, "--root", str(self.root)])[0], 0)
        # The same output, but no input reached exit 0: nothing of the Core was compared, which is no pass.
        before, after = self.fakes({"before": {"*": [1, "error"]}, "after": {"*": [1, "error"]}}, "before", "after")
        self.assertEqual(quiet_out(compare.main, ["core", before, after, "--root", str(self.root)]), (1, [
            "8 cases, 0 differ, 0 fell in one binary only, 0 fell in both",
            "core: no case ran to exit 0 in both binaries"]))  # fmt: skip
        # No input at all names where the inputs come from.
        (self.root / "empty").mkdir()
        self.assertEqual(quiet_out(compare.main, ["core", before, after, "--root", str(self.root / "empty")]), (1, [
            f"core: no case in tests (but tests/review-phase1) and examples of {self.root / 'empty'}"]))

    def test_cst(self):
        # W5-13 U9b: `dump --cst --tree` of each seed file, tests/review-phase1 too (the syntax only); the exit code and
        # the output tell, and no file to exit 0 in both is no pass.
        (self.root / "tests/review-phase1").mkdir()
        (self.root / "tests/review-phase1/r.onsa").write_text("")
        want = ["tests/a.onsa", "tests/b.onsa", "tests/c.onsa", "tests/d.onsa", "tests/p/sub/y.onsa", "tests/p/x.onsa",
                "tests/review-phase1/r.onsa"]  # fmt: skip
        out = {c: [0, "SourceFile@0..1\n"] for c in want}
        before, after = self.fakes({"before": out, "after": {**out, "tests/p/x.onsa": [0, "SourceFile@0..2\n"]}},
                                   "before", "after")  # fmt: skip
        argv = ["cst", before, after, "--root", str(self.root)]
        self.assertEqual(quiet_out(compare.main, argv), (1, [
            "tests/p/x.onsa", "  before: exit 0, 2 lines", "  after:  exit 0, 2 lines",
            "  line 1: 'SourceFile@0..1' -> 'SourceFile@0..2'",
            "7 cases, 1 differ, 0 fell in one binary only, 0 fell in both"]))  # fmt: skip
        calls = (self.bin / "calls").read_text().splitlines()
        self.assertEqual(sorted(x.split()[-1] for x in calls if x.startswith("before ")), want)
        self.assertTrue(all(x.split()[1:4] == ["dump", "--cst", "--tree"] for x in calls), calls)
        self.assertEqual(quiet_out(compare.main, ["cst", before, before, "--root", str(self.root)])[0], 0)
        before, after = self.fakes({"before": {"*": [1, "x"]}, "after": {"*": [1, "x"]}}, "before", "after")
        self.assertEqual(quiet_out(compare.main, ["cst", before, after, "--root", str(self.root)]), (1, [
            "7 cases, 0 differ, 0 fell in one binary only, 0 fell in both",
            "cst: no case ran to exit 0 in both binaries"]))  # fmt: skip

    def test_c(self):
        # Every target of the inputs of `core` as they are in the HEAD (tests/fuzz and tests/review-phase1 left out),
        # a fragment as a package of its own with the manifest `onsa_cases` lists (W5-13 U9b: here a made-up list);
        # the files written, an archive by its name alone, the out directory and the package named, the output and its
        # codes compared. A file the list does not have is an error.
        listed = [{"path": "tests/a.onsa", "manifest": '[package]\nname = "a"\n[targets.t1]\n[targets.t2]\n'},
                  {"path": "tests/b.onsa", "manifest": None}, {"path": "tests/c.onsa", "manifest": None},
                  {"path": "tests/d.onsa", "manifest": None}]  # fmt: skip
        (self.bin / "cases.json").write_text(json.dumps(listed))
        fake = (sys.executable, "-c", "import sys; sys.stdout.write(open(sys.argv[1]).read())", str(self.bin / "cases.json"))
        self.enterContext(mock.patch.object(compare, "CASES", fake))
        (self.root / "tests/review-phase1").mkdir()
        for rel in ("tests/a.onsa", "tests/fuzz/z.onsa", "tests/review-phase1/r.onsa"):
            (self.root / rel).write_text("// onsa.toml\n// [package]\n// name = \"a\"\n// [targets.t1]\n// [test]\n"
                                         "// mode = \"check\"\n// [targets.t2]\n\npub fn f() {}\n")  # fmt: skip
        (self.root / "tests/b.onsa").write_text("// onsa.toml\n// [test]\n// mode = \"check\"\n\npub fn f() {}\n")
        (self.root / "tests/p/onsa.toml").write_text("[package]\n[targets.host]\n")
        (self.root / "examples/e").mkdir(parents=True)
        (self.root / "examples/e/onsa.toml").write_text("[package]\n[targets.ex]\n")
        (self.root / "examples/e/m.onsa").write_text("pub fn f() {}\n")
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "head")
        (self.root / "tests/a.onsa").write_text("pub fn f() {}\n")  # not in the HEAD
        with tempfile.TemporaryDirectory() as tmp:
            builds = compare.c_builds(self.root, tmp)
            self.assertEqual(list(map(str, builds)), ["tests/a.onsa [t1]", "tests/a.onsa [t2]", "tests/p [host]",
                                                      "examples/e [ex]"])  # fmt: skip
            self.assertEqual(sorted(p.name for p in builds[0].package.iterdir()), ["a.onsa", "onsa.toml"])
            self.assertEqual((builds[0].package / "onsa.toml").read_text(), '[package]\nname = "a"\n[targets.t1]\n'
                                                                           '[targets.t2]\n')  # fmt: skip
        (self.bin / "build.json").write_text(json.dumps({"before": {}, "after": {"t2": [0, "int b;\n"],
                                                                                 "host": [2, ""]}}))  # fmt: skip
        for n in ("before", "after"):
            (self.bin / n).write_text(FAKE_BUILD.format(exe=sys.executable))
            (self.bin / n).chmod(0o755)
        def run(*names):
            return quiet_out(compare.main, ["c", *(str(self.bin / n) for n in names), "--root", str(self.root)])
        (self.bin / "cases.json").write_text(json.dumps(listed[:3]))
        self.assertEqual(run("before", "before"), (1, ["c: tests/d.onsa: not a case that `onsa_cases` lists (a file is "
                                                       "built with the manifest of its fragment)"]))  # fmt: skip
        (self.bin / "cases.json").write_text(json.dumps(listed))
        head = f"c: 4 builds of 3 inputs with targets in the HEAD of {self.root}"
        self.assertEqual(run("before", "before"), (0, [head, "4 cases, 0 differ, 0 fell in one binary only, 0 fell in "
                                                       "both"]))  # fmt: skip
        self.assertEqual(run("before", "after"), (1, [head,
            "tests/a.onsa [t2]", "  before: exit 0, 3 files", "  after:  exit 0, 3 files",
            "  m.c line 1: 'int a;' -> 'int b;'",
            "tests/p [host]", "  before: exit 0, 3 files", "  after:  exit 2, 0 files",
            "  output line 1: 'built host in <out> from <pkg>' -> 'm.onsa:1:2: error[E0200]: m'",
            "  codes: none -> E0200",
            "  files: -m.a -m.c -onsa_build.json",
            "4 cases, 2 differ, 0 fell in one binary only, 0 fell in both"]))  # fmt: skip

    def test_speed_turns_round(self):
        b1, b2 = self.fakes({}, "b1", "b2")
        log = self.bin / "log"

        def runs(*turns, per, chosen=0):  # the names the binaries logged: choosing the inputs of `core`, `check` of
            # each binary on each of `chosen` inputs, then `dump --core` of the first, then `per` runs of a binary in
            # its turn of a round
            want = ["b1", "b2"] * chosen + ["b1"] * chosen + [n for t in turns for n in [t] * per]
            got = log.read_text().split()
            log.unlink()
            return got, want

        unit = "minimum seconds, wall and cpu (user + sys of the children)"
        argv = ["speed", "long", "--rounds", "3", "--long", str(self.root / "tests"), b1, b2]
        code, lines = quiet_out(compare.main, argv)
        self.assertEqual((code, lines[0]), (0, f"4 long inputs, 3 rounds; {unit}"))
        self.assertEqual(*runs("b1", "b2", "b2", "b1", "b1", "b2", per=8))  # `check` and `fmt --check`, shown apart
        self.assertEqual([(x.split()[0], ast.literal_eval(x.split(" ", 1)[1]).keys()) for x in lines[1:3]],
                         [(n, {"check", "check cpu", "fmt", "fmt cpu"}) for n in ("1:b1", "2:b2")])
        # The five grown most in cpu, before -> after in the order of the arguments.
        self.assertEqual(lines[3], "the five grown most in cpu, 1:b1 -> 2:b2: input, command, cpu, wall")
        self.assertEqual(len(lines), 9)
        self.assertRegex(lines[4], r"^\w\.onsa (check|fmt) [\d.]+ -> [\d.]+ [\d.]+ -> [\d.]+$")
        core = "5 for core: 5 of 5 checked to 0 by every binary"
        with mock.patch.object(compare, "ROOT", self.root):  # 7 files `check` and `fmt --check`, 5 inputs `dump --core`
            code, lines = quiet_out(compare.main, ["speed", "all", "--rounds", "2", b1, b2])
            self.assertEqual((code, lines[0]), (0, f"7 files ({core}), 0 long inputs, 2 rounds; {unit}"))
            self.assertEqual(*runs("b1", "b2", "b2", "b1", per=19, chosen=5))
            code, lines = quiet_out(compare.main, argv[:1] + ["all", "--rounds", "2"] + argv[4:])
        self.assertEqual((code, lines[0]), (0, f"7 files ({core}), 4 long inputs, 2 rounds; {unit}"))
        self.assertEqual(*runs("b1", "b2", "b2", "b1", per=19 + 8, chosen=5))
        times = ast.literal_eval(lines[1].split(" ", 1)[1])
        kinds = ("check", "fmt", "core", "long", "long fmt")
        self.assertEqual(list(times), [f"{k}{s}" for k in kinds for s in ("", " cpu")])
        self.assertTrue(all(t > 0 for t in times.values()), times)  # the cpu of the children is counted

    def test_speed_names(self):
        # Two binaries of the same base name are told apart by the path past the directories they share, and the same
        # binary given twice by its place; each is measured on its own.
        for d in ("base/b5ddcf3", "debug"):
            (self.bin / d).mkdir(parents=True)
            (self.bin / d / "spec.json").write_text("{}")
            (self.bin / d / "onsa").write_text(FAKE_DIAGS.format(exe=sys.executable))
            (self.bin / d / "onsa").chmod(0o755)
        before, after = str(self.bin / "base/b5ddcf3/onsa"), str(self.bin / "debug/onsa")
        self.assertEqual(compare.labels([before, after]), ["1:base/b5ddcf3/onsa", "2:debug/onsa"])
        self.assertEqual(compare.labels([after, os.path.relpath(after)]), ["1:onsa", "2:onsa"])
        self.assertEqual(compare.labels([after]), ["1:onsa"])
        with mock.patch.object(compare, "ROOT", self.root):
            code, lines = quiet_out(compare.main, ["speed", "all", "--rounds", "1", after, after])
        self.assertEqual((code, [x.split()[0] for x in lines[1:]]), (0, ["1:onsa", "2:onsa"]))
        self.assertEqual((self.bin / "debug/log").read_text().split(), ["onsa"] * (5 * 2 + 19 * 2))  # one `check`

    def test_speed_core_lowers(self):
        # `core` times the inputs of `compare.py core` every binary checks to exit 0 and the first then lowers (exit
        # 0), chosen once before the rounds, a file a process (X-21 P-4): an input that one binary does not check to 0
        # gets no `dump --core` of any binary, so a binary before a fix does not lower an input the fixed one rejects.
        b1, b2 = self.fakes({"b1": {"check tests/p": [2, "no manifest"], "dump --core tests/a.onsa": [1, "error"]},
                             "b2": {"check tests/b.onsa": [1, {"diagnostics": []}]}}, "b1", "b2")  # fmt: skip
        with mock.patch.object(compare, "ROOT", self.root):
            code, lines = quiet_out(compare.main, ["speed", "all", "--rounds", "1", b1, b2])
        self.assertEqual((code, lines[0].split(";")[0]),
                         (0, "7 files (2 for core: 3 of 5 checked to 0 by every binary), 0 long inputs, 1 rounds"))
        calls = (self.bin / "calls").read_text().splitlines()
        self.assertEqual(calls[:12], [
            "b1 check tests/a.onsa", "b2 check tests/a.onsa", "b1 check tests/b.onsa", "b2 check tests/b.onsa",
            "b1 check tests/c.onsa", "b2 check tests/c.onsa", "b1 check tests/d.onsa", "b2 check tests/d.onsa",
            "b1 check tests/p",
            "b1 dump --core tests/a.onsa", "b1 dump --core tests/c.onsa", "b1 dump --core tests/d.onsa"])  # fmt: skip
        timed = [c.replace(f"{self.root}/", "") for c in calls[12:] if " dump " in c]
        self.assertEqual(timed, [f"{b} dump --core tests/{x}.onsa" for b in ("b1", "b2") for x in "cd"])
        self.assertEqual(len(calls), 12 + 16 * 2)  # a round: 7 files `check` and `fmt --check`, 2 `dump --core`

    def test_probe(self):
        old, new = (self.bin / n for n in ("old", "new"))
        for b in (old, new):
            b.write_text(FAKE_PROBE.format(exe=sys.executable))
            b.chmod(0o755)
        cases, out = self.root / "cases.txt", self.root / "out"
        cases.write_text(CASES)
        probe = lambda *argv: quiet_out(compare.main, ["probe", str(cases), "--out", str(out), *argv])  # noqa: E731
        self.assertEqual(probe(str(old), str(new)), (0, [
            "a: x0", "b:", "   1:old x1 E0302@main.onsa:1:2", "   2:new x1 E0302@main.onsa:1:2 E0302@sub/x.onsa:1:2",
            "c: x0", "d: x1 E0302@main.onsa:1:2", "k: signal 9"]))  # fmt: skip
        written = {p.relative_to(out).as_posix(): p.read_text() for p in out.rglob("*") if p.is_file()}
        self.assertEqual(written, {
            "a/onsa.toml": '[package]\nname = "a"\nedition = "2026"\n', "a/main.onsa": "pub fn f() {}\n",
            "b/onsa.toml": '[package]\nname = "b"\nedition = "2026"\n', "b/main.onsa": "bad\n", "b/sub/x.onsa": "new\n",
            "c/onsa.toml": '[package]\nname = "own"\n', "d/onsa.toml": '[package]\nname = "d"\nedition = "2026"\n',
            "d/main.onsa": "bad\n", "k/onsa.toml": '[package]\nname = "k"\nedition = "2026"\n',
            "k/main.onsa": "kill\n"})  # fmt: skip
        self.assertEqual(probe("--only", "d", "--cmd", "check", str(old), str(new)), (0, [
            "d:  (the same lines; the outputs differ: --full)", "   1:old x1 E0302@main.onsa:1:2",
            "   2:new x1 E0302@main.onsa:1:2"]))  # fmt: skip
        self.assertEqual(probe("--only", "a", "--cmd", "dump --core", str(old), str(new)), (0, ["a: x0 (1 lines)"]))
        self.assertEqual(probe("--only", "d", "--cmd", "check", "--full", str(old), str(new)), (0, [
            "##### d", "[1:old] x1", "main.onsa:1:2: error[E0302]: m", "[2:new] x1",
            "main.onsa:1:2: error[E0302]: m (new)"]))  # fmt: skip
        self.assertEqual(probe("--only", "a", "--full", str(old), str(new)), (0, [
            "##### a", "[all] x0", '{"diagnostics": []}']))  # fmt: skip
        self.assertEqual(probe("--only", "z", str(old)), (1, [f"probe: no case z in {cases}"]))
        for text, why in (("x\n=== a\n", "line 1: before the first `=== <name>`"),
                          ("=== a\n=== a\n", "line 2: 'a' is not a new name of a case"),
                          ("=== ../a\n", "line 1: '../a' is not a new name"),
                          ("=== a\n--- ../x.onsa\n", "line 2: '../x.onsa' is not a new path inside the case"),
                          ("=== a\nx\n--- main.onsa\n", "line 3: 'main.onsa' is not a new path"),
                          ("=== a\n--- /x.onsa\n", "line 2: '/x.onsa' is not a new path"), ("", "no case in")):  # fmt: skip
            with self.subTest(text=text):
                cases.write_text(text)
                code, lines = probe(str(old))
                self.assertEqual(code, 1)
                self.assertIn(why, lines[0])

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in compare.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^compare\.py {name}( |$)")
                code, lines = quiet_out(compare.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(compare.main, ["help", "--role", role])
                want = [n for n, c in compare.COMMANDS.items() if role in c.roles]
                self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        names = list(compare.COMMANDS)
        self.assertEqual(names, ["diags", "fmt", "cst", "core", "c", "speed", "probe"])
        self.assertEqual([x.split()[0] for x in quiet_out(compare.main, ["help"])[1][: len(names)]], names)
        for argv, code in (([], 2), (["--help"], 0)):  # no command is a usage error; `--help` lists the commands
            buf = io.StringIO()
            with self.subTest(argv=argv), mock.patch.object(sys, "stdout", buf), mock.patch.object(sys, "stderr", buf), \
                    self.assertRaises(SystemExit) as e:  # fmt: skip
                compare.main(argv)
            self.assertEqual(e.exception.code, code)
            self.assertIn("{" + ",".join(names + ["help"]) + "}", buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
