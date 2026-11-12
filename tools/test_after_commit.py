#!/usr/bin/env python3
"""Self-tests of tools/after_commit.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_after_commit.py
"""
import io
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import after_commit  # noqa: E402
import bg  # noqa: E402
import gate_runs  # noqa: E402
import work  # noqa: E402
from selftest_support import quiet_out, git_in, NOTHING  # noqa: E402


START_RUNNER = after_commit.start_runner  # the real one, for `AutoSweep.test_now`


# The gate of the made-up tree of `AutoSweep`: logs HEAD, writes a line of a sweep, exits with
# `target/gate-code`; with `target/meanwhile`, commits and calls `on_commit` while it runs. With
# `--save-base`, logs HEAD in `target/base-log` alone and exits with `target/base-code`.
FAKE_GATE = """\
import os, subprocess, sys
sys.path.insert(0, os.environ["AUTO_TOOLS"])
import gate_runs
root = os.getcwd()
def git(*a):
    return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false", *a],
                          cwd=root, capture_output=True, text=True, check=True).stdout
with open("target/base-log" if "--save-base" in sys.argv else "target/gate-log", "a") as f:
    f.write(git("rev-parse", "HEAD").strip() + "\\n")
if "--save-base" in sys.argv:
    sys.exit(int(open("target/base-code").read()) if os.path.exists("target/base-code") else 0)
if os.path.exists("target/meanwhile"):
    os.remove("target/meanwhile")
    open("crates/m.rs", "a").write("x\\n")
    git("add", "-A")
    git("commit", "-qm", "meanwhile")
    import after_commit
    after_commit.on_commit(root)
code = int(open("target/gate-code").read()) if os.path.exists("target/gate-code") else 0
shard = gate_runs.next_shard(gate_runs.read_history(root)[0], 2)
verdict = "FAIL" if code else "PASS"
gate_runs.record(root, f"sweep {shard}/2", [], {"fuzz": [verdict, 0.1]}, verdict, 0.1)
sys.exit(code)
"""


class AutoSweep(unittest.TestCase):
    """tools/after_commit.py (X-1 U4, U13): the request after a commit (`on_commit`, `work.py commit`), the
    runner, the hold, `--now` and the line `auto sweep:`, in a made-up main tree whose `tools/gate.sh` is
    FAKE_GATE. The runner runs in this process (`drive`) with short waits; starting one (`start_runner`) is
    recorded, except in `test_now`."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve() / "main"
        for rel, text in {".gitignore": "target/\n", "crates/c.rs": "fn c() {}\n", "docs/d.md": "d\n",
                          "tests/t.onsa": "t\n", "tools/fake_gate.py": FAKE_GATE,
                          "tools/gate.sh": '#!/bin/sh\nexec "$PYTHON" -B tools/fake_gate.py "$@"\n'}.items():  # fmt: skip
            self.write(rel, text)
        (self.root / "tools/gate.sh").chmod(0o755)
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        (self.root / "target").mkdir()
        self.started = []
        for name, value in (("QUIET", 0.3), ("NAP", 0.05), ("CLEAN_POLL", 0.05), ("CLEAN_WAIT", 0.3),
                            ("start_runner", self.started.append)):  # fmt: skip
            p = mock.patch.object(after_commit, name, value)
            p.start()
            self.addCleanup(p.stop)
        env = mock.patch.dict(os.environ, {"AUTO_TOOLS": str(Path(after_commit.__file__).parent),
                                           "PYTHON": sys.executable})  # fmt: skip
        env.start()
        self.addCleanup(env.stop)

    def write(self, rel, text="x\n"):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def commit(self, rel, text="x\n", root=None):
        p = (root or self.root) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        git_in(root or self.root, "add", "-A")
        git_in(root or self.root, "commit", "-qm", rel)

    def hook(self, *args, root=None):
        """`after_commit.py <args>`, or with none what a commit runs (`on_commit`): (the exit, stdout)."""
        if not args:
            return 0, after_commit.on_commit(root or self.root) + "\n"
        with mock.patch.object(sys, "stdout", io.StringIO()) as out, mock.patch.object(sys, "stderr", io.StringIO()):
            code = after_commit.main(["--root", str(root or self.root), *args])
        return code, out.getvalue()

    def head(self, back=0):
        return git_in(self.root, "rev-parse", f"HEAD~{back}").strip()

    def request(self):
        return gate_runs.read_json(self.root, "request")

    def gate_log(self, name="gate-log"):
        p = self.root / "target" / name
        return p.read_text().split() if p.exists() else []

    def line(self):
        return gate_runs.auto_line(self.root, gate_runs.read_history(self.root)[0], 2)

    def test_on_commit(self):
        self.commit("docs/e.md")  # documents only: nothing
        self.assertEqual(self.hook(), (0, f"{NOTHING}\n"))
        self.assertIsNone(self.request())
        self.assertEqual(self.line(), "auto sweep: no sweep yet")
        self.assertFalse((self.root / gate_runs.AUTO).exists())
        for rel in ("crates/c.rs", "tests/u.onsa", "rust-toolchain.toml"):
            self.commit(rel)
            self.assertEqual(self.hook(), (0, "auto sweep: requested; the runner starts\n"))
            self.assertEqual(self.request()["commit"], self.head())
        self.assertEqual(self.started, [self.root] * 3)
        self.assertRegex(self.line(), rf"^auto sweep: requested at {self.head()[:7]} .*, no runner \(")
        # a worktree: nothing, in it nor in the main tree
        wt = self.root.parent / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        before = self.request()
        self.commit("crates/w.rs", root=wt)
        self.assertEqual(self.hook(root=wt), (0, "auto sweep: nothing (not the main tree; the sweep is the parent's)\n"))
        self.assertEqual(self.hook("--now", root=wt)[0], 2)
        self.assertEqual((self.request(), len(self.started)), (before, 3))
        self.assertFalse((wt / gate_runs.AUTO).exists())

    def test_the_environment_of_git(self):
        """A git's GIT_* go: with them, the git of the tool would read another tree or index."""
        self.commit("crates/e.rs")
        seen = []
        env = {"GIT_DIR": str(self.root.parent / "nowhere"), "GIT_INDEX_FILE": ".git/index", "GIT_PREFIX": "sub/"}
        with mock.patch.dict(os.environ, env), \
                mock.patch.object(after_commit, "start_runner", lambda root: seen.append([k for k in os.environ if k.startswith("GIT_")])):  # fmt: skip
            self.assertEqual(self.hook("--now")[0], 0)
        self.assertEqual((seen, self.request()["commit"]), ([[]], self.head()))

    def test_commits_in_a_row_run_once(self):
        for i in range(3):
            self.commit(f"crates/{i}.rs")
            self.hook()
        self.assertEqual(after_commit.drive(self.root), 0)
        self.assertEqual(self.gate_log(), [self.head()])
        self.assertIsNone(self.request())
        self.assertEqual(self.line(), f"auto sweep: last PASS at {self.head()[:7]} (0 commits ago)")
        self.assertEqual(len(list((self.root / gate_runs.AUTO / "runs").glob(f"*-{self.head()[:7]}.out"))), 1)

    def test_a_commit_while_it_runs_runs_again(self):
        self.write("target/meanwhile")
        self.commit("crates/x.rs")
        self.hook()
        first = self.head()
        after_commit.drive(self.root)
        self.assertEqual(self.gate_log(), [first, self.head()])
        self.assertNotEqual(first, self.head())
        self.assertEqual(len(self.started), 1)  # the commit meanwhile found the runner on
        self.assertIsNone(self.request())

    def test_the_hold(self):
        (self.root / gate_runs.HOLD).parent.mkdir(parents=True)
        (self.root / gate_runs.HOLD).touch()
        self.commit("crates/x.rs")
        self.assertEqual(self.hook(), (0, "auto sweep: requested; held\n"))
        self.assertEqual(self.started, [])
        self.assertRegex(self.line(), rf"^auto sweep: held since .*, request at {self.head()[:7]} \(remove ")
        after_commit.drive(self.root)
        self.assertEqual((self.gate_log(), gate_runs.read_json(self.root, "state")["state"]), ([], "held"))
        self.assertEqual(self.hook("--now")[0], 1)
        (self.root / gate_runs.HOLD).unlink()
        self.assertEqual(self.hook("--now")[0], 0)
        self.assertEqual((len(self.started), self.request()["now"]), (1, True))

    def test_a_dirty_tree_waits_then_skips(self):
        self.commit("crates/x.rs")
        self.hook()
        self.write("crates/c.rs", "changed\n")
        t0 = time.monotonic()
        after_commit.drive(self.root)
        self.assertGreaterEqual(time.monotonic() - t0, after_commit.CLEAN_WAIT)
        self.assertEqual(self.gate_log(), [])
        self.assertEqual(self.line(), f"auto sweep: skipped at {self.head()[:7]}: uncommitted crates/c.rs "
                                      f"(tools/after_commit.py --now); no sweep yet")  # fmt: skip
        git_in(self.root, "checkout", "--", "crates/c.rs")
        self.write("docs/new.md")  # not the code: clean enough
        self.hook("--now")
        with mock.patch.object(after_commit, "QUIET", 1000):  # `--now` does not wait for the quiet
            after_commit.drive(self.root)
        self.assertEqual(self.gate_log(), [self.head()])

    def test_now(self):
        """`--now` with no request asks for HEAD; the runner it starts (bg.py) runs the sweep."""
        with mock.patch.object(after_commit, "start_runner", START_RUNNER):
            code, out = self.hook("--now")
        self.assertEqual(code, 0, out)
        self.assertIn("auto sweep: requested; the runner starts", out)
        job = self.root / gate_runs.AUTO / "job"
        with mock.patch.object(sys, "stdout", io.StringIO()):
            self.assertEqual(bg.wait(job, 60, 0), 0, (job / "out").read_text())
        self.assertEqual(self.gate_log(), [self.head()])
        self.assertIsNone(self.request())
        self.assertIn("nice -n 10", (job / "cmd").read_text())

    def test_after_the_runner_died(self):
        self.commit("crates/x.rs")
        self.hook()
        script = "import fcntl, sys, time\nf = open(sys.argv[1], 'a')\nfcntl.flock(f, fcntl.LOCK_EX)\nprint('on', flush=True)\ntime.sleep(60)\n"
        child = subprocess.Popen([sys.executable, "-B", "-c", script, str(self.root / gate_runs.AUTO / "lock")],
                                 stdout=subprocess.PIPE, text=True)  # fmt: skip
        self.addCleanup(child.wait)
        self.addCleanup(child.kill)
        self.addCleanup(child.stdout.close)
        self.assertEqual(child.stdout.readline(), "on\n")
        self.assertEqual(self.line(), "auto sweep: the runner is on; no sweep yet")
        self.assertEqual(self.hook(), (0, "auto sweep: requested; the runner is on\n"))
        self.assertEqual(len(self.started), 1)
        child.kill()  # SIGKILL: no crash report
        child.wait()
        self.assertRegex(self.line(), r"^auto sweep: requested at \w{7} .*, no runner \(target/gate/auto/job/out; ")
        self.commit("crates/y.rs")
        self.hook()
        self.assertEqual(len(self.started), 2)

    def test_a_whole_run_does_the_request(self):
        self.commit("crates/x.rs")
        self.hook()
        time.sleep(1.1)  # the history keeps the time in seconds
        gate_runs.record(self.root, "whole", [], {}, "PASS", 1.0, "t")
        after_commit.drive(self.root)
        self.assertEqual((self.gate_log(), self.request()), ([], None))

    def test_the_line(self):
        h = self.head()
        with gate_runs.request_lock(self.root):
            lock = gate_runs.try_runner(self.root)
        for state, part in (({"state": "waiting", "until": 0}, "auto sweep: waiting (quiet until "),
                            ({"state": "waiting-clean", "path": "crates/c.rs", "until": 0},
                             "auto sweep: waiting for a clean tree (uncommitted crates/c.rs, until "),
                            ({"state": "running", "commit": h}, f"auto sweep: running at {h[:7]} since ")):  # fmt: skip
            gate_runs.write_json(self.root, "state", {"time": time.time(), **state})
            self.assertTrue(self.line().startswith(part), self.line())
        lock.close()
        gate_runs.write_json(self.root, "state", {"time": time.time(), "state": "done", "commit": h, "code": 2, "out": "o"})
        self.assertEqual(self.line(), f"auto sweep: gate exit 2 at {h[:7]} (o); no sweep yet")
        # a failure stays until its shard passes
        gate_runs.record(self.root, "sweep 0/2", [], {"fuzz": ["FAIL", 1.0], "a": ["PASS", 1.0]}, "FAIL", 1.0)
        gate_runs.record(self.root, "sweep 1/2", [], {"fuzz": ["PASS", 1.0]}, "PASS", 1.0)
        self.assertTrue(self.line().endswith(f"FAILED at {h[:7]}: fuzz (no output kept)"), self.line())
        self.write(f"target/gate/auto/runs/20261018-000000-{h[:7]}.out")
        self.assertTrue(self.line().endswith(f"(target/gate/auto/runs/20261018-000000-{h[:7]}.out)".replace(
            "target", str(self.root / "target"), 1)), self.line())  # fmt: skip
        gate_runs.record(self.root, "sweep 0/2", [], {"fuzz": ["PASS", 1.0]}, "PASS", 1.0)
        self.assertTrue(self.line().endswith(f"last PASS at {h[:7]} (0 commits ago)"), self.line())

    def test_work_commit(self):
        """X-1 U13: `work.py commit` asks for the sweep after a commit of the code or the cases; with `--no-sweep`, for
        the base alone after one of the code, else nothing; a sweep asked for and not run yet stays one."""
        def commit(rel, *flags):
            self.write(rel)
            return quiet_out(work.main, ["commit", "-m", rel, rel, "--tree", str(self.root), *flags])[1][-1]

        base = "auto sweep: left out (--no-sweep); the base requested; the runner starts"
        same = "auto sweep: left out (--no-sweep); no change of the code, no base to save"
        for rel, flags, line, sweep in (("docs/a.md", (), NOTHING, None), ("docs/b.md", ("--no-sweep",), same, None),
                                        ("tests/a.onsa", ("--no-sweep",), same, None),
                                        ("crates/a.rs", ("--no-sweep",), base, False),
                                        ("tools/a.py", ("--no-sweep",), base, False),
                                        ("tests/b.onsa", (), "auto sweep: requested; the runner starts", True),
                                        ("crates/b.rs", ("--no-sweep",), base.replace(
                                            "requested", "requested (with the sweep asked for before)"), True),
                                        ("docs/c.md", ("--no-sweep",), same, True)):  # fmt: skip
            with self.subTest(rel=rel, flags=flags):
                self.assertEqual(commit(rel, *flags), line)
                self.assertEqual(self.request() and self.request()["sweep"], sweep)
        self.assertEqual(self.started, [self.root] * 4)
        after_commit.drive(self.root)  # the sweep saves the base too
        self.assertEqual((self.gate_log(), self.gate_log("base-log"), self.request()), ([self.head()], [], None))

    def test_the_base_alone(self):
        """X-1 U13: a request of the base alone runs `gate.sh --save-base` (not the sweep); a request after the run
        of a sweep began stays of the base; a failure shows in the line."""
        self.commit("crates/x.rs")
        self.assertEqual(after_commit.request(self.root, sweep=False), "requested; the runner starts")
        first = self.head()
        self.write("target/base-code", "1\n")
        after_commit.drive(self.root)
        self.assertEqual((self.gate_log(), self.gate_log("base-log"), self.request()), ([], [first], None))
        out = gate_runs.read_json(self.root, "state")["out"]
        self.assertTrue(out.endswith(f"-{first[:7]}-base.out"), out)
        self.assertEqual(self.line(), f"auto sweep: save-base exit 1 at {first[:7]} ({out}); no sweep yet")
        self.commit("crates/y.rs")
        after_commit.request(self.root)
        gate_runs.write_json(self.root, "request", {**self.request(), "taken": True})  # its run began
        after_commit.request(self.root, sweep=False)
        self.assertFalse(self.request()["sweep"])
        with gate_runs.request_lock(self.root):
            lock = gate_runs.try_runner(self.root)
        state = {"time": time.time(), "state": "running", "commit": first, "sweep": False}
        gate_runs.write_json(self.root, "state", state)
        self.assertTrue(self.line().startswith(f"auto sweep: saving the base at {first[:7]} since "), self.line())
        lock.close()

    def wait(self, *args):
        """`after_commit.py --wait <args>`: (the exit, its lines, the seconds it took)."""
        t0 = time.monotonic()
        code, out = self.hook("--wait", *args)
        return code, out.splitlines(), time.monotonic() - t0

    def test_wait(self):
        """`--wait` (the cases (a)–(g) of the work W5-13): the sweep of the last commit of the code or the cases."""
        for name, value in (("POLL", 0.05), ("START_GRACE", 0.5)):
            p = mock.patch.object(after_commit, name, value)
            p.start()
            self.addCleanup(p.stop)
        # (c) while the runner waits and runs, it waits; it returns after `done`
        self.commit("crates/x.rs")
        self.hook()
        runner = threading.Thread(target=after_commit.drive, args=(self.root,))
        runner.start()
        code, lines, took = self.wait()
        runner.join()
        self.assertEqual((code, lines), (0, [f"auto sweep: last PASS at {self.head()[:7]} (0 commits ago)"]))
        self.assertGreaterEqual(took, after_commit.QUIET)
        self.assertEqual(self.gate_log(), [self.head()])
        # (a) done: at once; (b) a commit of the documents after it does not move what it waits for
        self.assertEqual(self.wait()[0], 0)
        self.commit("docs/e.md")
        self.hook()
        code, lines, took = self.wait()
        self.assertEqual((code, lines[0].endswith("(1 commit ago)"), took < 0.5), (0, True, True))
        # (e) a sweep that fails: 1, the line points to its output
        self.write("target/gate-code", "1\n")
        self.commit("crates/y.rs")
        self.hook()
        after_commit.drive(self.root)
        code, lines, _ = self.wait()
        self.assertEqual(code, 1)
        self.assertRegex(lines[0], rf"FAILED at {self.head()[:7]}: fuzz \(.*-{self.head()[:7]}\.out\)$")
        (self.root / "target/gate-code").unlink()
        # (g) the runner leaves the request to a whole run of the same HEAD and writes no state: the state is old
        self.commit("crates/z.rs")
        self.hook()
        time.sleep(1.1)  # the history keeps the time in seconds
        gate_runs.record(self.root, "whole", [], {}, "PASS", 1.0, "t")
        after_commit.drive(self.root)
        self.assertEqual((self.request(), gate_runs.read_json(self.root, "state")["commit"]), (None, self.head(1)))
        self.assertEqual(self.wait()[0], 0)
        # (d) the hold: 3
        (self.root / gate_runs.HOLD).touch()
        self.commit("tests/h.onsa")
        self.hook()
        self.assertEqual(self.wait()[:2], (3, [self.line(), "after_commit: --wait: target/gate/hold is there"]))
        after_commit.drive(self.root)  # held: the request stays
        self.assertEqual(self.wait()[0], 3)
        (self.root / gate_runs.HOLD).unlink()
        # (f) a request whose runner does not come: it waits START_GRACE, up to --max
        code, lines, took = self.wait("--max", "0.2")
        self.assertEqual((code, lines[-1], took >= 0.2), (3, "after_commit: --wait: not done after 0.2 s", True))
        self.assertEqual(self.wait()[1][-1], "after_commit: --wait: requested, no runner")
        # skipped
        self.write("crates/c.rs", "changed\n")
        after_commit.drive(self.root)
        self.assertEqual(self.wait()[1][-1], "after_commit: --wait: skipped: uncommitted crates/c.rs")
        git_in(self.root, "checkout", "--", "crates/c.rs")
        after_commit.drive(self.root)  # the request left runs
        self.assertEqual((self.wait()[0], self.request()), (0, None))
        # --no-sweep: no sweep asked for
        self.commit("crates/n.rs")
        after_commit.on_commit(self.root, sweep=False)
        after_commit.drive(self.root)
        self.assertEqual(self.gate_log("base-log"), [self.head()])
        self.assertEqual(self.wait()[:2], (3, [self.line(), f"after_commit: --wait: no sweep at {self.head()[:7]} "
                                                    "or after, none asked for (--no-sweep, held, or skipped?)"]))  # fmt: skip
        with mock.patch.object(after_commit.narrowing, "git", side_effect=after_commit.narrowing.NarrowError("git log: x")):
            self.assertEqual(self.wait()[:2], (3, []))  # not 1: no sweep failed
        # the usage: with --now or --drive, --max alone, a worktree
        for args in (("--wait", "--now"), ("--wait", "--drive"), ("--now", "--max", "5")):
            with self.subTest(args=args), self.assertRaises(SystemExit) as e:
                self.hook(*args)
            self.assertEqual(e.exception.code, 2)
        wt = self.root.parent / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        self.assertEqual(self.hook("--wait", root=wt)[0], 2)

    def test_the_help(self):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.dict(os.environ), self.assertRaises(SystemExit):
            after_commit.main(["--help"])
        text = " ".join(out.getvalue().split())
        for part in ("tools/work.py commit calls it; by hand, use --now.", "--now run the sweep of HEAD now",
                     "--drive be the runner (a commit starts it; not by hand)", "--root ROOT the main tree",
                     "after a restart of the machine", "stop it: touch target/gate/hold",
                     "requested at …, no runner", "example: python3 -B tools/after_commit.py --now",
                     "commits start it: tools/work.py commit (the main tree; --no-sweep: the base binaries alone)",
                     "save-base exit N at <commit> the base binaries were not saved",
                     "right after --now it says so too", "the inputs the fuzzing made small, in target/fuzz/new/",
                     "until the class is in tests/fuzz/allowed.toml or in an R", "it can take 2 sweeps",
                     "--wait wait for the sweep of the last commit", "--max S with --wait", "default 3600 s) for the sweep",
                     "later commits of the documents alone do not move it", "Exit 0: it passed; 1: it failed",
                     "3: it does not come", "example: python3 -B tools/after_commit.py --now "
                     "python3 -B tools/after_commit.py --wait --max 1800"):  # fmt: skip
            self.assertIn(part, text)


if __name__ == "__main__":
    unittest.main(verbosity=1)
