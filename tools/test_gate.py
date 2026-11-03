#!/usr/bin/env python3
"""Self-tests of tools/gate.py: `gate.main` and `--golden` (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_gate.py
"""
import io
import json
import os
import re
import shutil
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
import fuzz  # noqa: E402
import gap_marks  # noqa: E402
import gate  # noqa: E402
import gate_runs  # noqa: E402
import gate_steps  # noqa: E402
import narrowing  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
from selftest_support import entry, quiet, quiet_out, Repo, TempRepo, git_in  # noqa: E402


def fake(name, code=0, **kw):
    """A gate item that records its argv in `<cwd>/argv-<name>` and exits with `code`."""
    script = (
        "import sys, pathlib; "
        f"pathlib.Path('argv-{name}').write_text('\\n'.join(sys.argv[1:])); "
        f"sys.exit({code})"
    )
    return gate_steps.Step(name, (sys.executable, "-B", "-c", script), **kw)


class GateRun(TempRepo):
    """Runs `gate.main` on the made-up root."""

    def run_main(self, argv, steps, env=None):
        out = io.StringIO()
        with mock.patch.dict(os.environ, env or {}, clear=False):
            if env is None:
                os.environ.pop("UPDATE_GOLDEN", None)
            old_err, sys.stderr = sys.stderr, io.StringIO()
            try:
                code = gate.main(argv, steps=steps, root=self.repo.root, out=out)
            finally:
                sys.stderr = old_err
        return code, out.getvalue()

    def argv_of(self, name):
        return (self.repo.root / f"argv-{name}").read_text().split("\n")


class GateWiring(GateRun):

    def test_exit_codes(self):
        self.assertEqual(self.run_main([], [fake("a"), fake("b")])[0], 0)
        self.assertEqual(self.run_main([], [fake("a"), fake("b", 1)])[0], 1)
        self.assertEqual(self.run_main(["--stage-end", "W4"], [fake("a")])[0], 2)
        self.assertEqual(self.run_main(["--stage-end", ""], [fake("a")])[0], 2)

    def test_runs_every_item_after_a_failure(self):
        code, out = self.run_main([], [fake("a", 1), fake("b")])
        self.assertEqual(code, 1)
        self.assertTrue((self.repo.root / "argv-b").exists())
        self.assertIn("gate: FAIL (a)", out)

    def test_stage_end_and_gate_steps_are_passed(self):
        steps = [fake("p", stage_args=True, gate_steps=True), fake("q"), fake("c-x", 0, pendable=True)]
        self.assertEqual(self.run_main(["--stage-end", "W3"], steps)[0], 0)
        self.assertEqual(self.argv_of("p"), ["--gate-steps", "c-x", "--stage-end", "W3"])
        self.assertEqual(self.argv_of("q"), [""])
        self.run_main([], steps)
        self.assertEqual(self.argv_of("p"), ["--gate-steps", "c-x"])

    def test_pending_items(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-x", until="W5-07") + entry("gate", "fmt", until="W5-07"))
        code, out = self.run_main(["--work", "W5-07"], [fake("c-x", 1, pendable=True), fake("fmt", 1)])
        self.assertEqual(code, 1)  # `fmt` is not pendable: listing it does not hide its failure
        self.assertIn("PENDING c-x", out)
        self.assertIn("FAIL    fmt", out)
        code, out = self.run_main(["--work", "W5-07"], [fake("c-x", 0, pendable=True)])
        self.assertEqual(code, 1)
        self.assertIn("remove the entry", out)
        # an item that cannot run (exit 2) is not pending (W1-06)
        code, out = self.run_main(["--work", "W5-07"], [fake("c-x", 2, pendable=True)])
        self.assertEqual(code, 1)
        self.assertIn("FAIL    c-x", out)
        self.assertIn("the item cannot run", out)

    def test_items_listed_whole_run_for_their_work_or_a_stage_end(self):
        self.repo.write("tests/pending.toml", entry("gate", "c-x", until="W3-07"))
        steps = [fake("c-x", 0, pendable=True), fake("c-y", 1, pendable=True)]
        ran = self.repo.root / "argv-c-x"
        code, out = self.run_main([], steps)
        self.assertEqual(code, 1)  # an item not listed runs and fails as it is
        self.assertFalse(ran.exists())
        self.assertIn("SKIPPED c-x", out)
        self.assertIn("listed until W3-07: runs with --work W3-07 or --stage-end", out)
        self.run_main(["--work", "W3-08"], steps)
        self.assertFalse(ran.exists())
        code, out = self.run_main(["--work", "W3-08", "--work", "W3-07"], steps)
        self.assertTrue(ran.exists())
        self.assertIn("remove the entry", out)  # it passes: the work fixed it
        ran.unlink()
        self.run_main(["--stage-end", "W3"], steps)
        self.assertTrue(ran.exists())
        # an entry of one case does not skip the item
        self.repo.write("tests/pending.toml", entry("gate", "c-x/a", until="W3-07"))
        ran.unlink()
        self.run_main([], steps)
        self.assertTrue(ran.exists())

    def test_unknown_work_is_a_usage_error(self):
        code, _ = self.run_main(["--work", "W9-99"], [fake("a")])
        self.assertEqual(code, 2)
        self.assertFalse((self.repo.root / "argv-a").exists())

    def test_stage_end_only(self):
        steps = [fake("a"), fake("deep", 0, stage_end_only=True)]
        code, out = self.run_main([], steps)
        self.assertEqual(code, 0)
        self.assertFalse((self.repo.root / "argv-deep").exists())
        self.assertIn("runs only with --stage-end", out)
        self.run_main(["--work", "W3-07"], steps)
        self.assertFalse((self.repo.root / "argv-deep").exists())
        self.run_main(["--stage-end", "W3"], steps)
        self.assertTrue((self.repo.root / "argv-deep").exists())

    def test_quick(self):
        steps = [fake("a"), fake("slow", 1, slow=True)]
        code, out = self.run_main(["--quick"], steps)
        self.assertEqual(code, 0)
        self.assertFalse((self.repo.root / "argv-slow").exists())
        self.assertIn("SKIPPED slow", out)
        self.assertIn("left out by --quick", out)
        self.assertEqual(out.splitlines()[-1], "gate (quick): PASS")  # not the verdict `gate: PASS`
        code, out = self.run_main([], steps)
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines()[-1], "gate: FAIL (slow)")
        steps = [fake("bad", 1), fake("slow", 0, slow=True)]
        self.assertEqual(self.run_main(["--quick"], steps)[1].splitlines()[-1], "gate (quick): FAIL (bad)")
        # it leaves items out, so it does not decide a work or a stage
        self.assertEqual(self.run_main(["--quick", "--stage-end", "W3"], steps)[0], 2)
        self.assertEqual(self.run_main(["--quick", "--work", "W3-07"], steps)[0], 2)

    def test_one_gate_at_a_time(self):
        # a gate that finds the lock taken says so and waits for it
        path = gate.lock_path(self.repo.root)
        self.assertEqual(path, self.repo.root / ".onsa-gate.lock")  # not a git repository
        out = io.StringIO()
        result = {}
        with open(path, "a+") as held:
            gate.fcntl.flock(held, gate.fcntl.LOCK_EX)
            held.write("pid 1 in elsewhere since 00:00:00\n")
            held.flush()
            other = threading.Thread(
                target=lambda: result.setdefault("code", gate.main([], steps=[fake("a")], root=self.repo.root, out=out))
            )
            other.start()
            deadline = time.monotonic() + 10
            while "waiting" not in out.getvalue() and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertIn("another gate runs (pid 1 in elsewhere since 00:00:00); waiting", out.getvalue())
            self.assertFalse((self.repo.root / "argv-a").exists())
        other.join(10)
        self.assertFalse(other.is_alive())
        self.assertEqual(result["code"], 0)
        self.assertTrue((self.repo.root / "argv-a").exists())
        self.assertIn(f"pid {os.getpid()} in ", path.read_text())

    def test_the_lock_is_shared_with_the_worktrees(self):
        root = self.repo.root
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        common = root / ".git"
        self.assertEqual(gate.lock_path(root).resolve(), (common / gate.LOCK).resolve())
        # a directory inside the tree is not its top: a made-up root there keeps its own lock
        self.assertEqual(gate.lock_path(root / "tests"), root / "tests" / ".onsa-gate.lock")
        git = ["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run([*git, "commit", "-q", "--allow-empty", "-m", "a"], cwd=root, check=True)
        tree = Path(self.tmp.name + "-wt")
        subprocess.run(["git", "worktree", "add", "-q", str(tree)], cwd=root, check=True)
        try:
            self.assertEqual(gate.lock_path(tree).resolve(), (common / gate.LOCK).resolve())
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", str(tree)], cwd=root, check=True)

    def test_update_golden_is_refused(self):
        code, _ = self.run_main([], [fake("a")], env={"UPDATE_GOLDEN": "1"})
        self.assertEqual(code, 2)
        self.assertFalse((self.repo.root / "argv-a").exists())

    def test_golden_listing_failure_fails(self):
        # the made-up root is not a git repository
        golden = gate_steps.Step("golden", (sys.executable, "-B", str(gate.TOOLS / "gate.py"), "--golden"), info=True)
        code, out = self.run_main([], [fake("a"), golden])
        self.assertEqual(code, 1)
        self.assertIn("gate: FAIL (golden)", out)
        self.assertIn("golden: cannot list", out)

    def test_results(self):
        listed = {
            "pend-fail": pending.Entry(0, "gate", "pend-fail", ("S-45",), "W3-07", "n"),
            "pend-pass": pending.Entry(1, "gate", "pend-pass", ("S-45",), "W3-07", "n"),
            "not-pendable": pending.Entry(2, "gate", "not-pendable", ("S-45",), "W3-07", "n"),
        }
        steps = [
            fake("ok", 0),
            fake("bad", 1),
            fake("pend-fail", 1, pendable=True),
            fake("pend-pass", 0, pendable=True),
            fake("not-pendable", 1),
            fake("show", 0, info=True),
            fake("show-broken", 1, info=True),
        ]
        results = gate.run_steps(steps, listed, cwd=self.repo.root, out=io.StringIO(), works=("W3-07",))
        self.assertEqual(
            {r.step.name: r.status for r in results},
            {
                "ok": "PASS",
                "bad": "FAIL",
                "pend-fail": "PENDING",
                "pend-pass": "FAIL",
                "not-pendable": "FAIL",
                "show": "INFO",
                "show-broken": "FAIL",
            },
        )
        # without their work, the items listed whole do not run
        results = gate.run_steps(steps, listed, cwd=self.repo.root, out=io.StringIO())
        statuses = {r.step.name: r.status for r in results}
        self.assertEqual((statuses["pend-fail"], statuses["pend-pass"]), ("SKIPPED", "SKIPPED"))
        self.assertEqual(statuses["not-pendable"], "FAIL")
        self.assertFalse(any(r.failed for r in results if r.status == "SKIPPED"))

    def test_summary(self):
        results = gate.run_steps([fake("ok"), fake("bad", 2)], {}, cwd=self.repo.root, out=io.StringIO())
        lines = gate.summary(results, [], ["M tests/golden/c/a.c"], ())
        self.assertEqual(lines[-1], "gate: FAIL (bad)")
        self.assertIn("    M tests/golden/c/a.c", lines)
        self.assertIn("  pending: none", lines)


def sleeper(name, seconds, **kw):
    """A gate item that sleeps for `seconds` and passes."""
    return gate_steps.Step(name, (sys.executable, "-B", "-c", f"import time; time.sleep({seconds})"), **kw)


class GateForms(GateRun):
    """The forms of a run (X-1 U2): the work check, `--only`, the sweep, the history, the warning."""

    def setUp(self):
        super().setUp()
        self.root = self.repo.root.resolve()  # git names /private/var
        self.repo.root = self.root
        self.repo.write(".gitignore", "target/\nargv-*\n")
        git_in(self.root, "init", "-q")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        self.saved = []  # a whole run saves the base (X-1 U4): no cargo here
        saving = mock.patch.object(gate_runs, "save_base", lambda root, keep, **kw: self.saved.append(root) or 0)
        saving.start()
        self.addCleanup(saving.stop)

    def ran(self, name):
        return (self.root / f"argv-{name}").exists()

    def forget(self):
        for p in self.root.glob("argv-*"):
            p.unlink()

    def history(self, root=None):
        return gate_runs.read_history(root or self.root)[0]

    def elsewhere(self):
        """A directory outside the made-up root, removed after the test."""
        other = tempfile.TemporaryDirectory()
        self.addCleanup(other.cleanup)
        return Path(other.name).resolve()

    def worktree(self):
        wt = self.elsewhere() / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        return wt

    def test_a_unit_of_an_item_of_x(self):
        """`--work X-3/U1` (X-1 U3): the work check of a unit; no `until` names it; a typo stops."""
        self.repo.write_id("X-3", "DOING")
        self.repo.write("tests/pending.toml", entry("gate", "c-x", until="W3-07"))
        steps = [fake("fz", narrows=("tools/fuzz.py",)), fake("c-x", 0, pendable=True)]
        code, out = self.run_main(["--work", "X-3/U1c-1"], steps)
        self.assertEqual(code, 0, out)
        self.assertEqual(self.argv_of("fz")[-2:], ["--salt", "X-3/U1c-1"])
        self.assertIn("SKIPPED c-x", out)
        self.assertEqual(self.history()[-1]["form"], "work X-3/U1c-1")
        for bad in ("X-99/U1", "X-3", "X-3/1", "X-3/U", "W9-99"):
            with self.subTest(bad=bad), mock.patch.object(sys, "stderr", io.StringIO()) as err:
                self.forget()
                self.assertEqual(gate.main(["--work", bad], steps=steps, root=self.root, out=io.StringIO()), 2)
                self.assertEqual(list(self.root.glob("argv-*")), [])
                self.assertIn("or a unit of an item of issues/X/ (X-3/U1); unknown: " + bad, err.getvalue())

    def test_the_tree_of_a_run(self):
        """A run keeps the tree its items read (X-1 U3): the whole of a worktree, `SWEPT` of the main tree."""
        self.repo.write_id("X-3", "DOING")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "x")
        wt = self.worktree()
        quiet(gate.main, ["--work", "X-3/U1"], steps=[fake("a")], root=wt, out=io.StringIO())
        quiet(gate.main, ["--quick"], steps=[fake("a")], root=wt, out=io.StringIO())
        rows = self.history(wt)
        self.assertEqual([(r["form"], r["tree"], r["tree_changed"]) for r in rows],
                         [("work X-3/U1", repo.tree_hash(wt), False), ("quick", repo.tree_hash(wt), False)])
        self.assertEqual(rows[0]["code_tree"], repo.tree_hash(wt, narrowing.SWEPT))  # X-1 U5
        writer = gate_steps.Step("w", (sys.executable, "-B", "-c", "open('crates/n.rs', 'w').write('x')"))
        (wt / "crates").mkdir()
        quiet(gate.main, ["--work", "X-3/U1"], steps=[writer], root=wt, out=io.StringIO())
        self.assertEqual([self.history(wt)[-1][f] for f in ("tree", "code_tree", "tree_changed")], [None, None, True])
        self.assertEqual(git_in(wt, "status", "--porcelain"), "?? crates/\n")  # the real index is not touched
        # the main tree: the code and the cases only (a document written meanwhile is no change)
        doc = gate_steps.Step("d", (sys.executable, "-B", "-c", "open('notes.md', 'w').write('x')"))
        self.run_main([], [doc])
        row = self.history()[-1]
        self.assertEqual((row["tree"], row["tree_changed"]), (repo.tree_hash(self.root, narrowing.SWEPT), False))
        self.assertNotIn("code_tree", row)  # the main tree keeps `SWEPT` as its `tree` (X-1 U5)
        # a commit of the documents while it runs moves HEAD, not the code and the cases (X-1 U4)
        g = "['git', '-c', 'user.name=t', '-c', 'user.email=t@t', '-c', 'commit.gpgsign=false']"
        doc_commit = (f"import subprocess; open('notes.md', 'w').write('y'); subprocess.run({g} + ['add', 'notes.md'], "
                      f"check=True); subprocess.run({g} + ['commit', '-qm', 'doc'], check=True)")  # fmt: skip
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        self.run_main([], [gate_steps.Step("dc", (sys.executable, "-B", "-c", doc_commit))])
        self.assertNotEqual(git_in(self.root, "rev-parse", "HEAD").strip(), head)
        self.assertEqual((self.history()[-1]["tree"], self.history()[-1]["tree_changed"]), (row["tree"], False))
        case = "open('tests/spec/ops/groups.onsa', 'a').write('// x')"
        self.run_main([], [gate_steps.Step("cs", (sys.executable, "-B", "-c", case))])
        self.assertEqual((self.history()[-1]["tree"], self.history()[-1]["tree_changed"]), (None, True))

    def test_a_whole_run_saves_the_base_and_counts_as_every_shard(self):
        """X-1 U4: a whole run saves the base; it counts as every shard unless its tree was dirty or changed."""
        steps = [fake("a")]
        for argv, saves in (([], True), (["--stage-end", "W3"], True), (["--work", "W3-07"], False),
                            (["--only", "a"], False), (["--sweep"], False)):  # fmt: skip
            with self.subTest(argv=argv):
                self.saved.clear()
                self.run_main(argv, steps)
                self.assertEqual(self.saved, [self.root] if saves else [])
        h = git_in(self.root, "rev-parse", "HEAD").strip()[:7]
        out = self.run_main([], steps)[1]
        self.assertIn(f"sweep: next 0/2 (0/2 last at {h}, 0 commits ago; 1/2 last at {h}, 0 commits ago)", out)
        self.assertIn(f"  auto sweep: last PASS at {h} (0 commits ago)", out)
        (self.root / "crates").mkdir()
        writer = gate_steps.Step("w", (sys.executable, "-B", "-c", "open('crates/x.rs', 'w').write('x')"), static=True)
        out = self.run_main(["--sweep"], [writer])[1]
        self.assertIn("tree changed during the run: the shard 0/2 is not counted", out)
        self.assertEqual(gate_runs.next_shard(self.history(), 2), 0)
        self.run_main([], steps)  # crates/x.rs is untracked: a dirty whole run counts as none
        self.assertTrue(self.history()[-1]["dirty"])
        self.assertFalse(gate_runs.whole_run(self.history()[-1]))
        self.assertEqual(gate_runs.next_shard(self.history(), 2), 0)

    def test_a_commit_while_it_runs(self):
        """The row keeps the HEAD and the dirt of the start of the run, not a commit made meanwhile (X-1 U4)."""
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        self.repo.write("crates/y.rs", "y\n")  # dirty at the start; the item commits it
        script = ("import subprocess; g = ['git', '-c', 'user.name=t', '-c', 'user.email=t@t', '-c', "
                  "'commit.gpgsign=false']; subprocess.run(g + ['add', '-A'], check=True); "
                  "subprocess.run(g + ['commit', '-qm', 'meanwhile'], check=True)")  # fmt: skip
        self.run_main([], [gate_steps.Step("c", (sys.executable, "-B", "-c", script))])
        row = self.history()[-1]
        self.assertNotEqual(git_in(self.root, "rev-parse", "HEAD").strip(), head)
        self.assertEqual((row["commit"], row["dirty"]), (head, True))
        self.assertFalse(gate_runs.whole_run(row))

    def test_the_help_of_work(self):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), self.assertRaises(SystemExit):
            gate.main(["--help"], root=self.root)
        text = " ".join(out.getvalue().split())
        for part in ("a W ID of tasks/W/ (W3-11) or a unit of an item of issues/X/ (X-3/U1)",
                     "tools/gate.sh --work X-1/U3", "`tools/work.py patch` reads the last work check",
                     "only the warnings and the last line (the verdict) come after them"):
            self.assertIn(part, text)

    def test_the_work_check_narrows_the_heavy_items(self):
        steps = [fake("fz", narrows=("tools/fuzz.py", "tools/narrowing.py")), fake("st", touches=("tools/",)),
                 fake("plain")]  # fmt: skip
        self.repo.write("crates/x.rs", "fn x() {}\n")
        code, out = self.run_main(["--work", "W3-07", "--work", "W3-08"], steps)
        self.assertEqual(code, 0)
        self.assertEqual(self.argv_of("fz"), ["--changed-since", "auto", "--sample", "0.1", "--salt", "W3-07"])
        self.assertIn("narrowed (sample 0.1, salt W3-07)", out)
        self.assertFalse(self.ran("st"))
        self.assertIn("SKIPPED st", out)
        self.assertIn("the diff does not touch tools/", out)
        self.assertTrue(self.ran("plain"))
        # a diff on the tool of an item narrows it too, the note names the tool (X-1 B1); any diff in tools/ runs
        # the self-test
        self.forget()
        self.repo.write("tools/narrowing.py", "x = 1\n")
        code, out = self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz"), ["--changed-since", "auto", "--sample", "0.1", "--salt", "W3-07"])
        self.assertIn("narrowed (sample 0.1, salt W3-07); the diff touches tools/narrowing.py: the whole runs in the "
                      "sweeps", out)  # fmt: skip
        self.assertTrue(self.ran("st"))
        (self.root / "tools/narrowing.py").unlink()
        self.repo.write("tools/other.py", "x = 1\n")
        self.forget()
        self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz")[:2], ["--changed-since", "auto"])
        self.assertTrue(self.ran("st"))
        (self.root / "tools/other.py").unlink()
        # the places in `touches_except` do not count (X-1 U10): the table of the allowed names alone does not run
        # the self-test (the made-up root's own table), with a tool it does
        real = next(s for s in gate_steps.STEPS if s.name == "gate-selftest")
        data = [fake("st", touches=real.touches, touches_except=real.touches_except)]
        self.repo.write("tools/builtin_names.toml", "x = 1\n")
        self.forget()
        code, out = self.run_main(["--work", "W3-07"], data)
        self.assertEqual((code, self.ran("st")), (0, False))
        self.assertIn("the diff does not touch tools/ other than tools/builtin_names.toml", out)
        self.repo.write("tools/other.py", "x = 1\n")
        self.forget()
        self.run_main(["--work", "W3-07"], data)
        self.assertTrue(self.ran("st"))
        for p in ("tools/builtin_names.toml", "tools/other.py"):
            (self.root / p).unlink()
        # the whole and the stage end: as before
        for argv in ([], ["--stage-end", "W3"], ["--stage-end", "W3", "--work", "W3-07"]):
            with self.subTest(argv=argv):
                self.forget()
                self.assertEqual(self.run_main(argv, steps)[0], 0)
                self.assertEqual(self.argv_of("fz"), [""])
                self.assertTrue(self.ran("st"))

    def test_the_work_check_picks_the_self_tests(self):
        # S2: an item with `picks` gets `--changed-since auto` in a work check whose diff is known, nothing else
        steps = [fake("st", touches=("tools/",), picks=True, sweep=True)]
        self.repo.write("tools/a.py", "x = 1\n")
        code, out = self.run_main(["--work", "W3-07"], steps)
        self.assertEqual((code, self.argv_of("st")), (0, ["--changed-since", "auto"]))
        self.assertIn("the self-tests the diff reads", out)
        for argv in ([], ["--stage-end", "W3"], ["--sweep"]):
            with self.subTest(argv=argv):
                self.forget()
                self.run_main(argv, steps)
                self.assertEqual(self.argv_of("st"), [""])

    def test_the_sweep_skips_an_item_whose_places_did_not_change(self):
        # X-1 (1): in a sweep, an item with `touches` runs unless its last clean run passed and its places other
        # than `touches_except` are as at that commit; a skip is not a run, the whole and the stage end run it
        st = fake("st", touches=("tools/",), touches_except=("tools/t.toml",), sweep=True)

        def sweep(steps=(st,)):
            self.forget()
            return self.run_main(["--sweep"], list(steps))[1]

        self.assertIn("ran: no clean run of it in the history", sweep())
        self.assertTrue(self.ran("st"))
        head = git_in(self.root, "rev-parse", "HEAD").strip()[:7]
        skip = f"tools/ other than tools/t.toml unchanged since its last PASS at {head}"
        for _ in range(2):  # the skipped run is not the base: the PASS of `head` stays it
            self.assertIn(f"SKIPPED st", out := sweep())
            self.assertFalse(self.ran("st"))
        self.assertIn(skip + " (0 commits ago)", out)
        self.repo.write("tools/t.toml", "x = 1\n")  # not counted, committed or not
        self.assertIn(skip, sweep())
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "toml")
        self.assertIn(skip + " (1 commit ago)", sweep())
        self.repo.write("tools/new.py", "x = 1\n")  # untracked
        self.assertIn(f"ran: tools/ other than tools/t.toml changed since its last PASS at {head}", sweep())
        self.assertTrue(self.ran("st"))
        # the stage end and the whole run it whatever the history says
        (self.root / "tools/new.py").unlink()
        self.assertIn("SKIPPED st", sweep())
        for argv in ([], ["--stage-end", "W3"]):
            self.forget()
            self.run_main(argv, [st])
            self.assertTrue(self.ran("st"), argv)
        # a failed last run runs it, also when a PASS comes before it
        self.forget()
        self.run_main([], [fake("st", 1, touches=("tools/",), sweep=True)])
        now = git_in(self.root, "rev-parse", "HEAD").strip()[:7]
        self.assertIn(f"ran: its last run at {now} failed", sweep())
        self.assertIn("SKIPPED st", sweep())

    def test_the_sweep_runs_an_item_without_a_clean_pass_to_compare(self):
        st = fake("st", touches=("tools/",), sweep=True)
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        path = self.root / gate_runs.HISTORY
        path.parent.mkdir(parents=True, exist_ok=True)
        for row, says in (
            ({"commit": head, "dirty": True, "items": {"st": ["PASS", 1.0]}}, "ran: no clean run of it in the history"),
            ({"commit": head, "tree_changed": True, "items": {"st": ["PASS", 1.0]}}, "ran: no clean run"),
            ({"commit": head, "items": {"st": ["SKIPPED", 0.0]}}, "ran: no clean run"),
            ({"commit": head, "items": {"st": "PASS"}}, "ran: no clean run"),
            ({"commit": "f" * 40, "items": {"st": ["PASS", 1.0]}}, f"ran: cannot compare with its last PASS at fffffff"),
        ):
            with self.subTest(row=row):
                path.write_text(json.dumps({"form": "sweep 0/2", **row}) + "\n")
                self.forget()
                self.assertIn(says, self.run_main(["--sweep"], [st])[1])
                self.assertTrue(self.ran("st"))

    def test_a_diff_that_cannot_be_read_runs_whole(self):
        git_in(self.root, "branch", "-D", "dev")
        steps = [fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",), picks=True)]
        code, out = self.run_main(["--work", "W3-07"], steps)
        self.assertEqual(code, 0)
        self.assertEqual(self.argv_of("fz"), [""])
        self.assertIn("whole: the diff is not known", out)
        self.assertTrue(self.ran("st"))
        self.assertEqual(self.argv_of("st"), [""])
        self.assertIn("all: the diff is not known", out)
        self.assertIn("diff: cannot read it (git merge-base HEAD dev", out)
        self.assertEqual(out.splitlines()[-1], "gate: PASS")

    def test_only(self):
        steps = [fake("a"), fake("b", static=True), fake("c", static=True), fake("bad", 1),
                 fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",)),
                 fake("sv", sweep=True, sweep_only=True)]  # fmt: skip
        code, out = self.run_main(["--only", "a"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate (only): PASS"))
        self.assertEqual([p.name for p in self.root.glob("argv-*")], ["argv-a"])
        self.assertNotIn(" b ", out)
        self.forget()
        code, out = self.run_main(["--only", "static,bad"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (1, "gate (only): FAIL (bad)"))
        self.assertEqual(sorted(p.name for p in self.root.glob("argv-*")), ["argv-b", "argv-bad", "argv-c"])
        # in the form of the other options; an item named runs whatever the diff touches
        self.forget()
        self.run_main(["--only", "fz,st", "--work", "W3-07"], steps)
        self.assertEqual(self.argv_of("fz")[:2], ["--changed-since", "auto"])
        self.assertTrue(self.ran("st"))
        self.forget()
        self.run_main(["--only", "fz"], steps)
        self.assertEqual(self.argv_of("fz"), [""])
        for argv in (["--only", "sv"], ["--only", "nope"], ["--only", ""], ["--only", "a", "--quick"]):
            with self.subTest(argv=argv):
                self.forget()
                self.assertEqual(self.run_main(argv, steps)[0], 2)
                self.assertEqual(list(self.root.glob("argv-*")), [])

    def test_the_sweep(self):
        steps = [fake("sv", sweep=True, sweep_only=True), fake("plain"), fake("b", static=True),
                 fake("fz", narrows=("tools/fuzz.py",)), fake("st", touches=("tools/",), sweep=True)]  # fmt: skip
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        code, out = self.run_main(["--sweep"], steps)
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate (sweep 0/2): PASS"))
        self.assertEqual(sorted(p.name for p in self.root.glob("argv-*")), ["argv-b", "argv-fz", "argv-st", "argv-sv"])
        self.assertLess(out.index("=== sv"), out.index("=== b"))
        self.assertEqual(self.argv_of("fz"), ["--shard", "0/2"])
        self.assertNotIn("plain", out)
        self.assertIn(f"sweep: next 1/2 (0/2 last at {head[:7]}, 0 commits ago; 1/2 never)", out)
        self.assertEqual(self.history()[-1]["form"], "sweep 0/2")
        self.run_main(["--sweep"], steps)
        self.assertEqual(self.argv_of("fz"), ["--shard", "1/2"])
        git_in(self.root, "commit", "-q", "--allow-empty", "-m", "next")
        with open(self.root / gate_runs.HISTORY, "a") as f:
            f.write("not json\n")
        code, out = self.run_main(["--sweep"], [fake("fz", 1, narrows=("tools/fuzz.py",))])
        self.assertEqual((code, out.splitlines()[-1]), (1, "gate (sweep 0/2): FAIL (fz)"))
        self.assertIn(f"sweep: next 1/2 (0/2 last at", out)
        self.assertIn(f"1/2 last at {head[:7]}, 1 commit ago); 1 unreadable line", out)
        self.run_main(["--sweep"], steps)  # a failed sweep counts: the next shard
        self.assertEqual(self.argv_of("fz"), ["--shard", "1/2"])
        # another K starts again
        with mock.patch.object(gate_steps, "SHARDS", 3):
            self.run_main(["--sweep"], steps)
            self.assertEqual(self.argv_of("fz"), ["--shard", "0/3"])
        # alone, and in the main tree only
        for argv in (["--sweep", "--work", "W3-07"], ["--sweep", "--quick"], ["--sweep", "--only", "b"]):
            self.assertEqual(self.run_main(argv, steps)[0], 2)
        wt = self.worktree()
        out = io.StringIO()
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=wt, out=out), 2)
        self.assertIn("a worktree", err.getvalue())
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=self.root / "tests", out=out), 2)
        self.assertIn("not a git work tree", err.getvalue())

    def test_the_history(self):
        steps = [fake("a"), fake("p", gate_steps.PARENT, parent=True)]
        head = git_in(self.root, "rev-parse", "HEAD").strip()
        for argv, form in ((["--work", "W3-07"], "work W3-07"), ([], "whole"), (["--stage-end", "W3"], "stage-end W3"),
                           (["--only", "a"], "only a"), (["--quick"], None), (["--work", "W9-99"], None)):  # fmt: skip
            with self.subTest(argv=argv):
                before = len(self.history())
                self.run_main(argv, steps)
                rows = self.history()
                if form is None:
                    self.assertEqual(len(rows), before)
                    continue
                self.assertEqual(len(rows), before + 1)
                row = rows[-1]
                self.assertEqual((row["form"], row["commit"], row["dirty"], row["verdict"]), (form, head, False, "PASS"))
                self.assertEqual(row["items"]["a"][0], "PASS")
                self.assertEqual(row["works"], ["W3-07"] if "--work" in argv else [])
        self.assertEqual(self.history()[0]["items"]["p"][0], "PARENT")
        self.repo.write("crates/x.rs", "x\n")  # untracked: dirty
        self.run_main([], steps)
        self.assertTrue(self.history()[-1]["dirty"])
        # a worktree keeps its own (X-1 U3)
        wt = self.worktree()
        before = len(self.history())
        quiet(gate.main, [], steps=steps, root=wt, out=io.StringIO())
        self.assertEqual(len(self.history()), before)
        self.assertEqual([r["form"] for r in self.history(wt)], ["whole"])
        # a history that cannot be written does not fail the gate
        (self.root / gate_runs.HISTORY).unlink()
        (self.root / gate_runs.HISTORY).mkdir()
        code, out = self.run_main([], steps)
        self.assertEqual(code, 0)
        self.assertIn("  history: cannot write it (", out)
        self.assertIn("  history: cannot read it (", out)
        with mock.patch.object(sys, "stderr", io.StringIO()) as err:
            self.assertEqual(gate.main(["--sweep"], steps=steps, root=self.root, out=io.StringIO()), 2)
        self.assertIn("cannot read the history", err.getvalue())

    def test_the_fuzz_inputs_not_sorted(self):
        """X-1 U9: the main tree's summary lists the inputs in `fuzz.new_inputs` that tests/fuzz/ has no file
        of the same name for, after the golden line and before `sweep:`; it does not fail the gate, and a
        worktree's summary has no such line."""
        new = self.root / "target" / "fuzz" / "new"
        lines = lambda argv=(): self.run_main(list(argv), [fake("a")])  # noqa: E731
        with mock.patch.object(fuzz, "target_directory", return_value=self.root / "target"):
            code, out = lines()
            self.assertEqual(code, 0)
            self.assertIn("  fuzz new: none outside tests/fuzz/\n", out)  # no directory yet
            new.mkdir(parents=True)
            for name in ("840a75a2.onsa", "7f730c9d.onsa", "1a2b3c4d.onsa", "notes.txt"):
                (new / name).write_text("fn\n")
            self.repo.write("tests/fuzz/1a2b3c4d.onsa", "fn\n")
            code, out = lines()
            self.assertEqual(code, 0)
            want = "  fuzz new: 2 not under tests/fuzz/ (sort them: tools/fuzz.py sort, rules/leader.md 4.5): 7f730c9d.onsa, 840a75a2.onsa"
            got = out.splitlines()
            at = got.index(want)
            self.assertTrue(got[at - 1].startswith("  golden: "), got)
            self.assertTrue(got[at + 1].startswith("  sweep: next "), got)
            self.assertIn(want, lines(["--only", "a"])[1].splitlines())  # as `sweep:`
            self.assertNotIn("fuzz new:", lines(["--quick"])[1])  # as `sweep:`
            for name in ("840a75a2.onsa", "7f730c9d.onsa"):
                self.repo.write(f"tests/fuzz/{name}", "fn\n")
            self.assertIn("  fuzz new: none outside tests/fuzz/\n", lines()[1])
            shutil.rmtree(new)
            new.write_text("not a directory\n")
            code, out = lines()
            self.assertEqual(code, 0)
            self.assertRegex(out, rf"\n  fuzz new: cannot read {re.escape(str(new))}/ \(.+\)\n")
            wt = self.worktree()
            (wt / "target" / "fuzz" / "new").mkdir(parents=True)
            (wt / "target" / "fuzz" / "new" / "7f730c9d.onsa").write_text("fn\n")
            out = io.StringIO()
            quiet(gate.main, [], steps=[fake("a")], root=wt, out=out)
            self.assertNotIn("fuzz new:", out.getvalue())

    def test_the_warning_of_the_time(self):
        steps = [sleeper("s3", 0.3), sleeper("s2", 0.2), sleeper("s1", 0.1), fake("s0")]
        with mock.patch.object(gate_steps, "BUDGET_WORK", 0.4):
            code, out = self.run_main(["--work", "W3-07"], steps)
            lines = out.splitlines()
            self.assertEqual((code, lines[-1]), (0, "gate: PASS"))
            self.assertRegex(lines[-2], r"^warning: the work check took \d+s, \d+s over its 0.4s; "
                                        r"the longest: s3 0\.\ds, s2 0\.\ds, s1 0\.\ds$")  # fmt: skip
            for argv in ([], ["--only", "s3,s2,s1", "--work", "W3-07"]):
                self.assertNotIn("warning", self.run_main(argv, steps)[1])
        with mock.patch.object(gate_steps, "BUDGET_SWEEP", 0):
            out = self.run_main(["--sweep"], [fake("b", static=True)])[1]
            self.assertTrue(out.splitlines()[-2].startswith("warning: the sweep took"))
        # the wait for the lock does not count
        with mock.patch.object(gate_steps, "BUDGET_WORK", 0.5), open(gate.lock_path(self.root), "a+") as held:
            gate.fcntl.flock(held, gate.fcntl.LOCK_EX)
            out = io.StringIO()
            other = threading.Thread(target=lambda: gate.main(["--work", "W3-07"], steps=[fake("a")], root=self.root,
                                                              out=out))  # fmt: skip
            other.start()
            time.sleep(1.0)
            gate.fcntl.flock(held, gate.fcntl.LOCK_UN)
            other.join(10)
        self.assertIn("waited", out.getvalue())
        self.assertNotIn("warning", out.getvalue())

    def test_parent(self):
        results = gate.run_steps([fake("gm", gate_steps.PARENT, parent=True), fake("x", gate_steps.PARENT)], {},
                                 cwd=self.root, out=io.StringIO())  # fmt: skip
        self.assertEqual([r.status for r in results], ["PARENT", "FAIL"])
        self.assertIn("waits for the parent", results[0].describe())
        code, out = self.run_main([], [fake("gm", gate_steps.PARENT, parent=True)])
        self.assertEqual((code, out.splitlines()[-1]), (0, "gate: PASS"))
        self.assertIn("PARENT  gm", out)

    def test_gap_marks_in_the_three_trees(self):
        def run(root):
            out = io.StringIO()
            with mock.patch.object(sys, "stdout", out):
                return gap_marks.main(["--root", str(root)]), out.getvalue()

        wt = self.worktree()
        for text, main_code, wt_code in (("// SPEC-GAP(S-45): x\n", 0, 0), ("// SPEC-GAP(NEW): x\n", 1, gate_steps.PARENT),
                                         ("// SPEC-GAP(S-99): x\n", 1, gate_steps.PARENT),
                                         ("// SPEC-GAP(NEW): x\n// SPEC-GAP: y\n", 1, 1),
                                         ("// SPEC-GAP(Q-10): x\n", 1, 1)):  # fmt: skip
            with self.subTest(text=text):
                for root in (self.root, wt):
                    (root / "crates/a/src").mkdir(parents=True, exist_ok=True)
                    (root / "crates/a/src/lib.rs").write_text(text)
                code, out = run(self.root)
                self.assertEqual(code, main_code, out)
                self.assertNotIn("parent:", out)
                code, out = run(wt)
                self.assertEqual(code, wt_code, out)
                if wt_code == gate_steps.PARENT:
                    self.assertIn("parent: crates/a/src/lib.rs:1:", out)
                    self.assertIn("1 for the parent to register", out)
        # not a git root (the made-up roots): fails as in the main tree
        plain = Repo(self.elsewhere())
        plain.write("crates/a/src/lib.rs", "// SPEC-GAP(NEW): x\n")
        self.assertEqual(run(plain.root)[0], 1)
        # X9-29: a mark that names a dropped S is told in every tree and fails none
        for root in (self.root, wt, plain.root):
            (root / "crates/a/src/lib.rs").write_text("// SPEC-GAP(S-15): x\n")
            code, out = run(root)
            self.assertEqual(code, gate_steps.PARENT, out)
            self.assertIn("parent: crates/a/src/lib.rs:1: S-15 is DROPPED", out)


class HashSeed(unittest.TestCase):
    def test_the_seed_of_the_environment_or_a_random_u64(self):
        saved = os.environ.pop("ONSA_HASH_SEED", None)
        try:
            os.environ["ONSA_HASH_SEED"] = "12345"
            self.assertEqual(gate.hash_seed(), "12345")
            for unset in ("", None):
                if unset is None:
                    del os.environ["ONSA_HASH_SEED"]
                else:
                    os.environ["ONSA_HASH_SEED"] = unset
                seed = gate.hash_seed()
                self.assertRegex(seed, r"^[0-9]+$")
                self.assertLess(int(seed), 2 ** 64)
        finally:
            os.environ.pop("ONSA_HASH_SEED", None)
            if saved is not None:
                os.environ["ONSA_HASH_SEED"] = saved


class Golden(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def write(self, rel, text="x\n"):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def test_changes(self):
        self.git("init", "-q")
        for rel in ("tests/golden/c/a.c", "tests/golden/c/b.h", "tests/golden/core/m.core", "tests/golden/core/m.onsa", "src/x.rs"):
            self.write(rel)
        self.git("add", ".")
        self.git(
            "-c", "commit.gpgsign=false", "-c", "user.name=t", "-c", "user.email=t@t",
            "commit", "--no-verify", "-q", "-m", "init",
        )  # fmt: skip
        self.write("tests/golden/c/a.c", "changed\n")
        (self.root / "tests/golden/c/b.h").unlink()
        self.write("tests/golden/graph/new.dot")
        self.write("tests/golden/core/m.onsa", "an input changed\n")
        self.write("tests/golden/core/n.core")
        self.git("add", "tests/golden/core/n.core")  # staged counts too
        self.write("tests/golden/c/é.c")  # not quoted
        self.write("src/x.rs", "outside tests/golden\n")
        self.assertEqual(
            gate.golden_changes(self.root),
            [
                "M tests/golden/c/a.c",
                "D tests/golden/c/b.h",
                "? tests/golden/c/é.c",
                "M tests/golden/core/m.onsa",
                "A tests/golden/core/n.core",
                "? tests/golden/graph/new.dot",
            ],
        )

    def test_not_a_repository(self):
        with self.assertRaises(subprocess.CalledProcessError):
            gate.golden_changes(self.root)
        self.assertEqual(quiet(gate.golden_main, self.root), 1)

    def commit(self):
        self.git("add", ".")
        self.git("-c", "commit.gpgsign=false", "-c", "user.name=t", "-c", "user.email=t@t", "commit", "--no-verify", "-q", "-m", "c")

    def test_fix_copies(self):
        # X9-27: the `.fix<K>` files under tests/ are listed as tests/golden is; other names are not
        self.git("init", "-q")
        for rel in ("tests/spec/a.onsa.fix1", "tests/spec/b.onsa.fix2", "tests/c.onsa.fix1", "tests/d.fix1.bak", "src/e.onsa.fix1"):
            self.write(rel)
        self.commit()
        self.assertEqual(gate.golden_changes(self.root), [])
        self.assertEqual(quiet_out(gate.golden_main, self.root), (0, ["no golden file differs from HEAD"]))
        self.write("tests/spec/a.onsa.fix1", "changed\n")
        (self.root / "tests/spec/b.onsa.fix2").unlink()
        self.write("tests/spec/deep/n.onsa.fix12")
        self.git("add", "tests/spec/deep/n.onsa.fix12")
        self.write("tests/u.onsa.fix3")
        for rel in ("tests/d.fix1.bak", "tests/f.onsa.fixed", "tests/g.onsa.fix", "src/e.onsa.fix1"):
            self.write(rel, "not a copy\n")
        self.assertEqual(
            gate.golden_changes(self.root),
            ["M tests/spec/a.onsa.fix1", "D tests/spec/b.onsa.fix2", "A tests/spec/deep/n.onsa.fix12", "? tests/u.onsa.fix3"],
        )

    def test_foreign_forms(self):
        # X9-27: the `id` of each form whose `fixed` differs; a change of the other fields is not listed
        def form(id_, *examples, origin="C"):
            return f'[[form]]\nid = "{id_}"\norigin = "{origin}"\n' + "".join(
                '[[form.example]]\nsource = "s"\n' + (f"fixed = {x}\n" if x is not None else "") for x in examples
            )

        self.git("init", "-q")
        self.write("spec/foreign-forms.toml", "# head\n")  # in HEAD with no form
        self.write("src/x", "x\n")
        self.commit()
        forms = form("semi", '["a"]') + form("two", '["b"]', '["c", "d"]') + form("e0002", None) + form("gone", '["g"]')
        self.write("spec/foreign-forms.toml", forms)
        self.assertEqual(
            gate.golden_changes(self.root),
            ["A spec/foreign-forms.toml: fixed of gone", "A spec/foreign-forms.toml: fixed of semi",
             "A spec/foreign-forms.toml: fixed of two"],
        )  # fmt: skip
        self.commit()
        self.assertEqual(gate.golden_changes(self.root), [])
        changed = (form("semi", '["a2"]') + form("two", '["b"]', None, '["c", "d"]', origin="Rust")
                   + form("e0002", None, None) + form("new", "['''\n''']"))  # fmt: skip
        self.write("spec/foreign-forms.toml", "# the head changed\n" + changed)
        self.assertEqual(
            gate.golden_changes(self.root),
            ["D spec/foreign-forms.toml: fixed of gone", "A spec/foreign-forms.toml: fixed of new",
             "M spec/foreign-forms.toml: fixed of semi"],
        )  # fmt: skip
        self.write("spec/foreign-forms.toml", "[[form]\n")  # a toml that cannot be read
        with self.assertRaises(ValueError):
            gate.golden_changes(self.root)
        code, out = quiet_out(gate.golden_main, self.root)
        self.assertEqual(code, 1)
        self.assertIn("cannot list the golden files", out[0])

    def test_summary_lines(self):
        # the head of the line and its text when nothing differs stay as they were (read by the parent)
        self.assertIn("  golden: no file differs from HEAD", gate.summary([], [], [], ()))
        lines = gate.summary([], [], ["M spec/foreign-forms.toml: fixed of semi"], ())
        self.assertIn("  golden: differs from HEAD (read and approve):", lines)
        self.assertIn("    M spec/foreign-forms.toml: fixed of semi", lines)


if __name__ == "__main__":
    unittest.main(verbosity=1)
