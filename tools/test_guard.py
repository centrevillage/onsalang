#!/usr/bin/env python3
"""Self-tests of tools/guard.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_guard.py
"""
import io
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import guard  # noqa: E402

PY = sys.executable


def alive(pid):
    """Whether `pid` is a process still (not reaped, or reaped late by init: a short wait)."""
    for _ in range(40):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        time.sleep(0.05)
    return True


class Guard(unittest.TestCase):
    """tools/guard.py run: the limits hold on the children of the command too (the grandchild of `sh -c`, as
    `/usr/bin/time -l onsa …` is), and nothing of the group is left when it ends."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.pidfile = Path(self.tmp.name) / "pid"

    def grandchild(self, body, background=False):
        """`sh -c` (the child) running Python (the grandchild) that writes its pid, then `body`. In the
        background the child ends once the pid is written, leaving the grandchild behind."""
        script = f"import os; open({str(self.pidfile)!r}, 'w').write(str(os.getpid())); {body}"
        then = f" & while [ ! -s {self.pidfile} ]; do sleep 0.01; done" if background else "; true"
        return ["sh", "-c", f"{PY} -c \"{script}\"{then}"]

    def run_guard(self, command, gb, seconds):
        out, err = io.StringIO(), io.StringIO()
        code, peak, why = guard.guard(command, gb, seconds, out=out, err=err)
        return code, peak, why, out.getvalue()

    def test_memory_of_a_grandchild_stops_the_group(self):
        code, peak, why, out = self.run_guard(
            self.grandchild("b = b'x' * (160 << 20); import time; time.sleep(30)"), 0.06, 20)
        self.assertEqual(why, "killed (memory)", out)
        self.assertGreater(peak, 60 * 1024)
        self.assertFalse(alive(int(self.pidfile.read_text())))

    def test_time_stops_the_group(self):
        code, peak, why, out = self.run_guard(self.grandchild("import time; time.sleep(30)"), 1, 0.4)
        self.assertEqual(why, "killed (time)", out)
        self.assertEqual(code, -9)
        self.assertFalse(alive(int(self.pidfile.read_text())))

    def test_a_command_that_ends_prints_its_output_and_the_last_line(self):
        code, peak, why, out = self.run_guard(["sh", "-c", "echo hi"], 1, 10)
        self.assertEqual((code, why), (0, ""))
        self.assertTrue(out.startswith("hi\n"), out)
        self.assertRegex(out.splitlines()[-1], r"^guard: exit 0 peak \d+ MB [0-9.]+ s$")

    def test_what_the_command_leaves_behind_is_killed(self):
        code, peak, why, out = self.run_guard(self.grandchild("import time; time.sleep(30)", background=True), 1, 10)
        self.assertEqual((code, why), (0, ""))
        self.assertFalse(alive(int(self.pidfile.read_text())))

    def test_the_command_line_takes_the_command_after_the_dashes(self):
        out = io.StringIO()
        real, sys.stdout = sys.stdout, out
        try:
            code = guard.main(["run", "1", "10", "--", "sh", "-c", "echo there"])
        finally:
            sys.stdout = real
        self.assertEqual(code, 0)
        self.assertIn("there\n", out.getvalue())
        self.assertIn("guard: exit 0", out.getvalue())


if __name__ == "__main__":
    unittest.main()
