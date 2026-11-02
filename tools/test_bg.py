#!/usr/bin/env python3
"""Self-tests of tools/bg.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_bg.py
"""
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bg  # noqa: E402
from selftest_support import quiet  # noqa: E402


class Bg(unittest.TestCase):
    """tools/bg.py: a command in the background, waited for by its pid; nothing is left running."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dirs = []

    def tearDown(self):
        for d in self.dirs:
            quiet(bg.stop, d)
            pid = bg.read(d, "pid")
            self.assertFalse(pid and bg.alive(int(pid)), f"{d}: left running")
        self.tmp.cleanup()

    def bg(self, *args):
        r = subprocess.run([sys.executable, "-B", str(Path(bg.__file__)), *map(str, args)], capture_output=True,
                           text=True, timeout=60)
        return r.returncode, r.stdout

    def run_(self, name, *cmd):
        d = Path(self.tmp.name) / name
        self.dirs.append(d)
        self.assertEqual(self.bg("run", d, "--", *cmd)[0], 0)
        return d

    def test_exit_and_output(self):
        d = self.run_("short", "sh", "-c", "echo out; echo err >&2; exit 3")
        code, out = self.bg("wait", d, "--timeout", "30")
        self.assertEqual(code, 3, out)
        self.assertIn("exit 3", out)
        self.assertIn("| out\n  | err", out)
        self.assertIn("finished, exit 3", self.bg("status", d)[1])

    def test_timeout_stop_and_status(self):
        d = self.run_("long", "sleep", "30")
        self.assertEqual(self.bg("run", d, "--", "true")[0], 1)  # still running
        code, out = self.bg("wait", d, "--timeout", "0.3")
        self.assertEqual(code, bg.TIMEOUT_EXIT, out)
        self.assertIn("still running", out)
        self.assertIn(": running", self.bg("status", d)[1])
        self.assertEqual(self.bg("stop", d)[0], 0)
        self.assertIn("finished, exit SIGTERM", self.bg("status", d)[1])
        self.assertEqual(self.bg("wait", d)[0], 128 + signal.SIGTERM)
        self.assertEqual(self.bg("run", d, "--", "true")[0], 0)  # finished: the directory is free again
        self.assertEqual(self.bg("wait", d, "--timeout", "30")[0], 0)

    def test_a_lost_watcher(self):
        d = self.run_("lost", "sleep", "30")
        watcher, pid = int(bg.read(d, "watcher")), int(bg.read(d, "pid"))
        os.kill(watcher, signal.SIGKILL)
        deadline = time.monotonic() + 10
        while bg.alive(watcher) and time.monotonic() < deadline:
            time.sleep(0.05)
        code, out = self.bg("wait", d, "--timeout", "5")
        self.assertEqual(code, bg.LOST_EXIT, out)
        self.assertIn("lost", out)
        self.assertIn(": lost", self.bg("status", d)[1])
        self.assertEqual(self.bg("run", d, "--", "true")[0], 1)  # its command still runs
        self.assertEqual(self.bg("stop", d)[0], 0)
        self.assertFalse(bg.alive(pid))


if __name__ == "__main__":
    unittest.main(verbosity=1)
