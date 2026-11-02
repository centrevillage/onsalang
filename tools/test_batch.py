#!/usr/bin/env python3
"""Self-tests of tools/batch.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_batch.py
"""
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import batch  # noqa: E402
from selftest_support import TempRepo  # noqa: E402

# A stand-in for `onsa_cases --serve`: answers `served:<text>` (exit 0) for the text of the request's last
# file; `die` ends it with SIGKILL (an abort would make the system write a crash report), `exit` with 3,
# `hang` gives no answer, `broken` a head that is no answer. Its starts are counted in `starts`.
SERVER = r"""
import os, sys, time
if sys.argv[1:] != ["--serve"]:
    sys.exit(2)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "starts"), "a") as f:
    f.write("x")
inp, out = sys.stdin.buffer, sys.stdout.buffer
while line := inp.readline():
    words, n = line.decode().rstrip("\n").rsplit("\t", 1)
    for _ in range(int(n)):
        name, size = inp.readline().decode().rstrip("\n").rsplit("\t", 1)
        text = inp.read(int(size)).decode()
    if text.startswith("die"):
        os.kill(os.getpid(), 9)
    if text.startswith("exit"):
        sys.exit(3)
    if text.startswith("hang"):
        time.sleep(30)
    if text.startswith("broken"):
        out.write(b"x\ty\n")
    body = f"served:{words}:{text}".encode()
    out.write(f"0\t{len(body)}\t0\n".encode() + body)
    out.flush()
"""

# A stand-in for the command: prints `alone:<words>:<text>` of its last file; `...-crash` exits 7 (a crash
# for `crashed` below), `hang-both` sleeps past the time-out.
PRODUCT = r"""
import sys, time
text = open(sys.argv[-1], encoding="utf-8").read()
if text == "hang-both":
    time.sleep(30)
print(f"alone:{' '.join(sys.argv[1:-1])}:{text}", end="")
sys.exit(7 if text.endswith("-crash") else 0)
"""


def crashed(words, result):
    return result.code != 0


class Pool(TempRepo):
    def setUp(self):
        super().setUp()
        self.server = [sys.executable, "-B", str(self.repo.write("server.py", SERVER)), "--serve"]
        self.product = [sys.executable, "-B", str(self.repo.write("product.py", PRODUCT))]

    def pool(self, serve=True, timeout=10, max_deaths=batch.MAX_DEATHS, server=None):
        p = batch.Pool((server or self.server) if serve else None, lambda words: [*self.product, *words],
                       self.repo.root / "work", timeout, crashed, max_deaths)
        self.addCleanup(p.close)
        return p

    def run_all(self, pool, texts):
        return [pool.run(("check",), [("m.onsa", t.encode())]).out.decode() for t in texts]

    @property
    def starts(self):
        path = self.repo.root / "starts"
        return len(path.read_text()) if path.exists() else 0

    def test_one_server_answers_request_after_request(self):
        p = self.pool()
        self.assertEqual(self.run_all(p, ["a", "b"]), ["served:check:a", "served:check:b"])
        r = p.run(("fmt", "--check"), [("d/n.onsa", b"c")])
        self.assertEqual((r.code, r.out, r.err), (0, b"served:fmt --check:c", ""))
        self.assertEqual((self.starts, p.deaths, p.close()), (1, 0, []))

    def test_an_ended_server_reruns_that_request_alone(self):
        p = self.pool()
        self.assertEqual(self.run_all(p, ["a", "die", "b", "exit", "die-crash", "c"]),
                         ["served:check:a", "alone:check:die", "served:check:b", "alone:check:exit",
                          "alone:check:die-crash", "served:check:c"])
        self.assertEqual((self.starts, p.deaths), (4, 3))
        # where the command does not crash, the server and the command disagree
        self.assertEqual(p.close(), [
            "the server of onsa_cases ended (signal 9) on check of m.onsa, where the command does not crash",
            "the server of onsa_cases ended (exit 3) on check of m.onsa, where the command does not crash"])

    def test_a_broken_answer_and_a_time_out(self):
        p = self.pool(timeout=1)
        self.assertEqual(self.run_all(p, ["broken", "hang", "a"]),
                         ["alone:check:broken", "alone:check:hang", "served:check:a"])
        r = p.run(("check",), [("m.onsa", b"hang-both")])
        self.assertEqual((r.code, r.out), (None, b""))  # the command timed out too: a crash, no failure
        self.assertEqual(p.deaths, 3)
        self.assertEqual(p.close(), [
            "the server of onsa_cases ended (a broken answer) on check of m.onsa, where the command does not crash",
            "the server of onsa_cases ended (no answer within 1 s) on check of m.onsa, where the command does not "
            "crash"])

    def test_past_max_deaths_the_rest_runs_alone_and_fails(self):
        p = self.pool(max_deaths=2)
        self.assertEqual(self.run_all(p, ["die-crash"] * 3 + ["a", "b"]),
                         ["alone:check:die-crash"] * 3 + ["alone:check:a", "alone:check:b"])
        self.assertEqual((self.starts, p.deaths), (3, 3))
        self.assertEqual(p.close(), ["onsa_cases --serve ended 3 times (more than 2): the rest ran one process each"])

    def test_a_binary_without_serve_fails(self):
        for server, why in ((self.product + ["--serve"], "exit 1"), ([str(self.repo.root / "none")], "cannot start")):
            with self.subTest(why):
                p = self.pool(server=server)
                self.assertEqual(self.run_all(p, ["a"]), ["alone:check:a"])
                failures = p.close()
                self.assertEqual(len(failures), 1, failures)
                self.assertIn(f"the server of onsa_cases ended ({why}", failures[0])

    def test_no_server_runs_each_alone(self):
        p = self.pool(serve=False)
        self.assertEqual(self.run_all(p, ["a", "die"]), ["alone:check:a", "alone:check:die"])
        self.assertEqual((self.starts, p.deaths, p.close()), (0, 0, []))
        self.assertEqual(list((self.repo.root / "work").iterdir()), [])  # the files of each run are gone

    def test_request(self):
        self.assertEqual(batch.request(("diff", "--ast"), [("a.onsa", b"x\n"), ("b.onsa", b"")]),
                         b"diff --ast\t2\na.onsa\t2\nx\nb.onsa\t0\n")
        with self.assertRaises(ValueError):
            batch.request(("check",), [("a\tb.onsa", b"")])


if __name__ == "__main__":
    unittest.main()
