#!/usr/bin/env python3
"""Self-tests of tools/handback.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_handback.py
"""
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import handback  # noqa: E402
import repo  # noqa: E402
from selftest_support import handback_line, quiet_out  # noqa: E402


class Handback(unittest.TestCase):
    """tools/handback.py save / usage (X-9 U14): the main session's line with no agent, the agents' lines as before."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.project = Path(self.tmp.name)
        patch = mock.patch.object(handback, "PROJECT", self.project)
        patch.start()
        self.addCleanup(patch.stop)

    def write(self, rel, calls):
        """A made-up record: (id, model, usage) per line; a line that is not JSON first."""
        path = self.project / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        lines = ["not json"] + [json.dumps({"message": {"id": i, "model": m, "usage": u}}) for i, m, u in calls]
        path.write_text("\n".join(lines) + "\n")
        return path

    def test_usage(self):
        opus = "claude-opus-5-5"
        self.write("s1.jsonl", [("m1", opus, {"input_tokens": 100}), ("m1", opus, {"input_tokens": 100}),
                                ("m2", opus, {"input_tokens": 10, "cache_read_input_tokens": 4990}),
                                ("m3", opus, {"input_tokens": 3000, "output_tokens": 50}),
                                ("m4", "<synthetic>", {"input_tokens": 0, "output_tokens": 0})])  # fmt: skip
        self.write("s1/subagents/agent-a1.jsonl", [("x", opus, {"input_tokens": 7000})])
        self.write("s1/subagents/agent-a2.jsonl", [("y", opus, {"input_tokens": 30000})])
        self.assertEqual(quiet_out(handback.main, ["usage", "s1"]), (0, [
            "s1: calls 4, context now 3,000, largest context 5,000, cache read 4,990, cache write 0, output 50, "
            "API-equivalent $0.0"]))  # fmt: skip
        self.assertEqual(quiet_out(handback.main, ["usage", "s1", "a1", "a2"]), (0, [
            "a1: calls 1, largest context 7,000, cache read 0, cache write 0, output 0, API-equivalent $0.0",
            "a2: calls 1, largest context 30,000, cache read 0, cache write 0, output 0, API-equivalent $0.1"]))

    def test_save(self):
        path = self.write("a.jsonl", [])
        out = self.project / "r.md"
        self.assertEqual(quiet_out(handback.main, ["save", str(path), str(out)]), (1, [f"no SubagentHandback in {path}"]))
        path.write_text(handback_line("報告") + handback_line("前の報告", "api-request-blob"))  # a copy (X-11)
        self.assertEqual(quiet_out(handback.main, ["save", str(path), str(out)]), (0, ["2 characters"]))
        self.assertEqual(out.read_text(), "報告")

    def test_help(self):
        # rules/tools.md 9.4, as `Work.test_help`
        for name, c in handback.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^handback\.py {name}( |$)")
                code, lines = quiet_out(handback.main, ["help", name])
                self.assertEqual(code, 0)
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            with self.subTest(role=role):
                code, lines = quiet_out(handback.main, ["help", "--role", role])
                want = [n for n, c in handback.COMMANDS.items() if role in c.roles]
                self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want or ["（役割"]))
        names = list(handback.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(handback.main, ["help"])[1][: len(names)]], names)
        for argv, code in (([], 2), (["--help"], 0)):  # no command is a usage error; `--help` lists the commands
            buf = io.StringIO()
            with self.subTest(argv=argv), mock.patch.object(sys, "stdout", buf), mock.patch.object(sys, "stderr", buf), \
                    self.assertRaises(SystemExit) as e:  # fmt: skip
                handback.main(argv)
            self.assertEqual(e.exception.code, code)
            self.assertIn("{" + ",".join(names + ["help"]) + "}", buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
