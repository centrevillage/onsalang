#!/usr/bin/env python3
"""Self-tests of tools/hooks/claude_hook.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/hooks/test_claude_hook.py
"""
import io
import json
import os
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import claude_hook  # noqa: E402
import handback  # noqa: E402
import repo  # noqa: E402
from selftest_support import handback_line, quiet_out, git_in  # noqa: E402


class ClaudeHook(unittest.TestCase):
    """tools/hooks/claude_hook.py (X-9 U3): what each event stops, changes, writes and tells, and its help."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.scratch = Path(self.tmp.name) / "scratch"
        self.scratch.mkdir()

    def tearDown(self):
        self.tmp.cleanup()

    def hook(self, event_name, event, stdin=None):
        """(the JSON it printed or None, the other lines); the exit is always 0."""
        text = json.dumps({"scratchpad_dir": str(self.scratch), **event}) if stdin is None else stdin
        code, lines = quiet_out(claude_hook.main, [event_name], io.StringIO(text))
        self.assertEqual(code, 0)
        out = [x for x in lines if x.startswith("{")]
        self.assertLessEqual(len(out), 1, lines)
        return (json.loads(out[0])["hookSpecificOutput"] if out else None), [x for x in lines if not x.startswith("{")]

    def pre(self, role, tool, **inp):
        event = {"tool_name": tool, "tool_input": inp, "cwd": "/r"}
        if role != "parent":
            event["agent_type"] = repo.ROLES.get(role, role)
        return self.hook("PreToolUse", event)[0]

    def denied(self, role, tool, **inp):
        out = self.pre(role, tool, **inp)
        if out and out.get("permissionDecision") == "deny":
            self.assertTrue(out["permissionDecisionReason"])
            return True
        self.assertNotIn("permissionDecision", out or {})  # only a stop decides the permission
        return False

    def test_stops(self):
        bash = lambda c: ("Bash", {"command": c})  # noqa: E731
        cases = [  # (role, (tool, input), stopped)
            ("parent", bash("cd /r/.claude/worktrees/a && git log"), True),
            ("parent", bash("(cd .claude/worktrees/a; ls)"), True),
            ("parent", bash("git -C /r/.claude/worktrees/a log"), False),
            ("parent", bash("echo 'cd .claude/worktrees/a'"), False),
            ("parent", bash("cd /r/tools && ls"), False),
            ("i", bash("cd /r/.claude/worktrees/a && git log"), False),
            ("parent", ("Agent", {"subagent_type": "onsa-impl", "model": "sonnet", "prompt": "p"}), True),
            ("parent", ("Agent", {"subagent_type": "onsa-impl", "prompt": "p"}), False),
            ("parent", ("Agent", {"subagent_type": "general-purpose", "model": "sonnet"}), False),
            ("parent", bash("python3 -B tools/fuzz.py --deep"), True),
            ("i", bash("env X=1 python3 -B /r/tools/fuzz.py --seed 3 --deep"), True),
            ("i", bash("python3 -B tools/fuzz.py --seed 3"), False),
            ("t", bash("python3 -B tools/bg.py run /d -- tools/gate.sh --work X"), True),
            ("t", bash("git log -- tools/gate.py; python3 -B tools/test_gate.py"), False),
            ("advisor", bash("cargo -q test -p onsa_cli"), True),
            ("gap", bash("ls && cargo build"), True),
            ("advisor", bash("cargo metadata; ./target/debug/onsa check a.onsa"), False),
            ("b", bash("cargo test -p onsa_cli"), False),
            ("t", ("Read", {"file_path": "/r/crates/onsa_cli/src/main.rs"}), True),
            ("t", ("Grep", {"pattern": "fn", "path": "crates/onsa_diag/src"}), True),
            ("t", ("Glob", {"pattern": "crates/*/src/**/*.rs"}), True),
            ("t", ("Grep", {"pattern": "fn", "path": "crates", "glob": "*/src/*.rs"}), True),  # the path and the glob
            ("t", ("Glob", {"pattern": "*/src/**", "path": "/r/crates"}), True),
            ("t", ("Grep", {"pattern": "fn", "path": "crates", "glob": "*/tests/*.rs"}), False),
            ("t", ("Grep", {"pattern": "crates/onsa_cli/src/", "path": "tests"}), False),  # the text, not a path
            ("t", ("Read", {"file_path": "/r/crates/onsa_cli/tests/cli.rs"}), False),
            ("t", bash("cat crates/onsa_cli/src/main.rs"), False),
            ("i", ("Read", {"file_path": "/r/crates/onsa_cli/src/main.rs"}), False),
            ("i", bash("python3 -B tools/work.py close --dry-run"), True),  # the cleaning up is the parent's (X-9 U5)
            ("b", bash("cd /r && python3 -B /r/tools/work.py done agent-a1 --main /r"), True),
            ("onsa-other", bash("tools/work.py remove /r/.claude/worktrees/a"), True),
            ("i", bash("python3 -B tools/work.py apply /tmp/p.patch --to /r/.claude/worktrees/a"), False),
            ("i", bash("python3 -B tools/work.py apply /tmp/p.patch"), False),
            ("parent", bash("python3 -B tools/work.py close"), False),
        ]  # fmt: skip
        for role, (tool, inp), stopped in cases:
            with self.subTest(role=role, input=inp):
                self.assertEqual(self.denied(role, tool, **inp), stopped)
        for role in repo.ROLES:  # the gate (X9-47) and the builds, by role
            with self.subTest(role=role):
                self.assertEqual(self.denied(role, "Bash", command="tools/gate.sh --work X-9/U3"),
                                 role in ("t", "b", "advisor", "gap", "docs"))  # fmt: skip
                self.assertEqual(self.denied(role, "Bash", command="cargo run -q -p onsa_cli"), role in ("advisor", "gap"))

    def test_heredocs(self):
        """X-9 U7: a heredoc's body is not commands but for what the shell runs in an unquoted one."""
        cases = [  # (role, command, stopped)
            ("advisor", "cat > /tmp/x.md <<'EOF2'\n- V-12 消すのは `work.py done`\nEOF2", False),  # the three of M-8
            ("parent", "cat > /tmp/x.md <<'EOF2'\n- 4.2 `fuzz.py --deep` は回さない\nEOF2", False),
            ("t", "cat > /tmp/x.md <<'EOF2'\n受ける形は `tools/gate.sh --help`\nEOF2", False),
            ("advisor", "tools/work.py done x", True),  # the same words as commands
            ("parent", "tools/fuzz.py --deep", True),
            ("t", "tools/gate.sh --work X", True),
            ("i", "grep -n 'fuzz.py --deep' rules/checks.md", False),
            ("i", 'cat <<"E"F\n$(tools/fuzz.py --deep)\nEF', False),  # a word quoted in part
            ("i", "cat <<\\EOF\n`tools/fuzz.py --deep`\nEOF", False),
            ("i", "cat <<EOF\nfuzz.py --deep; tools/fuzz.py --deep\nEOF", False),  # the plain text of the body
            ("i", "cat <<EOF\na $(tools/fuzz.py --deep) b\nEOF", True),  # what the shell runs in it
            ("i", "cat <<EOF\na `python3 -B tools/fuzz.py --deep` b\nEOF", True),
            ("i", "cat <<EOF\n$(echo ')' $(tools/fuzz.py --deep))\nEOF", True),
            ("i", "cat <<EOF\n\\$(tools/fuzz.py --deep) \\`tools/fuzz.py --deep\\`\nEOF", False),
            ("i", "cat <<EOF\n$(ls; tools/fuzz.py --deep", True),  # no end of the `$(`, no line of the word
            ("i", "cat <<'A' > a; cat <<B > b\nfuzz.py --deep\nA\n$(tools/fuzz.py --deep)\nB", True),  # two on a line
            ("i", "cat <<'A' > a; cat <<'B' > b\n$(tools/fuzz.py --deep)\nA\ntools/fuzz.py --deep\nB", False),
            ("i", "cat <<-'EOF'\n\ttools/fuzz.py --deep\n\tEOF\ntools/fuzz.py --deep", True),  # the line after it
            ("i", "cat <<-'EOF'\n\ttools/fuzz.py --deep\n\tEOF\nls", False),
            ("i", "cat <<'EOF'\n\tEOF\ntools/fuzz.py --deep\nEOF", False),  # `<<`: the tab stays in the line
            ("i", "cat <<'EOF'\nx\ntools/fuzz.py --deep", False),  # no line of the word: the rest is the body
            ("i", "cat <<'EOF'\nx\n EOF\nEOF\ntools/fuzz.py --deep", True),
            ("i", "echo '<<EOF'\ntools/fuzz.py --deep", True),  # not an operator
            ("i", "ls # <<EOF\ntools/fuzz.py --deep", True),
            ("i", "echo $((1<<2))\ntools/fuzz.py --deep", True),
            ("i", "cat <<< x\ntools/fuzz.py --deep", True),
            ("i", "cat <<\ntools/fuzz.py --deep", True),
            ("i", "cat <<`x`\ntools/fuzz.py --deep", True),  # no word: no operator
        ]  # fmt: skip
        for role, command, stopped in cases:
            with self.subTest(role=role, command=command):
                self.assertEqual(self.denied(role, "Bash", command=command), stopped)
        tells = lambda c: "additionalContext" in (self.pre("i", "Bash", command=c) or {})  # noqa: E731
        self.assertFalse(tells("python3 - <<'EOF'\nx = '<<EOF'\ny = 1 <<E\nEOF"))  # M-7: `<<` in a body
        self.assertTrue(tells("cat <<'A' > a; python3 - <<B\nx\nA\ny\nB"))
        self.assertFalse(tells("python3 -c 'print(\"<<EOF\")'"))

    def test_gate_help(self):
        """X-9 U7 (M-6): the gate's help alone is no run of the gate."""
        for command, stopped in (("tools/gate.sh --help", False), ("tools/gate.sh -h", False),
                                 ("python3 -B tools/gate.py --help", False), ("tools/gate.sh --work X", True),
                                 ("tools/gate.sh --help --work X", True), ("tools/gate.sh", True),
                                 ("tools/gate.sh --help; tools/gate.sh --quick", True)):  # fmt: skip
            with self.subTest(command=command):
                self.assertEqual(self.denied("t", "Bash", command=command), stopped)

    def test_changes_and_tells(self):
        out = self.pre("i", "Bash", command="tools/gate.sh --work X-9/U3", description="gate")
        self.assertEqual(out, {"hookEventName": "PreToolUse",  # the whole input, no decision (X9-52)
                               "updatedInput": {"command": "tools/gate.sh --work X-9/U3", "description": "gate",
                                                "timeout": 600000}})  # fmt: skip
        self.assertEqual(self.pre("parent", "Bash", command="python3 -B tools/bg.py wait /d", timeout=1000)["updatedInput"]
                         ["timeout"], 600000)  # fmt: skip
        for inp in ({"command": "tools/gate.sh", "timeout": 600000}, {"command": "python3 -B tools/bg.py run /d -- ls"}):
            self.assertIsNone(self.pre("i", "Bash", **inp))
        heredoc = self.pre("i", "Bash", command="python3 - a <<EOF\nprint(1)\nEOF")
        self.assertEqual(list(heredoc), ["hookEventName", "additionalContext"])
        self.assertIn("<<'EOF'", heredoc["additionalContext"])
        for line in ("python3 - <<'EOF'\nx\nEOF", 'python3 - <<"EOF"\nx\nEOF', "cat <<EOF\nx\nEOF", "python3 x.py <<< a"):
            with self.subTest(line=line):
                self.assertIsNone(self.pre("i", "Bash", command=line))

    def test_messages_and_crash_reports(self):
        for to in ("main", "onsa-impl [3fa]"):
            self.hook("PostToolUse", {"tool_name": "SendMessage", "tool_input": {"to": to, "message": "直して"}})
        files = sorted(p.name for p in (self.scratch / "messages").iterdir())
        self.assertEqual(files, ["001-main.md", "002-onsa-impl__3fa_.md"])
        self.assertEqual((self.scratch / "messages" / files[1]).read_text(), "from: main\nto: onsa-impl [3fa]\n\n直して\n")
        reports = Path(self.tmp.name) / "reports"
        reports.mkdir()
        (reports / "onsa-2026-10-01.ips").write_text("")
        bash = {"tool_name": "Bash", "tool_input": {"command": "ls"}, "agent_type": "onsa-impl"}
        with mock.patch.dict(os.environ, {"ONSA_CRASH_REPORTS": str(reports)}):
            self.assertIsNone(self.hook("PostToolUse", bash)[0])  # the first time only keeps what is there
            (reports / "onsa_cases-2026-10-18.ips").write_text("")
            (reports / "Python-2026-10-18.ips").write_text("")
            told = self.hook("PostToolUse", bash)[0]["additionalContext"]
            self.assertIn("onsa_cases-2026-10-18.ips", told)
            self.assertNotIn("onsa-2026-10-01", told)
            self.assertNotIn("Python-", told)
            self.assertIsNone(self.hook("PostToolUse", bash)[0])

    def test_session_start(self):
        root = Path(self.tmp.name) / "repo"
        (root / ".claude" / "agents").mkdir(parents=True)
        (root / ".claude" / "agents" / "onsa-x.md").write_text("x")
        git_in(root.parent, "init", "-q", "-b", "dev", str(root))
        git_in(root, "add", "-A")
        git_in(root, "commit", "-q", "-m", "a " + "long subject " * 40)
        git_in(root, "branch", "topic")
        for i in range(40):
            (root / f"new{i:02d}-{'x' * 60}.txt").write_text("")
        for source in ("startup", "compact"):
            out = self.hook("SessionStart", {"cwd": str(root), "source": source})[0]
            text = out["additionalContext"]
            self.assertEqual(out["hookEventName"], "SessionStart")
            self.assertLessEqual(len(text), claude_hook.SUMMARY_MAX)
            for part in ("git status --short: 40 件", "git worktree list: 1 件", "dev・main の外の枝: 1", "auto sweep: ",
                         "担当の定義: onsa-x", "docs due の文書: 0",
                         "parent: no commit from HEAD has a `Docs-Checked:` trailer"):
                self.assertIn(part, text)
            self.assertEqual(sum(x.startswith("?? new") for x in text.split("\n")), 10)

    def record(self, *largest):
        """A made-up record of an agent: one call per context size, a SubagentHandback after each."""
        path = Path(self.tmp.name) / "agent-a1.jsonl"
        with path.open("w") as f:
            for i, n in enumerate(largest):
                f.write(json.dumps({"type": "assistant", "message": {"id": f"m{i}", "model": "claude-opus-5-5",
                                                                     "usage": {"input_tokens": n}}}) + "\n")  # fmt: skip
                f.write(handback_line(f"報告 {i}"))
        return path

    def stop(self, path, later=(), delay=0.3):
        """SubagentStop of onsa-impl a1 on `path`, while a thread appends the chunks of `later` to it, one each
        `delay` seconds after the hook starts (X-11: the report reaches the record after the hook starts);
        (the hook's outputs, the seconds it took, the text of the file it saved or None)."""
        before = set((self.scratch / "handback").glob("*")) if (self.scratch / "handback").exists() else set()

        def append():
            for chunk in later:
                time.sleep(delay)
                with path.open("a") as f:
                    f.write(chunk)

        thread, start = threading.Thread(target=append), time.monotonic()
        thread.start()
        try:
            out = self.hook("SubagentStop", {"agent_type": "onsa-impl", "agent_id": "a1",
                                             "agent_transcript_path": str(path)})  # fmt: skip
        finally:
            took = time.monotonic() - start
            thread.join()
            time.sleep(0.01)  # the next call's lines are made later than this stop (timestamps in milliseconds)
        new = sorted(set((self.scratch / "handback").glob("*")) - before) if (self.scratch / "handback").exists() else []
        self.assertLessEqual(len(new), 1)
        return out, took, (new[0].read_text() if new else None)

    def test_subagent_stop(self):
        self.assertEqual(self.stop(self.record(1000, 250000))[0], (None, []))
        self.assertEqual(self.stop(self.record(1000, 2000, 310000))[0], (None, []))
        saved = sorted((self.scratch / "handback").iterdir())
        self.assertEqual([p.name for p in saved], ["onsa-impl-a1-001.md", "onsa-impl-a1-002.md"])
        first, second = (p.read_text().split("\n") for p in saved)
        self.assertEqual(first[0], "usage: calls 2, largest context 250,000, API-equivalent $1.0")
        self.assertEqual(first[1:], ["", "報告 1", ""])
        self.assertIn("largest context 310,000", second[0])
        self.assertIn("新しい担当へ（rules/leader.md 2.6）", second[0])
        self.assertEqual(second[1:], ["", "報告 2", ""])
        self.hook("SubagentStop", {"agent_type": "", "agent_transcript_path": str(self.record(1))})
        self.assertEqual(len(list((self.scratch / "handback").iterdir())), 2)  # Claude Code's own agents

    def test_subagent_stop_late_report(self):
        """X-11 (1): the report written after the hook starts, a line in two pieces, is saved with its call."""
        path = self.record()
        path.write_text(json.dumps({"type": "user", "message": {"content": "作業票"}}) + "\n")
        line = handback_line("遅れた報告")
        out, took, text = self.stop(path, [line[:20], line[20:]])
        self.assertEqual(out, (None, []))
        self.assertEqual(text.split("\n")[1:], ["", "遅れた報告", ""])
        self.assertLess(took, claude_hook.WAIT)  # it stops waiting when the report comes

    def test_subagent_stop_calls_again(self):
        """X-11 (2): the n-th call of an agent saves the n-th report, not the one before nor its copy in an
        `api-request-blob` line; (3): with no report within WAIT, the body says so and how to take it out."""
        path = self.record(1000)
        self.assertEqual(self.stop(path)[2].split("\n")[1:], ["", "報告 0", ""])
        prompt = json.dumps({"type": "user", "message": {"content": "段 2"}}) + "\n"
        copy = handback_line("報告 0", "api-request-blob")
        text = self.stop(path, [prompt + copy, handback_line("報告 1")])[2]
        self.assertEqual(text.split("\n")[1:], ["", "報告 1", ""])
        late = handback_line("報告 2")  # made before the stop, written after the hook gave up
        with mock.patch.object(claude_hook, "WAIT", 0.5):
            out, took, text = self.stop(path, [prompt + handback_line("報告 1", "api-request-blob")], delay=0.1)
        self.assertEqual(out, (None, []))
        self.assertGreaterEqual(took, 0.5)
        self.assertLess(took, 2)
        saved = sorted((self.scratch / "handback").iterdir())[-1]
        self.assertEqual(text.split("\n")[1:], [
            "", "（本文なし: 今の呼び出しの SubagentHandback が、0.5 秒待っても記録に無い。最後の文: None）",
            f"取り出し直す: python3 -B tools/handback.py save {path} {saved}", ""])  # fmt: skip
        with path.open("a") as f:
            f.write(late)
        self.assertEqual(quiet_out(handback.main, ["save", str(path), str(saved)]), (0, ["4 characters"]))
        self.assertEqual(saved.read_text(), "報告 2")  # the command in the body takes it out
        now = handback_line("報告 3")  # the next call: its stop waits for its own report, not the late one
        self.assertEqual(self.stop(path, [prompt + now])[2].split("\n")[1:], ["", "報告 3", ""])

    def test_subagent_stop_bad_records(self):
        """X-11 (4): a record that is not there, not a file, or not lines of the record: no exception out of the hook."""
        with mock.patch.object(claude_hook, "WAIT", 0.2):
            path = Path(self.tmp.name) / "agent-a1.jsonl"
            path.write_bytes(b"not json\n\xff\xfe\n[1]\n{\"type\": \"assistant\", \"message\": \"x\"}\n"
                             b"{\"type\": \"assistant\", \"message\": {\"content\": [1, {\"type\": \"text\"}]}}\n")
            out, took, text = self.stop(path)
            self.assertEqual(out, (None, []))
            self.assertIn("（本文なし: ", text)
            self.assertLess(took, 2)
            out, took, text = self.stop(Path(self.tmp.name))  # a directory
            self.assertEqual((out, text), ((None, []), None))
        self.assertRegex((self.scratch / "hooks" / "errors.log").read_text(), r"^SubagentStop: IsADirectoryError: ")

    def test_errors_do_nothing(self):
        out, lines = self.hook("SubagentStop", {"agent_type": "onsa-impl", "agent_id": "a1",
                                                "agent_transcript_path": str(Path(self.tmp.name) / "none.jsonl")})
        self.assertEqual((out, lines), (None, []))
        self.assertRegex((self.scratch / "hooks" / "errors.log").read_text(), r"^SubagentStop: FileNotFoundError: ")
        out, lines = self.hook("PreToolUse", {}, stdin="not json")
        self.assertIsNone(out)
        self.assertRegex(lines[0], r"^PreToolUse: JSONDecodeError: ")

    def test_help(self):
        for name, c in claude_hook.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertTrue(c.roles)
                self.assertRegex(c.example, rf"\| python3 -B tools/hooks/claude_hook\.py {name}$")
                code, lines = quiet_out(claude_hook.main, ["help", name])
                self.assertIn(f"  例:   {c.example}", lines)
        for role in repo.ROLES:
            code, lines = quiet_out(claude_hook.main, ["help", "--role", role])
            want = [n for n, c in claude_hook.COMMANDS.items() if role in c.roles]
            self.assertEqual((code, [x.split()[0] for x in lines if not x.startswith(" ")]), (0, want))
        names = list(claude_hook.COMMANDS)
        self.assertEqual([x.split()[0] for x in quiet_out(claude_hook.main, ["help"])[1][: len(names)]], names)


if __name__ == "__main__":
    unittest.main(verbosity=1)
