#!/usr/bin/env python3
"""The records of the agents of a session and of the session itself (rules/leader.md 1.2, 2.6, 2.8, 2.9).

Its commands are `save` and `usage` (COMMANDS, rules/tools.md 9.1); `handback.py help` shows them.
`usage` prints, for each agent, the calls, the largest context, the tokens read from and written to the prompt
cache, and an API-equivalent cost; with no agent, the same of the main session with its context now (the context
of its last call). A call reads its whole context again, so the largest context decides the cost of the next call
(2.6: hand over above 300,000 tokens, CONTEXT_BUDGET). The hook of SubagentStop (tools/hooks/claude_hook.py) uses
`report_in` and `stats`. The records are ~/.claude/projects/<the repository's project directory>/<session id>.jsonl
and, of its agents, <session id>/subagents/agent-<agent id>.jsonl.
"""
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import repo  # noqa: E402

PROJECT = Path.home() / ".claude" / "projects" / "-Users-centrevillage-projects-onsalang"
# The context of an agent above which its next unit or fix goes to a new agent (rules/budgets.md, the budget
# of an agent's context; rules/leader.md 2.6). The hook of SubagentStop (tools/hooks/claude_hook.py) says so.
CONTEXT_BUDGET = 300_000
REPORTS = "handback"  # the directory of the saved reports in the session's scratchpad (`report_prefix`)
# USD per million tokens: input, output, cache read. A cache write costs the input price times
# 1.25 (5 minutes) or 2 (1 hour). Prices of the API, used only to compare agents.
PRICES = {
    "claude-opus-5-5": (4, 20, 0.20),
    "claude-sonnet-5-5": (2, 10, 0.20),
    "claude-fable-5-1": (10, 50, 0.25),
}


def safe(name) -> str:
    """`name` as a piece of a file name: only letters, digits, `_`, `.` and `-` (no glob nor path)."""
    return re.sub(r"[^A-Za-z0-9_.-]", "_", name or "none")[:60]


def report_prefix(agent_type, agent_id) -> str:
    """The start of the names of an agent's saved reports in `<scratchpad>/REPORTS/` (the hook of SubagentStop
    adds the number; `work.py` looks for them before removing the agent's worktree)."""
    return f"{safe(agent_type)}-{safe(agent_id)}-"


def records(path: Path):
    """The lines of a record that are JSON objects (the hook of SubagentStop reads it: no line stops it)."""
    with path.open(encoding="utf-8", errors="replace") as f:
        for line in f:
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(d, dict):
                yield d


def report_in(d) -> "str | None":
    """The report of a line of a record: the message of its last SubagentHandback, else None. Only the agent's own
    lines (`type: "assistant"`) count: an `api-request-blob` line copies an earlier report into a later call (X-11)."""
    m = d.get("message") if isinstance(d, dict) and d.get("type") == "assistant" else None
    content = m.get("content") if isinstance(m, dict) else None
    message = None
    for block in content if isinstance(content, list) else ():
        if isinstance(block, dict) and block.get("type") == "tool_use" and block.get("name") == "SubagentHandback":
            message = block["input"].get("message") or json.dumps(block["input"], ensure_ascii=False)
    return message


def last_report(path) -> "str | None":
    """The message of the last SubagentHandback in the agent's record (its report), or None."""
    message = None
    for d in records(Path(path)):
        message = report_in(d) or message
    return message


def stats(path) -> dict:
    """The calls of the agent's record, its largest context, the tokens read from and written to the prompt
    cache, the output, the API-equivalent cost (`cost`, USD) and the context of the last call (`last`; a call with
    no context, as Claude Code's `<synthetic>` messages, does not count as the last)."""
    calls = {}
    for d in records(Path(path)):
        m = d.get("message")
        if isinstance(m, dict) and m.get("usage"):
            calls[m.get("id") or len(calls)] = (m.get("model"), m["usage"])
    s = dict(calls=len(calls), largest=0, read=0, write=0, out=0, cost=0.0, last=0)
    for model, u in calls.values():
        cc = u.get("cache_creation") or {}
        w1h, w5m = cc.get("ephemeral_1h_input_tokens", 0), cc.get("ephemeral_5m_input_tokens", 0)
        context = u.get("input_tokens", 0) + u.get("cache_read_input_tokens", 0) + u.get("cache_creation_input_tokens", 0)
        s["largest"] = max(s["largest"], context)
        s["last"] = context or s["last"]
        s["read"] += u.get("cache_read_input_tokens", 0)
        s["write"] += w1h + w5m
        s["out"] += u.get("output_tokens", 0)
        pi, po, pr = PRICES.get(model, PRICES["claude-opus-5-5"])
        s["cost"] += (u.get("input_tokens", 0) * pi + w1h * pi * 2 + w5m * pi * 1.25
                      + u.get("cache_read_input_tokens", 0) * pr + u.get("output_tokens", 0) * po) / 1e6
    return s


def save(args) -> int:
    message = last_report(args.jsonl)
    if message is None:
        print("no SubagentHandback in", args.jsonl)
        return 1
    Path(args.output).write_text(message, encoding="utf-8")
    print(len(message), "characters")
    return 0


def usage_line(name, s, now=False) -> str:
    """A line of `usage`; `now` adds the context of the last call (the main session's)."""
    return (f"{name}: calls {s['calls']}, " + (f"context now {s['last']:,}, " if now else "")
            + f"largest context {s['largest']:,}, cache read {s['read']:,}, "
            f"cache write {s['write']:,}, output {s['out']:,}, API-equivalent ${s['cost']:,.1f}")


def usage(args) -> int:
    if not args.agents:
        print(usage_line(args.session, stats(PROJECT / f"{args.session}.jsonl"), now=True))
    for agent in args.agents:
        print(usage_line(agent, stats(PROJECT / args.session / "subagents" / f"agent-{agent}.jsonl")))
    return 0


def save_args(p):
    p.add_argument("jsonl", help="the record of the agent (<session id>/subagents/agent-<agent id>.jsonl)")
    p.add_argument("output")


def usage_args(p):
    p.add_argument("session")
    p.add_argument("agents", nargs="*", metavar="agent", help="agent ids (none: the main session itself)")


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "save": C(save_args, save, ("parent",),
              "担当の記録の最後の SubagentHandback（報告）を <output> に書く",
              "フックが保存していない報告を取り出すとき（前のセッションの担当、`hooks/errors.log` に失敗があるとき）と、控えが「本文なし」のとき",
              "handback.py save ~/.claude/projects/-Users-centrevillage-projects-onsalang/<セッション ID>/subagents/agent-<担当の ID>.jsonl r.md"),
    "usage": C(usage_args, usage, ("parent",),
               "担当ごとに呼び出しの数・文脈の最大・キャッシュの読み書き・出力・API 換算を一行で出す。担当の ID が無ければ主のセッションのもの（今の文脈も）",
               "担当を新しい担当に引き継ぐかを決めるとき（動いている担当にも）、費用の目安を改めるとき、親の文脈が区切りを超えたかを見るとき",
               "handback.py usage <セッション ID> <担当の ID>"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("handback.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
