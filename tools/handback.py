#!/usr/bin/env python3
"""The records of the agents of a session (docs/leader-rules.md 2.6, 2.9).

    tools/handback.py save <agent jsonl> <output>
    tools/handback.py usage <session id> <agent id>...

save   writes the message of the agent's last SubagentHandback (its report) to <output>.
usage  prints, for each agent of the session, the calls, the largest context, the tokens read from
       and written to the prompt cache, and an API-equivalent cost. A call reads its whole context
       again, so the largest context decides the cost of the next call (2.6: hand over above
       300,000 tokens).
The records are under ~/.claude/projects/<the repository's project directory>/<session id>/subagents/.
"""
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
PROJECT = Path.home() / ".claude" / "projects" / "-Users-centrevillage-projects-onsalang"
# USD per million tokens: input, output, cache read. A cache write costs the input price times
# 1.25 (5 minutes) or 2 (1 hour). Prices of the API, used only to compare agents.
PRICES = {
    "claude-opus-5-5": (4, 20, 0.20),
    "claude-sonnet-5-5": (2, 10, 0.20),
    "claude-fable-5-1": (10, 50, 0.25),
}


def records(path: Path):
    for line in path.open(encoding="utf-8"):
        try:
            yield json.loads(line)
        except json.JSONDecodeError:
            continue


def save(jsonl: str, output: str) -> int:
    message = None
    for d in records(Path(jsonl)):
        content = (d.get("message") or {}).get("content")
        if not isinstance(content, list):
            continue
        for block in content:
            if block.get("type") == "tool_use" and block.get("name") == "SubagentHandback":
                message = block["input"].get("message") or json.dumps(block["input"], ensure_ascii=False)
    if message is None:
        print("no SubagentHandback in", jsonl)
        return 1
    Path(output).write_text(message, encoding="utf-8")
    print(len(message), "characters")
    return 0


def usage(session: str, agents: list) -> int:
    for agent in agents:
        path = PROJECT / session / "subagents" / f"agent-{agent}.jsonl"
        calls = {}
        for d in records(path):
            m = d.get("message")
            if isinstance(m, dict) and m.get("usage"):
                calls[m.get("id") or len(calls)] = (m.get("model"), m["usage"])
        largest = read = write = out = 0
        cost = 0.0
        for model, u in calls.values():
            cc = u.get("cache_creation") or {}
            w1h, w5m = cc.get("ephemeral_1h_input_tokens", 0), cc.get("ephemeral_5m_input_tokens", 0)
            context = u.get("input_tokens", 0) + u.get("cache_read_input_tokens", 0) + u.get("cache_creation_input_tokens", 0)
            largest = max(largest, context)
            read += u.get("cache_read_input_tokens", 0)
            write += w1h + w5m
            out += u.get("output_tokens", 0)
            pi, po, pr = PRICES.get(model, PRICES["claude-opus-5-5"])
            cost += (u.get("input_tokens", 0) * pi + w1h * pi * 2 + w5m * pi * 1.25
                     + u.get("cache_read_input_tokens", 0) * pr + u.get("output_tokens", 0) * po) / 1e6
        print(f"{agent}: calls {len(calls)}, largest context {largest:,}, cache read {read:,}, "
              f"cache write {write:,}, output {out:,}, API-equivalent ${cost:,.1f}")
    return 0


def main() -> int:
    if len(sys.argv) == 4 and sys.argv[1] == "save":
        return save(sys.argv[2], sys.argv[3])
    if len(sys.argv) >= 4 and sys.argv[1] == "usage":
        return usage(sys.argv[2], sys.argv[3:])
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
