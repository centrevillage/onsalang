"""Collect every gate summary from the session transcripts (parent and agents).

usage: python3 -I gate_runs.py <projects dir> <out.json>
Each run: time, session, agent (type, description), command, mode (full/quick/work/stage-end),
steps [(status, name, seconds, note)], verdict, and the tail of the failing items' sections.
"""
import json
import re
import sys
from pathlib import Path

ROW = re.compile(r"^\s+(PASS|FAIL|SKIPPED|INFO|PENDING|XFAIL|LISTED|\w+)\s+([a-z][a-z0-9-]*)\s+([\d.]+)s\s*(.*)$")


def texts(content):
    if isinstance(content, str):
        yield content
    elif isinstance(content, list):
        for c in content:
            if isinstance(c, dict):
                if c.get("type") == "text":
                    yield c.get("text", "")
                elif c.get("type") == "tool_result":
                    yield from texts(c.get("content"))


def sections(text):
    """name -> body of each `=== name: argv` section before the summary."""
    out = {}
    parts = re.split(r"\n=== ([a-z][a-z0-9-]*): [^\n]*\n", "\n" + text)
    for i in range(1, len(parts) - 1, 2):
        out[parts[i]] = parts[i + 1].split("\n=== summary")[0]
    return out


def parse(text):
    runs = []
    for m in re.finditer(r"=== summary\n", text):
        rows, verdict = [], None
        for line in text[m.end():].split("\n"):
            r = ROW.match(line)
            if r:
                rows.append((r[1], r[2], float(r[3]), r[4]))
                continue
            if line.startswith("gate"):
                verdict = line.strip()
                break
            if line.startswith("  "):
                continue
            break
        if rows:
            runs.append((rows, verdict, text[: m.start()]))
    return runs


def main():
    root, out = Path(sys.argv[1]), Path(sys.argv[2])
    seen, runs = set(), []
    for f in sorted(root.glob("*.jsonl")) + sorted(root.glob("*/subagents/*.jsonl")):
        if f.parent.name == "subagents":
            session = f.parent.parent.name
            agent = f.stem.removeprefix("agent-")
            meta_p = f.with_suffix(".meta.json")
            meta = json.loads(meta_p.read_text()) if meta_p.exists() else {}
            atype, desc = meta.get("agentType", "?"), meta.get("description", "")
        else:
            session, agent, atype, desc = f.stem, "parent", "parent", ""
        commands = {}
        for line in f.open(encoding="utf-8", errors="replace"):
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            msg = d.get("message") or {}
            content = msg.get("content")
            if isinstance(content, list):
                for c in content:
                    if isinstance(c, dict) and c.get("type") == "tool_use":
                        commands[c.get("id")] = (c.get("input") or {}).get("command", "")
            if d.get("type") != "user" or not isinstance(content, list):
                continue
            for c in content:
                if not (isinstance(c, dict) and c.get("type") == "tool_result"):
                    continue
                for t in texts(c.get("content")):
                    if "=== summary" not in t:
                        continue
                    for rows, verdict, before in parse(t):
                        key = (session, agent, tuple(rows))
                        if key in seen:
                            continue
                        seen.add(key)
                        cmd = commands.get(c.get("tool_use_id"), "")
                        secs = sections(before)
                        fails = {n: secs.get(n, "")[-1500:] for s, n, _, _ in rows if s == "FAIL"}
                        names = {n for _, n, _, _ in rows}
                        mode = "quick" if "fuzz" not in names else ("stage-end" if any(n == "fuzz-deep" and s != "SKIPPED" for s, n, _, _ in rows) else "full")
                        runs.append({
                            "time": d.get("timestamp", ""), "session": session, "agent": agent, "type": atype,
                            "desc": desc, "cwd": d.get("cwd", ""), "cmd": cmd[:300], "mode": mode,
                            "verdict": verdict, "total": round(sum(r[2] for r in rows), 1),
                            "steps": rows, "fails": fails,
                        })
    runs.sort(key=lambda r: r["time"])
    out.write_text(json.dumps(runs, ensure_ascii=False, indent=1))
    print(f"{len(runs)} runs -> {out}")


main()
