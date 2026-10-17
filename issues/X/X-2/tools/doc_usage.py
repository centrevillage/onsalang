"""How the parent and the agents read and edited the documents in W3, from the session transcripts.

usage: python3 -I doc_usage.py <projects dir> <since YYYY-MM-DD> <out.json>
One record per tool call: role (parent / agent type), session, agent, tool, the documents it names,
the action (read / edit / check / script / other), the characters of its input and of its result.
"""
import json
import re
import sys
from pathlib import Path

DOCS = [  # (category, pattern on a path or a command)
    ("spec", r"onsa-lang-spec-0\.3\.md"),
    ("plan", r"docs/implementation-tasks\.md"),
    ("rework", r"docs/rework-phase1\.md"),
    ("review", r"docs/review-impl-phase1\.md"),
    ("changes", r"docs/onsa-0\.3-changes\.md"),
    ("carryovers", r"docs/carryovers\.md"),
    ("rules", r"docs/(agent|leader)-rules\.md|\.claude/agents/"),
    ("gaps", r"docs/spec-gaps-[\w.-]*\.md"),
    ("tools-doc", r"docs/onsa-tools\.md"),
    ("other-docs", r"docs/(?!implementation-tasks|rework-phase1|review-impl-phase1|onsa-0\.3-changes|carryovers|agent-rules|leader-rules|spec-gaps|onsa-tools)[\w.-]+\.(md|toml)"),
    ("memory", r"/memory/|MEMORY\.md"),
    ("tickets", r"scratchpad/[^ \"']*(ticket|handback|design|todo_parent|reply|estimate|notes|step\d)[\w.-]*\.md"),
]
DOC_RES = [(c, re.compile(p)) for c, p in DOCS]
EDIT = re.compile(r"sed -i|perl -[pi]*i|write_text|\.write\(|open\([^)]*['\"][wa]['\"]|>>?\s*\S*(docs/|onsa-lang-spec)|\btee\b")
CHECK = re.compile(r"\.swp|\.sw\*|count\(['\"]\|['\"]\)|awk -F ?['\"]?\\?\|")
SCRIPT = re.compile(r"python3? [^|]*(<<|-c )|python3? -[BI]* ?\S+\.py")


def cats(text):
    return sorted({c for c, r in DOC_RES if r.search(text or "")})


def result_text(content):
    if isinstance(content, str):
        return content
    out = []
    for c in content or []:
        if isinstance(c, dict) and c.get("type") == "text":
            out.append(c.get("text", ""))
    return "\n".join(out)


def main():
    root, since, out = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
    recs = []
    files = [(f, "parent", f.stem, "parent", "") for f in sorted(root.glob("*.jsonl"))]
    for f in sorted(root.glob("*/subagents/*.jsonl")):
        mp = f.with_suffix(".meta.json")
        meta = json.loads(mp.read_text()) if mp.exists() else {}
        files.append((f, meta.get("agentType", "?"), f.parent.parent.name, f.stem.removeprefix("agent-"),
                      meta.get("description", "")))
    for f, role, session, agent, desc in files:
        calls = {}
        for line in f.open(errors="replace"):
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            t = d.get("timestamp") or ""
            if t < since:
                continue
            msg = d.get("message") or {}
            content = msg.get("content")
            if not isinstance(content, list):
                continue
            if d.get("type") == "assistant":
                for c in content:
                    if isinstance(c, dict) and c.get("type") == "tool_use":
                        calls[c.get("id")] = (c.get("name"), c.get("input") or {}, t)
            elif d.get("type") == "user":
                for c in content:
                    if not (isinstance(c, dict) and c.get("type") == "tool_result"):
                        continue
                    name, inp, ts = calls.pop(c.get("tool_use_id"), (None, {}, t))
                    if name is None:
                        continue
                    res = result_text(c.get("content"))
                    if name == "Bash":
                        cmd = inp.get("command", "")
                        target = cmd
                        if EDIT.search(cmd) and cats(cmd):
                            action = "edit"
                        elif CHECK.search(cmd):
                            action = "check"
                        else:
                            action = "read"
                        script = bool(SCRIPT.search(cmd))
                    elif name in ("Read", "Edit", "Write", "NotebookEdit"):
                        target = inp.get("file_path", "")
                        action = "read" if name == "Read" else "edit"
                        script = name == "Write" and target.endswith(".py") and bool(cats(inp.get("content", "")))
                        if script:
                            action = "script"
                    elif name in ("Grep", "Glob"):
                        target = (inp.get("path") or "") + " " + (inp.get("glob") or "")
                        action = "read"
                        script = False
                    else:
                        target, action, script = json.dumps(inp, ensure_ascii=False)[:300], "other", False
                    doc = cats(target if name != "Write" or not script else inp.get("content", ""))
                    recs.append({
                        "t": ts, "role": role, "session": session, "agent": agent, "desc": desc, "tool": name,
                        "docs": doc, "action": action, "script": script,
                        "in": len(json.dumps(inp, ensure_ascii=False)), "out": len(res),
                        "target": target[:240], "offset": inp.get("offset"), "limit": inp.get("limit"),
                        "longest_line": max((len(l) for l in res.split("\n")), default=0),
                        "long_chars": sum(len(l) for l in res.split("\n") if len(l) > 1000),
                        "cmd_key": (name, target[:240], inp.get("offset"), inp.get("limit")),
                    })
    out.write_text(json.dumps(recs, ensure_ascii=False))
    print(len(recs), "tool calls")


main()
