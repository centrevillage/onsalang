"""Document usage of one session (parent + finished subagents) on the layout after X-2.

usage: python3 -I usage38.py <projects dir> <session id> [<agent id to skip>...]
The same measures as issues/X/X-2/step1_eval.md (chars of a call's input and result), on the new paths.
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

DOCS = [
    ("spec", r"spec/[\w./-]+\.(md|toml)"),
    ("decisions", r"decisions/"),
    ("issues", r"issues/(R|RF|X)/"),
    ("tasks", r"tasks/"),
    ("rules", r"rules/[\w.-]+\.md|\.claude/agents/|CLAUDE\.md"),
    ("design", r"design/"),
    ("readme", r"(^|[/ ])README\.md"),
    ("pending", r"tests/pending\.toml|tests/fuzz/allowed\.toml"),
    ("history", r"history/"),
    ("memory", r"/memory/|MEMORY\.md"),
    ("tickets", r"scratchpad/[^ \"']*(ticket|handback|design|todo_parent|reply|decided|notes|memo)[\w.-]*\.md"),
]
DOC_RES = [(c, re.compile(p)) for c, p in DOCS]
REPO_DOCS = {"spec", "decisions", "issues", "tasks", "rules", "design", "readme", "pending", "history"}
EDIT = re.compile(r"sed -i|perl -[pi]*i|write_text|\.write\(|open\([^)]*['\"][wa]['\"]|>>?\s*\S*(spec/|decisions/|issues/|rules/|tasks/|design/)|\btee\b|\bcp\b[^|;]*(issues|decisions|spec|rules)/")
STD_TOOL = re.compile(r"tools/(docs|take|handback|bg|pending|ignores|gate)\.(py|sh)|tools/gate\.sh")
ADHOC = re.compile(r"python3? [^|]*(<<|-c )|python3? -[BI]* ?(/private|/tmp|\S*scratchpad)\S*\.py")
DOCS_SUB = re.compile(r"tools/docs\.py (\w+)")


def cats(text):
    return {c for c, r in DOC_RES if r.search(text or "")}


def result_text(content):
    if isinstance(content, str):
        return content
    return "\n".join(c.get("text", "") for c in content or [] if isinstance(c, dict) and c.get("type") == "text")


def read_method(name, inp):
    if name == "Read":
        return "Read(range)" if inp.get("offset") or inp.get("limit") else "Read(whole)"
    if name == "Grep":
        return "Grep"
    cmd = inp.get("command", "")
    if STD_TOOL.search(cmd):
        return "std tool"
    if ADHOC.search(cmd):
        return "ad hoc python"
    head = cmd.strip().split("|")[0]
    for k, pat in [("grep", r"\b(grep|rg)\b"), ("sed/head/tail", r"\b(sed -n|head|tail|awk)\b"), ("cat", r"\bcat\b")]:
        if re.search(pat, head):
            return k
    return "other shell"


def main():
    root, session, skip = Path(sys.argv[1]), sys.argv[2], set(sys.argv[3:])
    files = [(root / f"{session}.jsonl", "parent", "parent")]
    for f in sorted((root / session / "subagents").glob("*.jsonl")):
        aid = f.stem.removeprefix("agent-")
        if aid in skip:
            continue
        meta = json.loads(f.with_suffix(".meta.json").read_text())
        files.append((f, meta.get("agentType", "?").removeprefix("onsa-"), aid))
    tot = Counter(); docread = Counter(); docedit = Counter(); ticketedit = Counter()
    methods = defaultdict(Counter)  # repo doc reads: method -> chars
    nmeth = defaultdict(Counter)
    edits = defaultdict(Counter)    # role -> edit kind -> count
    docs_sub = Counter(); adhoc_files = defaultdict(set); checks = Counter()
    rules_whole = Counter()
    for f, role, aid in files:
        calls = {}
        for line in f.open(errors="replace"):
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            msg = d.get("message") or {}
            content = msg.get("content")
            if not isinstance(content, list):
                continue
            if d.get("type") == "assistant":
                for c in content:
                    if isinstance(c, dict) and c.get("type") == "tool_use":
                        calls[c.get("id")] = (c.get("name"), c.get("input") or {})
                continue
            for c in content:
                if not (isinstance(c, dict) and c.get("type") == "tool_result"):
                    continue
                name, inp = calls.pop(c.get("tool_use_id"), (None, {}))
                if name is None:
                    continue
                res = result_text(c.get("content"))
                size = len(json.dumps(inp, ensure_ascii=False)) + len(res)
                tot[role] += size
                if name == "Bash":
                    target = inp.get("command", "")
                    for m in DOCS_SUB.finditer(target):
                        docs_sub[(role if role == "parent" else "agents", m.group(1))] += 1
                    if ADHOC.search(target):
                        for m in re.finditer(r"(\S+scratchpad\S*\.py)", target):
                            adhoc_files[role].add(m.group(1).rsplit("/", 1)[-1])
                    if re.search(r"docs\.py (swaps|check)|\.swp", target):
                        checks[role] += 1
                    is_edit = bool(EDIT.search(target))
                elif name in ("Read", "Edit", "Write", "NotebookEdit"):
                    target = inp.get("file_path", "")
                    is_edit = name != "Read"
                elif name in ("Grep", "Glob"):
                    target = (inp.get("path") or "") + " " + (inp.get("glob") or "") + " " + (inp.get("pattern") or "")
                    is_edit = False
                else:
                    continue
                cs = cats(target)
                if not cs:
                    continue
                repo = cs & REPO_DOCS
                if is_edit:
                    if repo:
                        docedit[role] += size
                        kind = name if name != "Bash" else ("shell python" if "python" in target else "shell other")
                        edits[role][kind] += 1
                    elif "tickets" in cs or "memory" in cs:
                        ticketedit[role] += size
                else:
                    docread[role] += size
                    if repo:
                        mth = read_method(name, inp)
                        methods[role if role == "parent" else "agents"][mth] += len(res)
                        nmeth[role if role == "parent" else "agents"][mth] += 1
                        if "rules" in cs and name == "Read" and not (inp.get("offset") or inp.get("limit")):
                            rules_whole[role] += 1
    print("== chars by role (total, doc read %, doc edit %, ticket/memory edit %)")
    for r in sorted(tot, key=lambda r: -tot[r]):
        t = tot[r]
        print(f"{r:8} {t/1e6:6.2f}M  read {100*docread[r]/t:4.1f}%  edit {100*docedit[r]/t:4.1f}%  tickets {100*ticketedit[r]/t:4.1f}%")
    print("== repo doc reads by method (calls, result chars)")
    for who in ("parent", "agents"):
        tc = sum(methods[who].values()) or 1
        print(who, ", ".join(f"{m} {nmeth[who][m]} ({100*v/tc:.0f}%)" for m, v in methods[who].most_common()))
    print("== repo doc edits by kind (count)")
    for r, c in edits.items():
        print(r, dict(c))
    print("== docs.py subcommands", dict(docs_sub))
    print("== ad hoc scratchpad scripts run", {r: sorted(s) for r, s in adhoc_files.items()})
    print("== pre-edit checks (swaps/check)", dict(checks))
    print("== whole reads of rules files", dict(rules_whole))


main()
