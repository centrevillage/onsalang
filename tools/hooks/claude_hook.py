#!/usr/bin/env python3
"""The hooks of Claude Code (X-9, X9-42 to X9-61): one tool, one subcommand per event.

    python3 -B tools/hooks/claude_hook.py PreToolUse | PostToolUse | SessionStart | SubagentStop  < the hook's JSON
    python3 -B tools/hooks/claude_hook.py help [--role ROLE] [EVENT]

The settings (`.claude/settings.json`, the user's) run each event's command; the hook's JSON comes on stdin, and
what Claude Code reads (https://code.claude.com/docs/en/hooks) goes to stdout as one JSON object, or nothing.
The role is `agent_type` looked up in `repo.ROLES` (no `agent_type`: the main session, the parent).
Only a stop prints `permissionDecision` (`deny`); the other outputs leave the permission to the rules.
The exit is always 0: an error does nothing for that event and writes one line to
`<scratchpad_dir>/hooks/errors.log` (stderr when the input has no `scratchpad_dir`).
The files go under the session's `scratchpad_dir`: `messages/`, `handback/`, `hooks/`. The crash reports
are read from $ONSA_CRASH_REPORTS (default ~/Library/Logs/DiagnosticReports; the self-tests change it).
"""
import json
import os
import re
import subprocess
import sys
import traceback
from pathlib import Path

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TOOLS))
import repo  # noqa: E402

NO_GATE = ("t", "b", "advisor", "gap", "docs")  # rules/checks.md 4: the roles that never run the gate
NO_BUILD = ("advisor", "gap")  # nor build, test, run (they use the parent's binaries)
LONG = 600000  # the Bash timeout of the gate and of `bg.py wait` (rules/checks.md 4.1, rules/common.md 1.8)
CRATE_SRC = re.compile(r"(^|/)crates/[^/]+/src(/|$)")  # what the test role does not read (X9-46)
PATHS = {"Read": ("file_path",), "Grep": ("path", "glob"), "Glob": ("path", "pattern")}  # the inputs that are paths
HEREDOC = re.compile(r"(?<!<)<<-?[ \t]*[A-Za-z_]")  # a heredoc whose word is not quoted (X9-49)
DUE_DOC = re.compile(r"^parent: \S+: .* after the docs check ")  # a document of `docs.py due` (counted, not listed)
SUMMARY_MAX, LOG_WIDTH = 2000, 100  # the state of SessionStart (X9-56) and the width of a line of its log
WRAPPERS = ("python3", "python", "sh", "bash", "zsh", "exec", "env", "time", "nohup", "command", "{", "!",
            "then", "do", "else", "elif", "if", "while")  # fmt: skip


def role_of(event):
    """The role of `repo.ROLES` the hook fires in: "parent" without `agent_type`, None for another agent."""
    kind = event.get("agent_type")
    return "parent" if not kind else next((r for r, d in repo.ROLES.items() if d == kind), None)


def scratch(event, sub):
    """`<scratchpad_dir>/<sub>`, made; None when the input has no scratchpad."""
    if not event.get("scratchpad_dir"):
        return None
    d = Path(event["scratchpad_dir"]) / sub
    d.mkdir(parents=True, exist_ok=True)
    return d


def new_file(d, prefix, suffix=""):
    """`<d>/<prefix><NNN><suffix>.md` with the next number from 001 among the files of `prefix`, made at once
    (two hooks never take one name)."""
    n = sum(1 for p in d.iterdir() if p.name.startswith(prefix))
    while True:
        n += 1
        path = d / f"{prefix}{n:03d}{suffix}.md"
        try:
            path.open("x").close()
            return path
        except FileExistsError:
            continue


def safe(name):
    return re.sub(r"[^A-Za-z0-9_.-]", "_", name or "none")[:60]


# ---------------------------------------------------------------- the shell line


def split_line(line):
    """The simple commands of a shell line, each its words with the quotes taken off: split at `;`, `&`, `|`,
    newlines, parentheses, backquotes and `$(` outside the quotes."""
    cmds, words, cur, quote, i = [], [], None, None, 0
    while i < len(line):
        ch = line[i]
        if quote:
            if ch == quote:
                quote = None
            elif ch == "\\" and quote == '"' and i + 1 < len(line):
                i += 1
                cur += line[i]
            else:
                cur += ch
        elif ch in "'\"":
            quote, cur = ch, cur or ""
        elif ch == "\\" and i + 1 < len(line):
            i += 1
            cur = (cur or "") + line[i]
        elif ch in " \t;&|\n()`" or line.startswith("$(", i):
            if cur is not None:
                words.append(cur)
            cur = None
            if ch not in " \t":
                cmds.append(words)
                words, i = [], i + line.startswith("$(", i)
        else:
            cur = (cur or "") + ch
        i += 1
    return cmds + [words + ([cur] if cur is not None else [])]


def programs(line):
    """Each simple command of `line` from its program on: assignments, wrappers (`python3`, `env`, `then`, …)
    and the options right after a wrapper are dropped; `bg.py run DIR -- CMD…` gives CMD… as a command too."""
    out, todo = [], split_line(line)
    while todo:
        w, i = todo.pop(0), 0
        while i < len(w) and (re.match(r"[A-Za-z_][A-Za-z0-9_]*=", w[i]) or w[i] in WRAPPERS):
            i += 1
            while w[i - 1] in WRAPPERS and i < len(w) and w[i].startswith("-"):
                i += 1  # `python3 -B`, `env -i`
        w = w[i:]
        if w and name(w[0]) == "bg.py" and "--" in w:
            todo.insert(0, w[w.index("--") + 1:])
            w = w[: w.index("--")]
        if w:
            out.append(w)
    return out


def name(word):
    return word.rsplit("/", 1)[-1]


def runs_gate(cmds):
    return any(name(w[0]) in ("gate.sh", "gate.py") for w in cmds)


def runs_build(cmds):
    return any(name(w[0]) == "cargo" and next((x for x in w[1:] if x[:1] not in "-+"), None) in
               ("build", "test", "run", "clippy") for w in cmds)  # fmt: skip


def waits(cmds):
    return any(name(w[0]) == "bg.py" and w[1:2] == ["wait"] for w in cmds)


def cd_into_worktree(cmds, cwd):
    for w in cmds:
        if w[0] == "cd":
            target = next((x for x in w[1:] if not x.startswith("-")), None)
            if target is None:
                continue  # `cd` alone goes home
            path = os.path.normpath(os.path.join(cwd or "/", os.path.expanduser(target)))
            if "/.claude/worktrees/" in path + "/":
                return True
    return False


# ---------------------------------------------------------------- the events


def stop_reason(event, role):
    """Why the call is stopped (X9-42, 43, 46, 47, 50), with what to do instead; None: not stopped."""
    tool, inp = event.get("tool_name"), event.get("tool_input") or {}
    if tool in ("Agent", "Task") and inp.get("model") and str(inp.get("subagent_type", "")).startswith("onsa-"):
        return ("担当のモデルは定義の frontmatter で決まる（rules/process.md 8.6）。"
                "Agent の入力から `model` を外して呼ぶ")  # fmt: skip
    if role == "t" and tool in PATHS:
        parts = [str(inp.get(k) or "") for k in PATHS[tool]]
        if CRATE_SRC.search("/".join(parts)):  # Glob's path and pattern, Grep's path and glob: one path
            return ("テストの担当は実装（`crates/*/src/`）を読まない（rules/process.md 8.5）。"
                    "仕様（spec/）と CLI の使い方（`onsa --help`）から書き、事例は `crates/*/tests/` と `tests/` を読む")
    if tool != "Bash":
        return None
    cmds = programs(str(inp.get("command", "")))
    if role == "parent" and cd_into_worktree(cmds, event.get("cwd")):
        return ("親は担当の作業ツリーに cd しない（rules/leader.md 3.1）。"
                "`git -C <経路>` と絶対パスで読み、道具の作業ディレクトリは引数で渡す")  # fmt: skip
    if any(name(w[0]) == "fuzz.py" and "--deep" in w for w in cmds):
        return "fuzz の `--deep` はどの役割も回さない（rules/checks.md 4.2）。`--deep` を外して回す"
    if role in NO_GATE and runs_gate(cmds):
        return (f"役割 {role} は gate を回さない（rules/checks.md 4 章の表）。"
                "表の「作業の途中」の確かめを使い、gate が要るときは報告に書いて親に頼む")  # fmt: skip
    if role in NO_BUILD and runs_build(cmds):
        return (f"役割 {role} はビルドとテストを回さない（rules/checks.md 4 章の表）。"
                "親が渡すバイナリを使い、要るものは報告に書いて親に頼む")  # fmt: skip
    return None


def pre_tool_use(event):
    out = {"hookEventName": "PreToolUse"}
    reason = stop_reason(event, role_of(event))
    if reason:
        return {"hookSpecificOutput": {**out, "permissionDecision": "deny", "permissionDecisionReason": reason}}
    inp = event.get("tool_input") or {}
    if event.get("tool_name") != "Bash":
        return None
    line = str(inp.get("command", ""))
    cmds = programs(line)
    if (runs_gate(cmds) or waits(cmds)) and not (isinstance(inp.get("timeout"), int) and inp["timeout"] >= LONG):
        out["updatedInput"] = {**inp, "timeout": LONG}  # the whole input (X9-52); no permissionDecision
    if HEREDOC.search(line) and "python" in line:
        out["additionalContext"] = ("引用符の無いヒアドキュメントは、本文のバッククォートと `$` をシェルで展開する。"
                                    "Python を渡すときは `<<'EOF'` と囲み、引数は sys.argv で渡す（rules/common.md 1.5）")
    return {"hookSpecificOutput": out} if len(out) > 1 else None


def post_tool_use(event):
    tool, inp = event.get("tool_name"), event.get("tool_input") or {}
    if tool == "SendMessage":  # X9-54
        if event.get("scratchpad_dir"):
            path = new_file(scratch(event, "messages"), "", f"-{safe(inp.get('to'))}")
            sender = event.get("agent_type") or "main"
            path.write_text(f"from: {sender}\nto: {inp.get('to')}\n\n{inp.get('message', '')}\n", encoding="utf-8")
        return None
    if tool != "Bash" or not event.get("scratchpad_dir"):
        return None
    reports = Path(os.environ.get("ONSA_CRASH_REPORTS") or Path.home() / "Library/Logs/DiagnosticReports")
    now = sorted(p.name for p in reports.glob("onsa*.ips")) if reports.is_dir() else []
    seen_file = scratch(event, "hooks") / "crash-reports-seen"
    first = not seen_file.exists()
    seen = set() if first else set(seen_file.read_text(encoding="utf-8").split("\n"))
    new = [n for n in now if n not in seen]
    if new or first:
        seen_file.write_text("\n".join(sorted(seen | set(now))), encoding="utf-8")
    if first or not new:
        return None
    return {"hookSpecificOutput": {"hookEventName": "PostToolUse", "additionalContext": (
        f"onsa のクラッシュの報告が新しく出た（{reports}）: {', '.join(new)}。"
        "どのコマンドで出たかを確かめ、報告に書く（rules/common.md 3.1）")}}  # fmt: skip


def run(args, cwd, ok=(0,)):
    """The stdout of `args`, or a line that says why there is none."""
    try:
        r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as e:
        return f"({args[0]}: {e})"
    if r.returncode in ok:
        return r.stdout.rstrip()  # the leading spaces of `git status --short` stay
    return f"({' '.join(args[:3])}: exit {r.returncode} {r.stderr.strip()[:200]})"


def state(cwd):
    """The state at the start of a session and after a compaction (X9-56); the summary lines are the tools'."""
    import gate_runs
    import gate_steps

    status = run(["git", "status", "--short"], cwd).splitlines()
    branches = [b for b in run(["git", "branch", "--format=%(refname:short)"], cwd).splitlines()
                if b not in ("dev", "main")]  # fmt: skip
    due = run([sys.executable, "-B", str(TOOLS / "docs.py"), "due", "--root", cwd], cwd, (0, 3)).splitlines()
    main = repo.main_tree(cwd) or Path(cwd)
    try:
        auto = gate_runs.auto_line(main, gate_runs.read_history(main)[0], gate_steps.SHARDS)
    except Exception as e:  # noqa: BLE001 (the line says it; the rest of the state still helps)
        auto = f"auto sweep: cannot read the history of the main tree ({e})"
    agents = sorted(p.stem for p in (Path(cwd) / ".claude" / "agents").glob("onsa-*.md"))
    trees = [" ".join(x.split()) for x in run(["git", "worktree", "list"], cwd).splitlines()]
    parts = ["状態（tools/hooks/claude_hook.py SessionStart）", "git log --oneline -3:",
             *[x[:LOG_WIDTH] for x in run(["git", "log", "--oneline", "-3"], cwd).splitlines()],
             f"git status --short: {len(status)} 件", *status[:10],
             f"git worktree list: {len(trees)} 件", *trees[:10],
             f"dev・main の外の枝: {len(branches)}",
             *[x for x in due if not DUE_DOC.match(x)], f"docs due の文書: {sum(bool(DUE_DOC.match(x)) for x in due)}",
             auto, f"core.hooksPath: {run(['git', 'config', 'core.hooksPath'], cwd, (0, 1)) or '(無し)'}",
             f"担当の定義: {' '.join(agents)}"]  # fmt: skip
    text = "\n".join(parts)
    return text if len(text) <= SUMMARY_MAX else text[: SUMMARY_MAX - 1] + "…"


def session_start(event):
    cwd = event.get("cwd") or os.environ.get("CLAUDE_PROJECT_DIR") or os.getcwd()
    return {"hookSpecificOutput": {"hookEventName": "SessionStart", "additionalContext": state(cwd)}}


def subagent_stop(event):
    """X9-59, X9-61: the report and the usage of the agent, in `handback/`. No output of SubagentStop reaches the
    parent (`additionalContext` and `decision: block` keep the subagent running), so the usage is the head line."""
    import handback

    kind, record = event.get("agent_type"), event.get("agent_transcript_path")
    if not kind or not record or not event.get("scratchpad_dir"):
        return None  # Claude Code's own agents have no agent_type
    record = Path(record).expanduser()
    report, s = handback.last_report(record), handback.stats(record)
    head = (f"usage: calls {s['calls']}, largest context {s['largest']:,}, API-equivalent ${s['cost']:,.1f}"
            + (f"; 担当の文脈の予算（{handback.CONTEXT_BUDGET:,}）を超えた: 次の単位か直しは新しい担当へ（rules/leader.md 2.6）"
               if s["largest"] > handback.CONTEXT_BUDGET else ""))  # fmt: skip
    body = report if report is not None else f"（SubagentHandback が無い。最後の文: {event.get('last_assistant_message')!r}）"
    path = new_file(scratch(event, "handback"), f"{safe(kind)}-{safe(event.get('agent_id'))}-")
    path.write_text(f"{head}\n\n{body}\n", encoding="utf-8")
    return None


# ---------------------------------------------------------------- the subcommands


def hook(fn):
    """The run of an event: the JSON of stdin to `fn`, its output to stdout; any error logged, exit 0."""

    def go(args):
        event = {}
        try:
            event = json.loads(args.stdin.read() or "{}")
            out = fn(event)
            if out:
                print(json.dumps(out, ensure_ascii=False))
        except Exception as e:  # noqa: BLE001 (a hook never stops the session for its own error)
            line = f"{args.cmd}: {type(e).__name__}: {e} ({traceback.extract_tb(e.__traceback__)[-1].lineno})\n"
            try:
                with (scratch(event, "hooks") / "errors.log").open("a", encoding="utf-8") as f:
                    f.write(line)
            except Exception:  # noqa: BLE001 (no scratchpad, or not a dict)
                sys.stderr.write(line)
        return 0

    return go


EVERY = tuple(repo.ROLES)
EX = "echo '{\"tool_name\":\"Bash\",\"tool_input\":{\"command\":\"tools/gate.sh --work X-9/U3\"}}' | python3 -B "
C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "PreToolUse": C(lambda p: None, hook(pre_tool_use), EVERY,
                    "道具の呼び出しの前に、止めるもの（担当の作業ツリーへの cd、担当の model、fuzz --deep、役割の gate とビルド、"
                    "テストの担当の crates/*/src）を止め、gate と bg.py wait の timeout を 600000 にし、引用符の無いヒアドキュメントを知らせる",
                    "設定の PreToolUse（matcher `Bash|Agent|Read|Grep|Glob`）が呼ぶ。止めた理由の文に代わりにすることがある",
                    EX + "tools/hooks/claude_hook.py PreToolUse"),
    "PostToolUse": C(lambda p: None, hook(post_tool_use), EVERY,
                     "SendMessage の宛先と本文を scratchpad の messages/ に控え、Bash の後に onsa のクラッシュの報告が新しく出たら知らせる",
                     "設定の PostToolUse（matcher `Bash|SendMessage`）が呼ぶ。控えは `<scratchpad>/messages/<連番>-<宛先>.md`",
                     "echo '{\"tool_name\":\"SendMessage\",\"tool_input\":{\"to\":\"main\",\"message\":\"…\"},"
                     "\"scratchpad_dir\":\"/tmp/s\"}' | python3 -B tools/hooks/claude_hook.py PostToolUse"),
    "SessionStart": C(lambda p: None, hook(session_start), ("parent",),
                      "セッションの始めと圧縮の後に、状態の要約（git、作業ツリー、枝、docs due、網羅の検査、hooksPath、担当の定義）を文脈に足す",
                      "設定の SessionStart（matcher `startup|resume|compact`）が呼ぶ。2,000 字以内",
                      "echo '{\"cwd\":\"/Users/centrevillage/projects/onsalang\"}' | python3 -B tools/hooks/claude_hook.py SessionStart"),
    "SubagentStop": C(lambda p: None, hook(subagent_stop), ("parent",),
                      "担当が止まるたびに、報告（最後の SubagentHandback）と呼び出しの数・文脈の最大・API 換算を scratchpad の handback/ に保存する",
                      "設定の SubagentStop が呼ぶ。`<scratchpad>/handback/<agent_type>-<agent_id>-<連番>.md` の頭の行が使用量で、"
                      "文脈の予算を超えたら引き継ぎの目安を添える",
                      "echo '{\"agent_type\":\"onsa-impl\",\"agent_id\":\"a1\",\"agent_transcript_path\":\"…/agent-a1.jsonl\","
                      "\"scratchpad_dir\":\"/tmp/s\"}' | python3 -B tools/hooks/claude_hook.py SubagentStop"),
}  # fmt: skip


def main(argv=None, stdin=None):
    args = repo.parse_command("claude_hook.py", __doc__.split("\n")[0], COMMANDS, argv,
                              lambda p: p.set_defaults(stdin=stdin or sys.stdin))  # fmt: skip
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
