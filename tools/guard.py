#!/usr/bin/env python3
"""Run a command under a limit of memory and of time on all of its processes (rules/common.md 3).

Its command is `run` (COMMANDS, rules/tools.md 9.1); `guard.py help` shows it.
`run <max_gb> <max_seconds> -- <command>…` starts the command in a process group of its own (a session of its
own, as tools/bg.py does) and every 0.05 s sums the resident memory of every process of the group (`ps -A -o
pgid=,rss=`: the `ps` of macOS selects no group), so a command wrapped in another (`/usr/bin/time -l onsa …`,
`sh -c …`) is measured whole, its children with it. Past max_gb or max_seconds it sends SIGKILL to the group
(SIGKILL makes no crash report, rules/common.md 3.1); when the command ends, it kills what is left of the group.
It prints the output of the command (the first 4000 characters of each stream), then a last line
`guard: exit <code> peak <MB> MB <seconds> s`, with `killed (memory)` or `killed (time)` when it stopped it
(the code is then -9); its own exit is 0. A limit of the system (setrlimit) is not used: macOS does not hold
the resident memory to it, and an allocation that fails aborts with a crash report.
"""
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

POLL = 0.05  # seconds between two looks at the group
SHOWN = 4000  # characters of each stream printed


def group_rss_kb(pgid):
    """The resident memory in KB of all the processes of the group `pgid`, from one `ps` of every process."""
    out = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True).stdout
    total = 0
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == str(pgid) and parts[1].isdigit():
            total += int(parts[1])
    return total


def kill_group(pgid):
    """SIGKILL to the group `pgid` (never `killpg(0)`, the group of this process); a group that is gone is fine."""
    if pgid > 1:
        try:
            os.killpg(pgid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass


def guard(command, max_gb, max_seconds, out=None, err=None):
    """Run `command` under the limits; print its output and the last line (to `out` and `err`, by default the
    streams of now); return (its code, the peak in KB, why it was killed or "")."""
    out, err = out or sys.stdout, err or sys.stderr
    with tempfile.TemporaryFile() as o, tempfile.TemporaryFile() as e:
        start, peak, why = time.time(), 0, ""
        p = subprocess.Popen(command, stdout=o, stderr=e, start_new_session=True)
        while p.poll() is None:
            peak = max(peak, group_rss_kb(p.pid))
            if peak > max_gb * 1024 * 1024:
                why = " killed (memory)"
            elif time.time() - start > max_seconds:
                why = " killed (time)"
            if why:
                kill_group(p.pid)
                p.wait()
                break
            time.sleep(POLL)
        kill_group(p.pid)  # what the command left behind (a child sent to the background)
        for f, stream in ((o, out), (e, err)):
            f.seek(0)
            stream.write(f.read().decode("utf-8", "replace")[:SHOWN])
        print(f"guard: exit {p.returncode} peak {peak // 1024} MB {time.time() - start:.2f} s{why}", file=out)
        return p.returncode, peak, why.strip()


def run_args(p):
    p.add_argument("max_gb", type=float, help="the limit of the resident memory of all the processes, in GB")
    p.add_argument("max_seconds", type=float, help="the limit of the time, in seconds")
    p.add_argument("command", nargs="+", help="the command, after `--`")


def run(args):
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        print("guard: no command after `--`", file=sys.stderr)
        return 2
    guard(command, args.max_gb, args.max_seconds)
    return 0


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "run": C(run_args, run, tuple(repo.ROLES),
             "命令を、全てのプロセス（子と孫）の常駐メモリの合計と時間の上限の下で回し、超えたらグループごと SIGKILL で止める",
             "大きさで増える入力（長い式、深い入れ子、多数の形）を onsa や台本に渡すとき（`rules/common.md` 3.2、全ての役割）。`/usr/bin/time -l` で測るときは、その外側に置く",
             "guard.py run 2 120 -- /usr/bin/time -l target/debug/onsa check big.onsa"),
}  # fmt: skip


def main(argv=None) -> int:
    args = repo.parse_command("guard.py", __doc__.split("\n")[0], COMMANDS, argv)
    return args.run_(args)


if __name__ == "__main__":
    sys.exit(main())
