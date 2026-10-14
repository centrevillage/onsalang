#!/usr/bin/env python3
"""Run a command in the background and wait for it by its process ID, never by its name.

    tools/bg.py run <dir> -- <command>...
    tools/bg.py wait <dir> [--timeout S] [--tail N]
    tools/bg.py status <dir>...
    tools/bg.py stop <dir>

`run` starts a small watcher process (a session of its own) and returns once
the command has started. The watcher starts the command in a process group
of its own, in the current directory, and writes into <dir>: `cmd` (the
command), `pid` (the command, also its process group), `watcher` (the
watcher), `out` (stdout and stderr) and, when the command ends, `exit` (its
exit code, or the name of the signal that ended it). The watcher ends with the
command. `run` refuses a <dir> whose command or watcher is still alive.

`wait` returns when `exit` is there: it prints the exit and the last lines of
`out` (`--tail`, 20) and exits with the command's code (128 + the signal
number for a signal). At `--timeout` (540 s: under the 600 s of a foreground
Bash call) it prints that the command still runs and exits 124. A watcher that
is gone without writing `exit` is printed as lost (exit 125). Whether a process
lives is `os.kill(pid, 0)` on the written numbers; no process is ever looked
up by its name or its command line (`pgrep -f` matches the waiting shell).

`status` prints, per <dir>, running / finished (exit) / lost, and the time
since the start (to the end when finished). `stop` sends SIGTERM to the
command's process group, then SIGKILL to what is left after `STOP_GRACE`
seconds; it never sends a signal that makes a crash report (SIGABRT, ...).
"""
import argparse
import os
import shlex
import signal
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True

TIMEOUT = 540
TIMEOUT_EXIT = 124
LOST_EXIT = 125
STOP_GRACE = 5.0
FILES = ("cmd", "pid", "watcher", "out", "exit")


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def read(d, name):
    try:
        return (Path(d) / name).read_text().strip()
    except FileNotFoundError:
        return None


def write(d, name, text):
    tmp = Path(d) / f".{name}.tmp"
    tmp.write_text(text + "\n")
    tmp.replace(Path(d) / name)


def state(d):
    """("finished", exit) | ("running", None) | ("lost", None) | ("none", None)."""
    if (e := read(d, "exit")) is not None:
        return "finished", e
    watcher = read(d, "watcher")
    if watcher is None:
        return "none", None
    if alive(int(watcher)):
        return "running", None
    if (e := read(d, "exit")) is not None:  # it wrote `exit` and ended since the first look
        return "finished", e
    return "lost", None


def going(d):
    """The command or its watcher is alive (a lost watcher may leave its command running)."""
    st, pid = state(d)[0], read(d, "pid")
    return st == "running" or (st == "lost" and pid is not None and alive(int(pid)))


def code_of(exit_text):
    if exit_text.lstrip("-").isdigit():
        return int(exit_text)
    return 128 + signal.Signals[exit_text].value


def elapsed(d, st):
    start = (Path(d) / "cmd").stat().st_mtime
    end = (Path(d) / "exit").stat().st_mtime if st == "finished" else time.time()
    return f"{end - start:.1f} s"


def watch(d, cmd):
    """The watcher: run the command, write its pid, wait, write its exit."""
    # `stop` signals the command's group, not this one; a handler (not SIG_IGN) is not inherited by the command
    signal.signal(signal.SIGTERM, lambda *_: None)
    with open(Path(d) / "out", "wb") as out:
        try:
            p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                                 process_group=0, restore_signals=True)
        except OSError as e:
            out.write(f"bg.py: the command does not start: {e}\n".encode())
            write(d, "exit", "127")
            return
        write(d, "pid", str(p.pid))
        code = p.wait()
    write(d, "exit", str(code) if code >= 0 else signal.Signals(-code).name)


def run(d, cmd):
    d.mkdir(parents=True, exist_ok=True)
    if going(d):
        print(f"{d}: the command before is still running (pid {read(d, 'pid')}); stop it or wait for it")
        return 1
    for name in FILES:
        (d / name).unlink(missing_ok=True)
    write(d, "cmd", shlex.join(cmd))
    w = subprocess.Popen([sys.executable, "-B", str(Path(__file__).resolve()), "_watch", str(d), "--", *cmd],
                         stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         start_new_session=True)
    write(d, "watcher", str(w.pid))
    deadline = time.time() + 10
    while read(d, "pid") is None and read(d, "exit") is None and time.time() < deadline and w.poll() is None:
        time.sleep(0.05)
    print(f"{d}: started, pid {read(d, 'pid')} (watcher {w.pid})")
    return 0


def tail(d, n):
    try:
        lines = (Path(d) / "out").read_text(errors="replace").splitlines()
    except FileNotFoundError:
        return
    for line in lines[-n:]:
        print(f"  | {line}")


def wait(d, timeout, n):
    deadline = time.monotonic() + timeout
    while True:
        st, e = state(d)
        if st == "finished":
            print(f"{d}: finished, exit {e} after {elapsed(d, st)}")
            tail(d, n)
            return code_of(e)
        if st in ("lost", "none"):
            print(f"{d}: {'lost: the watcher is gone without writing `exit`' if st == 'lost' else 'nothing was run here'}")
            tail(d, n)
            return LOST_EXIT
        if time.monotonic() >= deadline:
            print(f"{d}: still running after {timeout:g} s of waiting (pid {read(d, 'pid')}, {elapsed(d, st)} in all)")
            return TIMEOUT_EXIT
        time.sleep(min(0.2, max(0.0, deadline - time.monotonic())))


def stop(d):
    st, e = state(d)
    pid = read(d, "pid")
    if st == "finished" or pid is None:
        print(f"{d}: {st}" + (f", exit {e}" if e else "") + "; nothing to stop")
        return 0
    if not pid.isdigit() or int(pid) <= 1:
        # `killpg(0)` would signal the group of this process, and 1 is init.
        print(f"{d}: the written pid {pid!r} is no process group to stop")
        return 1
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(int(pid), sig)
        except ProcessLookupError:
            break
        deadline = time.monotonic() + STOP_GRACE
        while time.monotonic() < deadline and going(d):
            time.sleep(0.05)
        if not going(d):
            break
    st, e = state(d)
    print(f"{d}: {st}" + (f", exit {e}" if e else "") + (", still alive" if going(d) else ""))
    return 1 if going(d) else 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else list(argv)
    if argv[:1] == ["_watch"]:
        watch(Path(argv[1]), argv[3:])
        return 0
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("run")
    p.add_argument("dir", type=Path)
    p.add_argument("command", nargs=argparse.REMAINDER)
    p = sub.add_parser("wait")
    p.add_argument("dir", type=Path)
    p.add_argument("--timeout", type=float, default=TIMEOUT)
    p.add_argument("--tail", type=int, default=20)
    p = sub.add_parser("status")
    p.add_argument("dirs", type=Path, nargs="+")
    p = sub.add_parser("stop")
    p.add_argument("dir", type=Path)
    args = ap.parse_args(argv)
    if args.cmd == "run":
        cmd = args.command[1:] if args.command[:1] == ["--"] else args.command
        if not cmd:
            ap.error("run needs a command after `--`")
        return run(args.dir, cmd)
    if args.cmd == "wait":
        return wait(args.dir, args.timeout, args.tail)
    if args.cmd == "stop":
        return stop(args.dir)
    for d in args.dirs:
        st, e = state(d)
        print(f"{d}: {st}" + (f", exit {e}" if e else "") + (f", {elapsed(d, st)}" if st != "none" else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
