#!/usr/bin/env python3
"""Mutants by hand: put one mutant of a list into a tree, run the commands of the list in order, stop at the first
that fails, put the tree back; the next mutant, one at a time (X-19 3, X-27 TU1).

Its commands are `run`, `match` and `restore` (COMMANDS, rules/tools.md 9.1); `mutate.py help` shows them and the
text below.

The list is a TOML file: `[[command]]` tables run in their order in the tree (the working directory), each with
`label`, `run` (a list of words, or a string split as the shell does, no shell run) and `env` (optional, added to
the environment); `[[mutant]]` tables, each with `name`, `path` (from the tree), `before` and `after` (a ''' string
may span lines). More places of one mutant are `[[mutant.more]]` tables of `path`, `before` and `after`, put in
after the ones above it: every `before` must be found exactly once (in the text the earlier places left) before
anything is written.

    [[command]]
    label = "sema"
    run = "cargo test -q -p onsa_sema --lib"
    env = { CARGO_TARGET_DIR = "/path/to/target" }

    [[mutant]]
    name = "flip"
    path = "crates/onsa_sema/src/x.rs"
    before = "a < b"
    after = "a <= b"

`run` prints a line a mutant: its name, its result, the seconds. The results:
    LIVED                 every command passed
    killed by <label> […] that command failed (exit other than 0); the first names of `^test (\\S+) ... FAILED`
    COMPILE-ERROR <label> that command failed and printed `could not compile` (cargo)
    TIMEOUT <label>       that command ran past `--timeout` (default 1500 seconds); it and its children are killed
    BAD-MATCH <n>         a `before` is found n times, not once (`no file`: the path is not a file); nothing is run
and then how many of each. Exit 0 when every mutant has one of the first four; 1 on a BAD-MATCH, an error of the
list, a command that cannot start, a tree it could not put back, a backup left or a stop by a signal; 2 on an error
of the arguments (argparse).
Before a mutant is put in, the texts of its files go to the backup `<tree>/target/mutate.json` (made only when there
is none; git does not track target/). The files are put back and the backup removed when the commands end, fail,
time out, or are stopped (an exception, Ctrl-C, SIGTERM, SIGHUP). A backup left (after SIGKILL, or the machine
stopping) stops `run` and `match`: `mutate.py restore <tree>` puts the files back, only when each is still as the
mutant left it (or already back), else it stops and changes nothing.
On the main tree, while a mutant is in, the sweep after a commit waits (`waiting-clean`); a copy (rsync) is usual.
"""
import json
import os
import re
import shlex
import signal
import subprocess
import sys
import time
import tomllib
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import repo  # noqa: E402

BACKUP = Path("target") / "mutate.json"
TIMEOUT = 1500  # seconds a command
FAILED = re.compile(r"^test (\S+) \.\.\. FAILED", re.M)
SHOWN = 3  # the names of the failed tests on a line
STOPS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
KINDS = ("LIVED", "killed", "COMPILE-ERROR", "TIMEOUT", "BAD-MATCH")


class Fail(Exception):
    """An error that stops the tool (exit 1): its message is printed."""


class Stopped(Exception):
    """SIGTERM or SIGHUP while a mutant is in (SIGINT is KeyboardInterrupt)."""


def _stop(signum, frame):
    raise Stopped(signal.Signals(signum).name)


def _table(t, keys, need, what):
    if not isinstance(t, dict) or set(t) - set(keys) or set(need) - set(t):
        raise Fail(f"{what}: the keys are {', '.join(keys)} ({', '.join(need)} needed): {t!r}"[:300])
    return t


def _site(t, what):
    t = _table(t, ("path", "before", "after"), ("path", "before", "after"), what)
    if not all(isinstance(t[k], str) for k in t) or not t["before"] or t["before"] == t["after"]:
        raise Fail(f"{what}: path, before and after are strings, before not empty and not the same as after")
    p = Path(t["path"])
    if p.is_absolute() or ".." in p.parts:
        raise Fail(f"{what}: the path {t['path']} is not inside the tree")
    return (os.path.normpath(t["path"]), t["before"], t["after"])


def load(path):
    """([(label, argv, env)], {name: [(path, before, after)]}) of the list `path` (Fail on an error of it)."""
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as e:
        raise Fail(f"{path}: {e}") from None
    _table(data, ("command", "mutant"), ("command", "mutant"), str(path))
    commands = []
    for i, c in enumerate(data["command"]):
        c = _table(c, ("label", "run", "env"), ("label", "run"), f"command {i + 1}")
        argv = shlex.split(c["run"]) if isinstance(c["run"], str) else c["run"]
        env = c.get("env", {})
        if not isinstance(c["label"], str) or not argv or not all(isinstance(w, str) for w in argv) or \
                not isinstance(env, dict) or not all(isinstance(v, str) for v in env.values()):  # fmt: skip
            raise Fail(f"command {i + 1}: label is a string, run words, env a table of strings")
        commands.append((c["label"], argv, env))
    mutants = {}
    for i, m in enumerate(data["mutant"]):
        m = _table(m, ("name", "path", "before", "after", "more"), ("name",), f"mutant {i + 1}")
        name = m.pop("name")
        if not isinstance(name, str) or not name or name in mutants:
            raise Fail(f"mutant {i + 1}: the name {name!r} is empty or taken")
        more = m.pop("more", [])
        if not isinstance(more, list):
            raise Fail(f"{name}: more is a list of tables")
        mutants[name] = [_site(s, name) for s in (m, *more)]
    if not commands or not mutants:
        raise Fail(f"{path}: no command or no mutant")  # LIVED with nothing run would be a pass of nothing
    return commands, mutants


def _text(path):
    try:
        return path.read_bytes().decode("utf-8")
    except UnicodeDecodeError as e:
        raise Fail(f"{path} is not UTF-8: {e}") from None


def put_in(tree, sites):
    """({path: (the text, the mutated text)}, None) when every `before` is found once, else (None, what is shown)."""
    texts, counts = {}, []
    for rel, before, after in sites:
        f = tree / rel
        if rel not in texts and not f.is_file():
            return None, "no file " + rel
        old, new = texts.get(rel) or (_text(f),) * 2
        counts.append(new.count(before))
        texts[rel] = (old, new.replace(before, after, 1))
    return (texts, None) if counts == [1] * len(counts) else (None, ",".join(map(str, counts)))


def _left(tree):
    if (tree / BACKUP).exists():
        raise Fail(f"a backup is left: {tree / BACKUP}; put the tree back with `mutate.py restore {tree}`")


def restore(tree):
    """Put back the files of the backup of `tree` (each still as the mutant left it, or already back) and remove
    it; Fail, changing nothing, when one is neither. Signals wait until it is done."""
    signal.pthread_sigmask(signal.SIG_BLOCK, STOPS)
    try:
        b = tree / BACKUP
        try:
            saved = json.loads(b.read_text(encoding="utf-8"))
            files = {rel: (f["text"], f["mutated"]) for rel, f in saved["files"].items()}
        except (OSError, ValueError, KeyError, TypeError) as e:
            raise Fail(f"{b} cannot be read ({e}); see the files by hand and remove it") from None
        now = {rel: _text(tree / rel) if (tree / rel).is_file() else None for rel in files}
        changed = [rel for rel, (old, new) in files.items() if now[rel] not in (old, new)]
        if changed:
            raise Fail(f"changed since the mutant {saved.get('name')} was put in, not put back: {', '.join(changed)}")
        for rel, (old, new) in files.items():
            if now[rel] != old:
                (tree / rel).write_bytes(old.encode("utf-8"))
        b.unlink()
    finally:
        signal.pthread_sigmask(signal.SIG_UNBLOCK, STOPS)


def _kill(pid):
    try:
        os.killpg(pid, signal.SIGKILL)  # the group of the command (start_new_session), never this one's
    except (ProcessLookupError, PermissionError):
        pass


def run_command(tree, argv, env, timeout):
    """(the exit code or None on a timeout, the output) of `argv` in `tree`; it and its children are killed after."""
    try:
        p = subprocess.Popen(argv, cwd=tree, env={**os.environ, **env}, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, errors="replace", start_new_session=True)  # fmt: skip
    except OSError as e:
        raise Fail(f"cannot run {shlex.join(argv)}: {e}") from None
    try:
        out = p.communicate(timeout=timeout)[0]
        return p.returncode, out
    except subprocess.TimeoutExpired:
        _kill(p.pid)
        p.communicate()
        return None, ""
    finally:
        _kill(p.pid)
        p.wait()


def try_mutant(tree, commands, texts, name, timeout):
    """The result of the commands with the mutant in (put back after, `restore`)."""
    signal.pthread_sigmask(signal.SIG_BLOCK, STOPS)  # a signal waits until the backup and the files are written
    try:
        with open(tree / BACKUP, "x", encoding="utf-8") as f:  # "x": another run on the tree since `_left`
            json.dump({"name": name, "files": {r: {"text": o, "mutated": n} for r, (o, n) in texts.items()}}, f)
    except BaseException as e:
        signal.pthread_sigmask(signal.SIG_UNBLOCK, STOPS)
        if isinstance(e, FileExistsError):
            raise Fail(f"another run put a backup in {tree / BACKUP}") from None
        raise
    try:  # unblocked below, or by `restore`
        for rel, (_, new) in texts.items():
            (tree / rel).write_bytes(new.encode("utf-8"))
        signal.pthread_sigmask(signal.SIG_UNBLOCK, STOPS)
        for label, argv, env in commands:
            code, out = run_command(tree, argv, env, timeout)
            if code is None:
                return f"TIMEOUT {label}"
            if code != 0:
                if "could not compile" in out:
                    return f"COMPILE-ERROR {label}"
                names = FAILED.findall(out)
                more = "" if len(names) <= SHOWN else f" +{len(names) - SHOWN}"
                return f"killed by {label}" + (f" [{', '.join(names[:SHOWN])}{more}]" if names else "")
        return "LIVED"
    finally:
        restore(tree)


def _chosen(args):
    tree = args.tree.resolve()
    if not tree.is_dir():
        raise Fail(f"no tree {args.tree}")
    _left(tree)
    commands, mutants = load(args.list)
    unknown = [n for n in args.names if n not in mutants]
    if unknown:
        raise Fail(f"no mutant {', '.join(unknown)} in {args.list}")
    return tree, commands, [(n, mutants[n]) for n in args.names or mutants]


def _summary(results):
    counts = {k: sum(r.split()[0] == k for r in results) for k in KINDS}
    shown = ", ".join(f"{k} {n}" for k, n in counts.items() if n) or "none"
    print(f"mutate: {len(results)} mutant(s): {shown}", flush=True)


def cmd_run(args):
    tree, commands, chosen = _chosen(args)
    (tree / BACKUP.parent).mkdir(parents=True, exist_ok=True)
    old = {s: signal.signal(s, _stop) for s in STOPS[1:]}
    results = []
    try:
        for name, sites in chosen:
            t0 = time.monotonic()
            texts, bad = put_in(tree, sites)
            result = f"BAD-MATCH {bad}" if bad else try_mutant(tree, commands, texts, name, args.timeout)
            results.append(result)
            print(f"{name}  {result}  {time.monotonic() - t0:.0f}s", flush=True)
    except (KeyboardInterrupt, Stopped) as e:
        raise Fail(f"stopped ({type(e).__name__ if isinstance(e, KeyboardInterrupt) else e}); the tree is put back")
    finally:
        for s, h in old.items():
            signal.signal(s, h)
        _summary(results)
    return 1 if any(r.startswith("BAD-MATCH") for r in results) else 0


def cmd_match(args):
    tree, _, chosen = _chosen(args)
    bad = 0
    for name, sites in chosen:
        miss = put_in(tree, sites)[1]
        bad += miss is not None
        print(f"{name}  {'BAD-MATCH ' + miss if miss else 'ok'}  ({len(sites)} place(s))")
    print(f"mutate: {len(chosen)} mutant(s), BAD-MATCH {bad}")
    return 1 if bad else 0


def cmd_restore(args):
    tree = args.tree.resolve()
    if not (tree / BACKUP).exists():
        raise Fail(f"no backup {tree / BACKUP}")
    restore(tree)
    print(f"mutate: put back {tree}")
    return 0


def _list_args(p):
    p.add_argument("tree", type=Path, help="the tree the mutants go into, the commands' working directory")
    p.add_argument("list", type=Path, help="the TOML list of the commands and the mutants (`mutate.py help`)")
    p.add_argument("names", nargs="*", help="only these mutants (default: all, in the list's order)")


def _run_args(p):
    _list_args(p)
    p.add_argument("--timeout", type=float, default=TIMEOUT, help=f"seconds a command (default {TIMEOUT})")


C = repo.Command  # (add_arguments, run, roles, purpose, when, example); the help is `help` (repo.parse_command)
COMMANDS = {
    "run": C(_run_args, cmd_run, ("parent", "t", "i", "b"),
             "一覧の変異を一つずつ木に当て、命令を順に回し（最初に落ちた所で止める）、戻す。変異ごとに結果と秒を一行",
             "変異を当てて試験が落ちるかを見るとき（台本を書く代わりに。木は普通 rsync の写し）",
             "mutate.py run /path/tree /path/mutants.toml flip"),
    "match": C(_list_args, cmd_match, ("parent", "t", "i", "b"),
               "命令を回さずに、各変異の前の字が 1 か所に当たるか（`BAD-MATCH <数>`）を出す",
               "一覧を書いた後、重い試験の `run` の前",
               "mutate.py match /path/tree /path/mutants.toml"),
    "restore": C(lambda p: p.add_argument("tree", type=Path), cmd_restore, ("parent", "t", "i", "b"),
                 "残った控えから木を戻す（ファイルが今も変異の字のままか、既に元の字のときだけ）",
                 "`run` か `match` が「a backup is left」で止まったとき（SIGKILL や機械の停止の後）",
                 "mutate.py restore /path/tree"),
}  # fmt: skip


def more_help():
    """What `mutate.py help` prints after the commands: the docstring from the form of the list on."""
    return __doc__[__doc__.index("The list is") :]


def main(argv=None):
    args = repo.parse_command("mutate.py", __doc__.split("\n")[0], COMMANDS, argv, more=more_help)
    try:
        return args.run_(args)
    except Fail as e:
        print(f"mutate: {e}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
