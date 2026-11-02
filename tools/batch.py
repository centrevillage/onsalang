"""The commands the gate's tools run on each input, asked of `onsa_cases --serve` (W4-18 U10c; X-16 (a), X-20 (ii)):
one process per thread answers request after request, with no file written, as the commands would answer.

`Pool.run(words, files)` sends a request to a server (one per thread that asks at once, kept for the next request)
and returns the command's `Result`. When the server ends, answers in a broken form or gives no answer within the
time-out (it is then killed, SIGKILL), that request alone runs the way before: its files written in a directory of
their own and one process of the command (`fallback`), whose result is the request's; the next request starts a new
server. Where that command does not crash (`crashed`), the server and the command disagree: a failure (`close`).
Past `max_deaths` ends of servers, every request left runs the way before, and that fails too. A `Pool` with no
server runs every request the way before (the base binaries: their `onsa_cases` has no `--serve`).

Each request goes to a server at most once and to the command at most once, each within the time-out, so a request
takes at most twice the time-out; the servers started are at most the threads asking at once and `max_deaths` + 1.
"""
import os
import select
import shutil
import subprocess
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path

MAX_DEATHS = 8


@dataclass(frozen=True)
class Result:
    code: int | None  # the exit code (negative: the signal); None: no end within the time-out
    out: bytes
    err: str  # decoded with "replace", as the tools read it


class Server:
    """One process of `onsa_cases --serve`, asked one request at a time."""

    def __init__(self, argv):
        self.process = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        self.buffer = b""

    def ask(self, request, timeout):
        """(the answer as a `Result`, None), or (None, why there is none) with the process gone."""
        deadline = time.monotonic() + timeout
        try:
            self.process.stdin.write(request)
            self.process.stdin.flush()
            code, n_out, n_err = (int(n) for n in self._take(None, deadline).split(b"\t"))
            body = self._take(n_out + n_err, deadline)
            return Result(code, body[:n_out], body[n_out:].decode("utf-8", "replace")), None
        except TimeoutError:
            why = f"no answer within {timeout} s"
        except ValueError:
            why = "a broken answer"
        except (EOFError, BrokenPipeError):
            why = None  # the process ended: how, below
        code = self.end(wait=5 if why is None else 0)
        return None, why or (f"signal {-code}" if code < 0 else f"exit {code}")

    def _take(self, n, deadline):
        """The next `n` bytes of the answers, or with None the next line without its newline."""
        while (b"\n" not in self.buffer) if n is None else len(self.buffer) < n:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([self.process.stdout], [], [], left)[0]:
                raise TimeoutError
            chunk = os.read(self.process.stdout.fileno(), 1 << 16)
            if not chunk:
                raise EOFError
            self.buffer += chunk
        if n is None:
            line, self.buffer = self.buffer.split(b"\n", 1)
            return line
        taken, self.buffer = self.buffer[:n], self.buffer[n:]
        return taken

    def end(self, wait):
        """The exit code of the process, killed (SIGKILL) unless it ends within `wait` seconds."""
        for pipe in (self.process.stdin, self.process.stdout):
            try:
                pipe.close()  # stdin's end is the end of the requests: the server exits 0
            except OSError:
                pass
        try:
            return self.process.wait(timeout=wait)
        except subprocess.TimeoutExpired:
            self.process.kill()
            return self.process.wait()


class Pool:
    """The requests of a tool's run: `serve` the argv of the server (None: none), `fallback(words)` the argv of the
    command of `words` before the names of its files (run in their directory, under `work`), `crashed(words,
    result)` whether a result of the command is a crash (the tool's class of it)."""

    def __init__(self, serve, fallback, work, timeout, crashed, max_deaths=MAX_DEATHS):
        self.serve, self.fallback, self.work, self.timeout = serve, fallback, Path(work), timeout
        self.crashed, self.max_deaths = crashed, max_deaths
        self.lock = threading.Lock()
        self.idle = []
        self.deaths = 0
        self.failures = []

    def run(self, words, files):
        """The `Result` of the command of `words` (a tuple) on `files` (pairs of a name, the path the command shows,
        and the bytes)."""
        with self.lock:
            served = self.serve is not None and self.deaths <= self.max_deaths
            server = self.idle.pop() if served and self.idle else None
        if not served:
            return self.alone(words, files)
        try:
            server = server or Server(self.serve)
            result, why = server.ask(request(words, files), self.timeout)
        except OSError as e:
            result, why = None, f"cannot start: {e}"
        if result is not None:
            with self.lock:
                self.idle.append(server)
            return result
        result = self.alone(words, files)
        with self.lock:
            self.deaths += 1
            if not self.crashed(words, result):
                self.failures.append(f"the server of onsa_cases ended ({why}) on {' '.join(words)} of "
                                     f"{', '.join(name for name, _ in files)}, where the command does not crash")
        return result

    def alone(self, words, files):
        """The `Result` of the command run the way before, its files written in a directory of their own."""
        self.work.mkdir(parents=True, exist_ok=True)
        d = Path(tempfile.mkdtemp(dir=self.work))
        try:
            for name, data in files:
                (d / name).parent.mkdir(parents=True, exist_ok=True)
                (d / name).write_bytes(data)
            r = subprocess.run([*self.fallback(words), *(name for name, _ in files)], cwd=d, capture_output=True,
                               timeout=self.timeout)
            return Result(r.returncode, r.stdout, r.stderr.decode("utf-8", "replace"))
        except subprocess.TimeoutExpired:
            return Result(None, b"", "")
        finally:
            shutil.rmtree(d, ignore_errors=True)

    def close(self):
        """End the servers; the failures of the run."""
        with self.lock:
            idle, self.idle = self.idle, []
        for server in idle:
            server.end(wait=10)
        many = self.deaths > self.max_deaths
        return self.failures + ([f"onsa_cases --serve ended {self.deaths} times (more than {self.max_deaths}): "
                                 "the rest ran one process each"] if many else [])


def request(words, files):
    """The bytes of a request (`onsa_tests::serve`)."""
    parts = [f"{' '.join(words)}\t{len(files)}\n".encode()]
    for name, data in files:
        if "\t" in name or "\n" in name:
            raise ValueError(f"a name of a request holds a tab or a newline: {name!r}")
        parts += [f"{name}\t{len(data)}\n".encode(), data]
    return b"".join(parts)
