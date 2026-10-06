"""The items of the gate (`tools/gate.sh`, Q-08), in the order they run.

To add an item, add one `Step`. An item may be listed in `tests/pending.toml`
(kind `gate`) only if it says `pendable=True`: the items that keep the gate
complete (formatting, lints, tests, the spec examples, the list itself, the
self-tests) are never pending. Later works add checks that wait for a later
decision as pendable items.
"""
import sys
from dataclasses import dataclass
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
PY = (sys.executable, "-B")


@dataclass(frozen=True)
class Step:
    name: str
    argv: tuple
    info: bool = False  # shows something for the parent to read; a failure to show it fails
    pendable: bool = False  # may be listed in tests/pending.toml
    stage_args: bool = False  # receives `--stage-end STAGE`
    gate_steps: bool = False  # receives `--gate-steps <pendable items>`


STEPS = [
    Step("fmt", ("cargo", "fmt", "--all", "--", "--check")),
    Step("clippy", ("cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings")),
    Step("test", ("cargo", "test", "--workspace")),
    Step("spec-examples", (*PY, str(TOOLS / "check_spec_examples.py"))),
    Step("spec-sections", (*PY, str(TOOLS / "spec_sections.py"), "--check")),
    Step("pending", (*PY, str(TOOLS / "pending.py")), stage_args=True, gate_steps=True),
    Step("gate-selftest", (*PY, str(TOOLS / "test_gate.py"))),
    Step("golden", (*PY, str(TOOLS / "gate.py"), "--golden"), info=True),
    Step("spec-coverage", (*PY, str(TOOLS / "spec_sections.py"), "--list"), info=True),
]


def pendable(steps=None):
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info]
