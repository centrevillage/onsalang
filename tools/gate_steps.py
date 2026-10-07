"""The items of the gate (`tools/gate.sh`, Q-08), in the order they run.

To add an item, add one `Step`. An item may be listed in `tests/pending.toml`
(kind `gate`) only if it says `pendable=True`: the items that keep the gate
complete (formatting, lints, tests, the fuzzing, the spec examples, the list
itself, the static checks of W1-02, the self-tests, the fmt properties of W1-07)
are never pending. Later works add checks that wait for a later decision as
pendable items (the C checks of W1-06; the comment places and the CST round
trip of fmt, W1-07).

A pendable item may also apply the list case by case: the entries
`<item>/<case>` are the item's own to apply (the C checks, `onsa_tests::ccheck`);
the gate applies only the entry of the whole item.
"""
import sys
from dataclasses import dataclass
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
PY = (sys.executable, "-B")
# The C checks (Q-07, W1-06): one item per row of `onsa_tests::c::ITEMS`.
C_CHECK = ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--", "--c")


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
    # The compiler does not fail inside on mutated inputs (Q-06, W1-04).
    Step("fuzz", (*PY, str(TOOLS / "fuzz.py"))),
    Step("spec-examples", (*PY, str(TOOLS / "check_spec_examples.py"))),
    Step("spec-sections", (*PY, str(TOOLS / "spec_sections.py"), "--check")),
    Step("pending", (*PY, str(TOOLS / "pending.py")), stage_args=True, gate_steps=True),
    Step("diag-registry", (*PY, str(TOOLS / "diag_codes.py"), "--registry")),
    Step("diag-negatives", (*PY, str(TOOLS / "diag_codes.py"), "--negatives")),
    Step("gap-marks", (*PY, str(TOOLS / "gap_marks.py"))),
    Step("builtin-names", (*PY, str(TOOLS / "builtin_names.py"))),
    Step("ignored-files", (*PY, str(TOOLS / "ignored_files.py"))),
    Step("gate-selftest", (*PY, str(TOOLS / "test_gate.py"))),
    Step("golden", (*PY, str(TOOLS / "gate.py"), "--golden"), info=True),
    Step("spec-coverage", (*PY, str(TOOLS / "spec_sections.py"), "--list"), info=True),
    # The generated C (Q-07, W1-06): Clang and gcc-15 with -Wall -Wextra -Werror -pedantic and
    # conformance, the sanitizers, x86_64 under Rosetta, the public headers in C11, C99 and C++11.
    # A `-strict` item keeps the warnings its pair switches off for a known cause
    # (`onsa_tests::c::GCC_KNOWN_OFF`): the list holds the strict one, the pair always runs.
    Step("c-clang", (*C_CHECK, "c-clang"), pendable=True),
    Step("c-gcc", (*C_CHECK, "c-gcc"), pendable=True),
    Step("c-gcc-strict", (*C_CHECK, "c-gcc-strict"), pendable=True),
    Step("c-sanitize", (*C_CHECK, "c-sanitize"), pendable=True),
    Step("c-x86", (*C_CHECK, "c-x86"), pendable=True),
    Step("c-header", (*C_CHECK, "c-header"), pendable=True),
    Step("c-header-strict", (*C_CHECK, "c-header-strict"), pendable=True),
    # The properties of `onsa fmt` on perturbed case sources (Q-03, W1-07): the
    # same program, idempotence, the normal form of the code.
    Step("fmt-props", (*PY, str(TOOLS / "fmt_props.py"))),
    # Comments stay on the line of their element (R-70); listed until W3-11.
    Step("fmt-comments", (*PY, str(TOOLS / "fmt_props.py"), "--property", "comments"), pendable=True),
    # The CST gives the source back byte for byte (R-86); listed until W3-01.
    Step("fmt-cst", (*PY, str(TOOLS / "fmt_props.py"), "--property", "cst"), pendable=True),
]


def pendable(steps=None):
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info]
