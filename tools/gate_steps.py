"""The items of the gate (`tools/gate.sh`, Q-08), in the order they run.

To add an item, add one `Step`. An item may be listed in `tests/pending.toml`
(kind `gate`) only if it says `pendable=True`: the items that keep the gate
complete (formatting, lints, tests, the fuzzing, the spec examples, the list
itself, the static checks of W1-02, the self-tests, the fmt properties of W1-07)
are never pending. Later works add checks that wait for a later decision as
pendable items (the C checks of W1-06; the comment places of fmt, W1-07). The
CST round trip (W3-01) is never pending.

A pendable item may also apply the list case by case: the entries
`<item>/<case>` are the item's own to apply (the C checks, `onsa_tests::ccheck`;
the test vectors, `onsa_tests::vectors`); the gate applies only the entry of
the whole item. An item with `by_case_only=True` may be listed only by case
(`tools/pending.py` refuses its whole entry: it would hide every new failure).
An item with `expect_internal=True` may hold an internal error of the compiler
by a case entry with `expect = "internal"` (W1-04, W2-02). An item with
`counts_rows=True` counts the failing rows of a case: its case entries must
say how many (`rows = N`), and the item fails when the count differs.

An item listed whole (not by case) is known to fail, so the gate skips it
unless the run names its `until` (`--work`) or ends a stage (`--stage-end`).
An item with `slow=True` (the fuzzing, the fix loop, the self-test, the C,
the fmt properties) is left out by `--quick`, a check for the middle of a work that
is not the gate's verdict (2026-10-08). An item with `stage_end_only=True`
(the deep fuzzing) runs only with `--stage-end`, for the load on the machine
(W3-03).

The forms of a run (X-1; `tools/gate.py` builds the arguments):
- the whole (no option) and the stage end (`--stage-end`) run every item, the
  heavy ones whole;
- the work check (`--work ID`) narrows the items with `narrows` (`--changed-since
  auto --sample SAMPLE --salt <the first ID>`, `tools/narrowing.py`) unless the diff
  touches their tools, and runs an item with `touches` only when the diff touches
  those places (the self-test: `tools/`);
- the sweep (`--sweep`, the main tree only) runs `save-base`, the `static` items,
  the next of the SHARDS shards of the items with `narrows` (`--shard k/K`), and the
  items with `sweep`;
- `--only NAMES` runs the items named (`static`: the static items) in the form of
  the other options.
The work check warns past BUDGET_WORK seconds, a sweep past BUDGET_SWEEP. The
narrowed runs keep the cap of the codes of the tools (`narrowing.CODE_CAP`): the
gate passes none. An item with `parent=True` exits PARENT when what is left waits
for the parent (in a worktree, the marks of `tools/gap_marks.py` to register; the documents changed
after the last docs check, `docs.py due`): status PARENT, not a failure.
"""
import sys
from dataclasses import dataclass
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
PY = (sys.executable, "-B")
SAMPLE = 0.1  # the fraction of the sample of the work check (X-1 M-1)
SHARDS = 2  # the shards of the sweep, K (M-2): one sweep within BUDGET_SWEEP
BUDGET_WORK = 300  # seconds of the items of a work check before the warning (M-8)
BUDGET_SWEEP = 600  # seconds of the items of a sweep before the warning
BASES_KEPT = 5  # the base binaries kept in target/base (M-3)
# The size of the main tree's `target/debug` past which a run of the main tree warns: cargo keeps the
# outputs of the builds before (about 5 times a build from nothing, 1.6 GB on 2026-10-16).
DEBUG_DIR_LIMIT = 8 * 2**30
PARENT = 3  # the exit of an item whose findings wait for the parent (M-5): not 1, not CANNOT_RUN
# The tools of the narrowable items: a diff that touches them runs the item whole.
FUZZ_TOOLS = ("tools/fuzz.py", "tools/narrowing.py")
FMT_TOOLS = ("tools/fmt_props.py", "tools/narrowing.py")
# The C checks (Q-07, W1-06): one item per row of `onsa_tests::c::ITEMS`.
C_CHECK = ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--", "--c")
# The test vectors against an implementation (W2-02): `interp` or `c`.
VECTORS = ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--", "--vectors")


@dataclass(frozen=True)
class Step:
    name: str
    argv: tuple
    info: bool = False  # shows something for the parent to read; a failure to show it fails
    pendable: bool = False  # may be listed in tests/pending.toml
    stage_args: bool = False  # receives `--stage-end STAGE`
    gate_steps: bool = False  # receives `--gate-steps <pendable items>`
    by_case_only: bool = False  # a pendable item listed only by case (`<item>/<case>`)
    expect_internal: bool = False  # its case entries may say `expect = "internal"`
    counts_rows: bool = False  # its case entries must say `rows = N`, the failing rows they hold
    slow: bool = False  # left out by `--quick`
    stage_end_only: bool = False  # runs only at a stage end (`--stage-end`)
    narrows: tuple = ()  # its tools: narrowed in a work check, a shard in a sweep (X-1)
    touches: tuple = ()  # a work check runs it only when the diff touches one of these
    static: bool = False  # a static check: in every sweep, `--only static`
    sweep: bool = False  # in the sweep (the `static` and `narrows` items are, without it)
    sweep_only: bool = False  # only in the sweep; the other forms do not list it
    parent: bool = False  # its exit PARENT is the status PARENT


STEPS = [
    # The binaries of HEAD for the narrowed fuzzing of later works (X-1 M-3); first in a sweep.
    Step("save-base", (*PY, str(TOOLS / "gate.py"), "--save-base"), slow=True, sweep=True, sweep_only=True),
    Step("fmt", ("cargo", "fmt", "--all", "--", "--check")),
    Step("clippy", ("cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings")),
    Step("test", ("cargo", "test", "--workspace")),
    # The compiler does not fail inside on mutated inputs (Q-06, W1-04).
    Step("fuzz", (*PY, str(TOOLS / "fuzz.py")), slow=True, narrows=FUZZ_TOOLS),
    # The mutants that nest thousands deep (S-183, W3-14), with the replay: heavy on the machine
    # (1 to 2.5 minutes on 10 cores), so only at a stage end (W3-03, 2026-10-08).
    Step("fuzz-deep", (*PY, str(TOOLS / "fuzz.py"), "--deep"), slow=True, stage_end_only=True),
    # The fix candidates applied again and again until the loop stops (S-236, rules/criteria.md 7.27,
    # W3-22): the cases of tests/spec/fixes and the saved inputs of the fuzzing. It shows the cycles and the
    # divergences (report only, until the known ones are sorted out) and fails when it walks nothing, runs
    # out of its time, or a walk ends in an internal error.
    Step("fix-loop", ("cargo", "run", "-q", "-p", "onsa_tests", "--bin", "onsa_cases", "--", "--fix-loop-gate"),
         info=True, slow=True),  # fmt: skip
    Step("spec-examples", (*PY, str(TOOLS / "check_spec_examples.py")), static=True),
    Step("spec-sections", (*PY, str(TOOLS / "spec_sections.py"), "--check"), static=True),
    # The documents write the `init` of a delay in the omitted form (S-539 (c3a)): the ```onsa blocks of the spec
    # and of spec/tools.md, and the files of examples/ and std/.
    Step("default-inits", (*PY, str(TOOLS / "default_inits.py")), static=True),
    # The documents (X-2 DT-5): now the tables (d). The lines `fmt` would break are shown, never a failure (DT-4, DF-8).
    Step("docs", (*PY, str(TOOLS / "docs.py"), "check"), static=True),
    Step("docs-fmt", (*PY, str(TOOLS / "docs.py"), "fmt", "--list"), info=True, static=True),
    # The documents changed after the last check of onsa-docs taken in (the trailer `Docs-Checked:`, X-9 U1).
    Step("docs-due", (*PY, str(TOOLS / "docs.py"), "due"), stage_args=True, static=True, parent=True),
    Step("pending", (*PY, str(TOOLS / "pending.py")), stage_args=True, gate_steps=True, static=True),
    # The ignores of the Rust tests whose reason names a work that is done or not in tasks/W/ (R-224).
    Step("ignores", (*PY, str(TOOLS / "ignores.py"), "stale"), stage_args=True, static=True),
    Step("diag-registry", (*PY, str(TOOLS / "diag_codes.py"), "--registry"), static=True),
    Step("diag-negatives", (*PY, str(TOOLS / "diag_codes.py"), "--negatives"), static=True),
    Step("gap-marks", (*PY, str(TOOLS / "gap_marks.py")), static=True, parent=True),
    Step("builtin-names", (*PY, str(TOOLS / "builtin_names.py")), static=True),
    # The test vectors of 3.3 / 3.4 (W2-01): regenerated byte for byte, the registry against the spec, the
    # cross-check recorded for this data.
    Step("vectors", (*PY, str(TOOLS / "vectors" / "gen.py"), "--check")),
    # The interpreter against the vectors (W2-02): one case per operation, `vectors-interp/<op>`.
    Step(
        "vectors-interp", (*VECTORS, "interp"), pendable=True, by_case_only=True, expect_internal=True, counts_rows=True
    ),
    Step("ignored-files", (*PY, str(TOOLS / "ignored_files.py"))),
    # The keywords of the lexer against the list of §2.2 (W3-02): one case per word, `keywords/<word>`.
    Step("keywords", (*PY, str(TOOLS / "keywords.py")), pendable=True, by_case_only=True),
    Step("gate-selftest", (*PY, str(TOOLS / "test_gate.py")), slow=True, touches=("tools/",), sweep=True),
    Step("golden", (*PY, str(TOOLS / "gate.py"), "--golden"), info=True),
    Step("spec-coverage", (*PY, str(TOOLS / "spec_sections.py"), "--list"), info=True),
    # The generated C (Q-07, W1-06): Clang and gcc-15 with -Wall -Wextra -Werror -pedantic and
    # conformance, the sanitizers, x86_64 under Rosetta, the public headers in C11, C99 and C++11.
    # A `-strict` item keeps the warnings its pair switches off for a known cause (the `off` of
    # the row in `onsa_tests::c::ITEMS`; none since W2-09): the list holds the strict one, the
    # pair always runs.
    Step("c-clang", (*C_CHECK, "c-clang"), pendable=True, slow=True),
    Step("c-gcc", (*C_CHECK, "c-gcc"), pendable=True, slow=True),
    Step("c-sanitize", (*C_CHECK, "c-sanitize"), pendable=True, slow=True),
    Step("c-x86", (*C_CHECK, "c-x86"), pendable=True, slow=True),
    Step("c-header", (*C_CHECK, "c-header"), pendable=True, slow=True),
    Step("c-header-strict", (*C_CHECK, "c-header-strict"), pendable=True, slow=True),
    # The generated C against the vectors (W2-02), with every toolchain of the C checks:
    # one case per operation and toolchain, `vectors-c/<op>[<toolchain>]`.
    Step("vectors-c", (*VECTORS, "c"), pendable=True, by_case_only=True, counts_rows=True, slow=True),
    # The properties of `onsa fmt` on perturbed case sources (Q-03, W1-07): the
    # same program, idempotence, the normal form of the code.
    Step("fmt-props", (*PY, str(TOOLS / "fmt_props.py")), slow=True, narrows=FMT_TOOLS),
    # Comments stay on the line of their element (R-70); listed until W3-11.
    Step("fmt-comments", (*PY, str(TOOLS / "fmt_props.py"), "--property", "comments"), pendable=True, slow=True,
         narrows=FMT_TOOLS),  # fmt: skip
    # The CST gives the source back byte for byte (R-86, W3-01).
    Step("fmt-cst", (*PY, str(TOOLS / "fmt_props.py"), "--property", "cst"), slow=True, narrows=FMT_TOOLS),
]


def pendable(steps=None):
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info]


def by_case_only(steps=None):
    """The pendable items that may be listed only by case."""
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info and s.by_case_only]


def expect_internal(steps=None):
    """The pendable items whose case entries may say `expect = "internal"`."""
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info and s.expect_internal]


def counts_rows(steps=None):
    """The pendable items whose case entries must say `rows = N`."""
    return [s.name for s in (STEPS if steps is None else steps) if s.pendable and not s.info and s.counts_rows]


def static_names(steps=None):
    """The static items (`--only static`)."""
    return [s.name for s in (STEPS if steps is None else steps) if s.static]
