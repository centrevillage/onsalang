"""The ```onsa blocks of the spec, and their names in `tests/pending.toml` (D-06).

The one place for: reading the fences of the spec, the normalization used by
the verbatim check, and the form of a block's name ("§<section> <hash>: <first
line>"). `check_spec_examples.py` makes and matches names, `pending.py`
checks that a target has the form.
"""
import hashlib
import re
from dataclasses import dataclass

MARKER = re.compile(r"[ \t]*//~.*$", re.M)
HEADING = re.compile(r"#{1,6}\s+(\d+(?:\.\d+)*)\.?\s")
FENCE = re.compile(r"(`{3,}|~{3,})(.*)")
ONSA_FENCE = "```onsa"

# The name of a block: section, hash (8 hex digits of the SHA-256 of the
# normalized block), first non-empty line with whitespace runs collapsed.
ID_FORM = re.compile(r"§(?P<section>\d+(?:\.\d+)*) (?P<hash>[0-9a-f]{8}): (?P<head>\S.*)")


@dataclass(frozen=True)
class Block:
    line: int  # 1-based line of the first line inside the fence
    section: str
    code: str


def scan(spec_text):
    """Return (blocks, errors). Errors are fences the check cannot trust: a
    fence that is not closed, and one that looks like onsa but is not spelled
    exactly ```onsa (it would be skipped silently)."""
    lines = spec_text.split("\n")
    blocks, errors = [], []
    section = "0"
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        m = FENCE.fullmatch(stripped)
        if not m:
            h = HEADING.match(lines[i])
            if h:
                section = h.group(1)
            i += 1
            continue
        fence, info = m.group(1), m.group(2)
        run = re.escape(fence[0]) + "{%d,}" % len(fence)
        closer = re.compile(run)
        # A fence with an info string inside a fence of the same kind means the
        # first was not closed (Markdown would read it as text and swallow the
        # blocks after it).
        reopen = re.compile(run + r"\s*\S.*")
        j = i + 1
        while j < len(lines) and not closer.fullmatch(lines[j].strip()) and not reopen.fullmatch(lines[j].strip()):
            j += 1
        if j == len(lines):
            errors.append((i + 1, f'the fence "{stripped}" is not closed'))
            break
        if not closer.fullmatch(lines[j].strip()):
            errors.append((i + 1, f'the fence "{stripped}" is not closed before line {j + 1}'))
            i = j  # go on from the fence that follows
            continue
        if stripped == ONSA_FENCE:
            blocks.append(Block(i + 2, section, "\n".join(lines[i + 1 : j]).rstrip("\n")))
        elif info.strip().lower().startswith("onsa"):
            errors.append((i + 1, f'the fence "{stripped}" looks like onsa but is not "{ONSA_FENCE}"'))
        i = j + 1
    return blocks, errors


def normalize(text):
    """Drop `//~` markers, the indentation and trailing spaces of each line, and
    the blank lines around the text."""
    text = MARKER.sub("", text)
    return "\n".join(line.strip() for line in text.split("\n")).strip("\n")


def spec_id(section, code):
    norm = normalize(code)
    digest = hashlib.sha256(norm.encode("utf-8")).hexdigest()[:8]
    head = next((line for line in norm.split("\n") if line), "")
    return f"§{section} {digest}: {' '.join(head.split())}"


def parse_id(target):
    """(section, hash, head) of a name, or None if it is not of the form."""
    m = ID_FORM.fullmatch(target)
    return (m["section"], m["hash"], m["head"]) if m else None


def toml_string(s):
    """`s` as a TOML basic string, to paste into `tests/pending.toml`."""
    out = []
    for c in s:
        if c in '"\\':
            out.append("\\" + c)
        elif ord(c) < 0x20 or ord(c) == 0x7F:
            out.append("\\u%04X" % ord(c))
        else:
            out.append(c)
    return '"' + "".join(out) + '"'
