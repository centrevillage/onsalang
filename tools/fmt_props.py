#!/usr/bin/env python3
"""The property tests of `onsa fmt` (Q-03, D-16 4, W1-07).

The inputs are the source files of every case under `tests/` (the list of
`onsa_cases`, `mode = "none"` included), then the `.onsa` files of `std/`
and `examples/`. fmt must read each of them, except a file of a case that
`tests/pending.toml` lists as a whole `test-case`, a file whose markers hold
a syntax code (the runner's judgement, which `onsa_cases` lists), and a
fragment of `mode = "none"`; such a file is skipped when fmt refuses it.
Any other refusal fails, and so does a run where no source ran. Each source
`x` gives, besides itself, perturbed inputs `p`: the spec says the
perturbation changes no program (§2.5, `spec/tools.md` §3.2).

Perturbations (C-118: only where whitespace means nothing). The kinds:

    space    the whitespace inside a line: a gap of spaces between two tokens
             becomes 1 to 4 spaces; a space goes in after `(` `[` `,` and before
             `)` `]` `,` `:` where there was none; the indentation becomes 0 to
             8 spaces; spaces go at the end of a line without a comment and on
             an empty line.
    blank    empty lines: more of them where there is one already; at the start
             and the end of a block or a list (after a line ending in `{` `(`
             `[`, before a line starting with `}` `)` `]`); inside a
             continuation (after a line ending in a binary operator, `=`, `->`
             or an attribute line, before a line starting with `.` or `uses`).
    comment  comments `// fmtprop-<n>`: at the end of a line that has code and
             no comment, and on a line of their own before any line.
    break    a line break after a `,` or an opening `(` / `[` of a list with a
             `,` (the innermost bracket is `(` or `[`), unless the next token
             is `{` or a closing bracket.
    continue a line break that continues the line (§2.5): after a binary
             operator between two operands (in the head of an `if` or a
             `while` too: the `{` stays on the head's last line, S-202), after
             the `=` of `let` / `var` / `const` / `type`, after a `->`, before
             `uses` and before the `.` of a method call after `)`.
    inside   a line break inside an element, which fmt removes (S-497), 2 in
             10 of them a blank line (`inside_sites`): in a gap that
             `break_places` counts `removable`, only before and after `as`,
             `at`, `:`, `=>` and `;` (S-374, S-505: the `:` of a parameter, a
             type parameter and a field, the arrow of an arm, the `;` of
             `[e; N]` and of an array type), and after `if`, `match`,
             `with`, `move` and `inout` followed by a blank (§2.5: a keyword
             in an expression and its operand); never before a `{`.
    mixed    comment, then blank, then space.

Never touched: the gaps of no whitespace other than the ones named above
(so no space before a postfix `(` / `[`, around `~`, `!`, `^` and the
prefix `-`, or next to `.`); no line break other than the ones named above
(the newlines that end statements, and the place of `{`, `else` and
`with`, stay; none goes before a binary operator, a range symbol, the `|`
of a pattern, `->`, `=`, `?` or a postfix `(` / `[`, after a `.` or a
prefix `-`, `!`, `^`, between a name and `~`, `!` or `::`, between `else`
and `if`, `fn` and `(`, `@` and its name, §2.5); the inside of comments,
strings and characters. Only spaces are used: the spec does not name
another whitespace character (a tab).

The properties (`--property`):

    core      (the gate item `fmt-props`) for `x` and every `p`:
              0. the perturbation changes no program: `onsa diff --ast x p`;
              1. `onsa fmt` accepts `p` (exit 0; exit 2 would mean the
                 perturbation hit a place where whitespace means something);
              2. same program: `onsa diff --ast p fmt(p)` finds no difference
                 (the comparison of S-56, `spec/tools.md` §3.5: both
                 trees with the rewrites of §3.3);
              3. idempotence: `onsa fmt --check fmt(p)` changes nothing;
              4. the comments keep their texts in their order (none lost, none
                 changed, none swapped); the texts of the doc comments (`///`,
                 `//!`) and the heads of the items (`item_heads`) are the same
                 in `p` and `fmt(p)` (`spec/tools.md` §3.5: the AST and the doc comments
                 agree, and the texts of the comments are in the same order;
                 `diff --ast` compares the structure alone, not the comments
                 nor the doc comments, S-534);
              5. the depth: `fmt` makes no declaration deeper (spec §2.5: the
                 rewrites take parentheses and `return` away, never add a
                 level): the levels of each item, `onsa dump --levels`, of
                 `fmt(p)` are at most those of `x` (W3-14; `p` is the
                 program of `x`, 0);
              6. the line breaks of the writer (`spec/tools.md` §3.2,
                 R-143, S-497): fmt keeps the line breaks after the opening
                 bracket of a list, between its elements (and a blank line
                 there, S-499), between statements and items, at a place of
                 a continuation (§2.5) and after a comment, adds none there,
                 and removes those inside an element (`break_problems`, on
                 the text alone; the line breaks fmt adds or removes by the
                 form of a list or a block and round attributes, and the
                 gaps of what the rewrites of §3.3 drop, are not counted);
              7. the comments and the normal form (R-70, W3-11, `spec/tools.md`
                 §3.4): every comment (the markers and the source's own) stays
                 on the line of the same element (failure `comments`): a
                 comment at a line end at the end of the same line, a comment
                 on a line of its own on its own line before the same next
                 line (or at the end). The lines of the input and of the
                 output are paired by their order and their tokens
                 (`pair_lines`: a token fmt drops, a `return` or a
                 parenthesis, is a deletion of the sequence; `,` and the
                 spelling of numbers do not count; a line of brackets alone
                 is paired by its brackets, so a comment after a closing
                 bracket goes with it, `)` as `]` and `}`, S-528; a line of a
                 `,` alone is no code line, and its comment counts as a line
                 of a comment, S-529). And the normal form with the comments
                 (failure `convergence`): `fmt(p) == fmt(x)` for space and
                 blank; `fmt(p)` without the markers, formatted again, equals
                 `fmt(x)` for comment and mixed. break and continue keep the
                 author's line breaks (`spec/tools.md` §3.2), and inside opens
                 a body of one line whose element had a line break (S-525),
                 so they have no normal form here;
              8. the meaning: when `fmt(p)` is not `p`, `onsa check` ends with
                 the same exit code on both and reports the same codes in the
                 same order (spec §18.2: no rewrite of fmt changes the verdict
                 of a stage; `spec/tools.md` §3.3). The texts and the
                 places of the diagnostics are not compared (a rewrite may
                 change the text alone, W3-12/b2 6).
              5 and 8 run on `x` and on the comment and mixed inputs alone: the
              rewrites of fmt (§3.3) are decided by the program, which a
              perturbation does not change (0), so they are those of `x`, but
              a comment may stop one (§3.4). An input of another kind runs them
              too when the code tokens of `fmt(p)` are not those of `fmt(x)`
              (`written_tokens`): its rewrites differ, which the spec does not
              allow and the item does not take on trust.
              Every run ends in 0, 1 or 2 (an internal error or a signal fails).
    cst       (`fmt-cst`, R-86, W3-01) for `x` and every `p`, with or without
              syntax errors: `onsa dump --cst <file>` prints the file byte for
              byte (the CST round trip: the text of the leaves of the tree).

The perturbations come from a generator seeded with the version, the path,
the source, the kind and the index (`fuzz.seeded_random`): the same tree
gives the same inputs on every machine. The failing inputs that are shown
(`--show`) are written to `target/fmt_props/fail/<property>/` (the item
writes nothing under `tests/`; its work directory is
`target/fmt_props/work-<pid>`); `--minimize` shrinks them first (lines, then
characters, `fuzz.ddmin`) where the property holds on its own: rejected,
internal, ast, idempotence, comment-text, docs, items, depth, breaks,
meaning.

    tools/fmt_props.py [--property core|cst] [--per-kind N]
                       [--version V] [--jobs N] [--binary PATH]
                       [--time-budget S] [--minimize] [--show N] [--verbose]
                       [--changed-since REV|auto] [--code-cap N]
                       [--sample F --salt ID] [--shard I/K]

The options of `tools/narrowing.py` pick the sources (X-1); a narrowed run
(`--changed-since`, `--sample`) always has the cases under `tests/spec/fmt`
(`ALWAYS`), a shard does not. Each source's inputs come from that source
alone, so a narrowed run checks a part of the whole run's inputs.

Exit 0 when every property holds, 1 otherwise, 2 on a usage error (or when
the compiler or the list of cases cannot be had).
"""
import argparse
import difflib
import functools
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import builtin_names  # noqa: E402
import fuzz  # noqa: E402
import narrowing  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402

ROOT = repo.ROOT
# Changing the version changes every perturbation (a new set of inputs).
VERSION = "1"
PER_KIND = 2
TIMEOUT = 20  # seconds per run
TIME_BUDGET = 300  # seconds for the whole run
PROPERTIES = ("core", "cst")
KINDS = ("space", "blank", "comment", "break", "continue", "inside", "mixed")
# The kinds whose fmt output is the normal form of the source, as it is or
# with the markers removed.
CONVERGES = ("space", "blank")
CONVERGES_STRIPPED = ("comment", "mixed")
MARKER = "fmtprop-"
# Sources besides the cases (from the root; their `.onsa` files, build outputs aside).
OTHER_SOURCES = ("std", "examples")
# The sources a narrowed run always has (X-1): the cases of fmt.
ALWAYS = ("tests/spec/fmt",)
MARKER_LINE = re.compile(r"^[ ]*// " + MARKER + r"(\d+)[ ]*$")
MARKER_END = re.compile(r"[ ]*// " + MARKER + r"(\d+)[ ]*$")

# ------------------------------------------------------------------ tokens

def load_symbols(root, cmd):
    """Read the symbols of the lexer from the compiler, once, before the
    tokens and the perturbations read them: the symbols a line ending in which
    continues (§2.5: a binary operator, a range symbol, `=`, `->`; `<cmd>
    --continuing`, `onsa_syntax::continues`, [`continuing`]) and the symbols of
    more than one character that the lexer reads as one token (`<cmd>
    --symbols`, [`long_symbols`]). Raises RepoError when they cannot be had or
    a set is empty."""
    global _CONTINUING, _LONG
    found = {}
    for flag in ("--continuing", "--symbols"):
        symbols = repo.cases_json(root, cmd, flag)
        if not isinstance(symbols, list) or not symbols or not all(isinstance(s, str) for s in symbols):
            raise repo.RepoError(f"`{flag}` gave no list of symbols: {symbols!r}")
        found[flag] = symbols
    _CONTINUING = frozenset(found["--continuing"])
    _LONG = tuple(sorted(found["--symbols"], key=len, reverse=True))


def continuing():
    """The symbols after which a line goes on ([`load_symbols`])."""
    if _CONTINUING is None:
        raise RuntimeError("fmt_props.load_symbols was not called")
    return _CONTINUING


def long_symbols():
    """The symbols of more than one character, the longest first ([`load_symbols`])."""
    if _LONG is None:
        raise RuntimeError("fmt_props.load_symbols was not called")
    return _LONG


_CONTINUING = None
_LONG = None
NUMBER = re.compile(r"0[xXbB][0-9A-Za-z_]*|[0-9][0-9_]*(?:\.[0-9][0-9_]*)?(?:[eE][+-]?[0-9_]+)?")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
OPENERS = {"(": ")", "[": "]", "{": "}"}
CLOSERS = {")", "]", "}"}


@dataclass(frozen=True)
class Tok:
    kind: str  # code, comment, nl
    start: int
    end: int
    text: str


def tokenize(text):
    """The tokens of `text`: code tokens, comments (to the end of the line)
    and newlines. A string or a character is one token (they do not span
    lines, §2.4); an unknown character is a token of its own. A tuple, kept
    for the texts read last (each input and its output are read by several
    properties), per set of symbols ([`load_symbols`])."""
    return _tokenize(text, _LONG)


@functools.lru_cache(maxsize=64)
def _tokenize(text, symbols):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == "\n" or text.startswith("\r\n", i):  # a line ends with LF or CR LF (§2.5)
            j = i + (1 if c == "\n" else 2)
            out.append(Tok("nl", i, j, text[i:j]))
            i = j
            continue
        if c in " \t\r":
            i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            if j > i and text[j - 1] == "\r":  # a CR LF ends the line (§2.5)
                j -= 1
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] not in (c, "\n"):
                j += 2 if text[j] == "\\" else 1
            j = min(n, j + 1) if j < n and text[j] == c else min(j, n)
        elif c in "0123456789":
            j = NUMBER.match(text, i).end()
        elif c.isascii() and (c.isalpha() or c == "_"):
            j = IDENT.match(text, i).end()
        else:
            j = i + next((len(op) for op in long_symbols() if text.startswith(op, i)), 1)
        out.append(Tok("comment" if text.startswith("//", i) else "code", i, j, text[i:j]))
        i = j
    return tuple(out)


@dataclass
class Line:
    start: int  # offset of the first character
    end: int  # offset of the newline (or the end of the text)
    toks: list  # the code tokens and the comment of the line

    @property
    def code(self):
        return [t for t in self.toks if t.kind == "code"]

    @property
    def comment(self):
        return next((t for t in self.toks if t.kind == "comment"), None)


def lines_of(text, toks):
    lines, start, cur = [], 0, []
    for t in toks:
        if t.kind == "nl":
            lines.append(Line(start, t.start, cur))
            start, cur = t.end, []
        else:
            cur.append(t)
    lines.append(Line(start, len(text), cur))
    return lines


def contexts(toks):
    """For each code token, the innermost open bracket before it (or None),
    and for each opening bracket, whether a `,` stands directly inside it."""
    stack, ctx, has_comma = [], {}, {}
    for t in toks:
        if t.kind != "code":
            continue
        ctx[t.start] = stack[-1].text if stack else None
        if t.text in OPENERS:
            stack.append(t)
            has_comma[t.start] = False
        elif t.text in CLOSERS and stack:
            stack.pop()
        elif t.text == "," and stack:
            has_comma[stack[-1].start] = True
    return ctx, has_comma


def attribute_only(line):
    """The line is an attribute and nothing else (`@repr(c)`): it continues (§2.5)."""
    code = line.code
    if len(code) < 2 or code[0].text != "@" or not IDENT.fullmatch(code[1].text):
        return False
    rest = code[2:]
    if not rest:
        return True
    if rest[0].text != "(":
        return False
    depth = 0
    for k, t in enumerate(rest):
        depth += t.text == "("
        depth -= t.text == ")"
        if depth == 0:
            return k == len(rest) - 1
    return False


# ------------------------------------------------------------ perturbations


def apply(text, edits):
    """Apply (offset, length to delete, text to insert) edits; offsets of the original."""
    for pos, length, ins in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
        text = text[:pos] + ins + text[pos + length:]
    return text


def pick(rng, sites, p):
    """Each site with probability `p`, at least one when there is one."""
    chosen = [s for s in sites if rng.random() < p]
    if sites and not chosen:
        chosen = [rng.choice(sites)]
    return chosen


def blanks(rng, n):
    """`n` blanks, each a space or a tab (§2.5)."""
    return "".join(rng.choice(" \t") for _ in range(n))


def perturb_space(rng, text):
    # The blanks are the space and the tab, and a line ends with LF or CR LF (§2.5, S-201).
    toks = tokenize(text)
    lines = lines_of(text, toks)
    sites = []
    for line in lines:
        row = line.toks
        for a, b in zip(row, row[1:]):
            gap = text[a.end:b.start]
            if gap and set(gap) <= {" ", "\t"}:
                sites.append((a.end, len(gap), None))
            elif not gap and a.kind == "code" and (a.text in ("(", "[", ",") or b.text in (")", "]", ",", ":")):
                sites.append((a.end, 0, None))
        if row:
            indent = row[0].start - line.start
            if set(text[line.start:row[0].start]) <= {" ", "\t"}:
                sites.append((line.start, indent, "indent"))
        if line.comment is None and (row or line.end < len(text)):
            sites.append((line.end, 0, "trail"))  # not after a comment: its text would change
    edits = []
    for pos, length, what in pick(rng, sites, 0.3):
        if what == "indent":
            edits.append((pos, length, blanks(rng, rng.randint(0, 8))))
        else:
            edits.append((pos, length, blanks(rng, rng.randint(1, 4 if what is None else 3))))
    spaced = apply(text, edits)
    # Some line ends as CR LF: a string does not span lines, and a comment
    # ends before its CR LF, so no text but the line ends changes.
    *lines, last = spaced.split("\n")
    return "".join(ln.removesuffix("\r") + ("\r\n" if rng.random() < 0.3 else "\n") for ln in lines) + last


def perturb_blank(rng, text):
    toks = tokenize(text)
    lines = lines_of(text, toks)
    sites = set()
    for i, line in enumerate(lines):
        if i == len(lines) - 1 and line.start == len(text):
            break  # after the final newline
        code = line.code
        if not line.toks and line.end < len(text) and not text[line.start:line.end].strip():
            sites.add(i)  # an empty line already: more of them
        if code and code[0].text in CLOSERS:
            sites.add(i)  # the end of a block or a list
        if code and (code[0].text == "." or code[0].text == "uses"):
            sites.add(i)  # a continuation
        if i > 0:
            prev = lines[i - 1].code
            if prev and (prev[-1].text in ("{", "(", "[") or prev[-1].text in continuing()):
                sites.add(i)  # the start of a block or a list; a continuation
            if attribute_only(lines[i - 1]):
                sites.add(i)
    edits = [(lines[i].start, 0, "\n" * rng.randint(1, 2)) for i in pick(rng, sorted(sites), 0.4)]
    return apply(text, edits)


def perturb_comment(rng, text):
    """The text with markers `// fmtprop-<n>`, numbered in the order of the text."""
    toks = tokenize(text)
    lines = lines_of(text, toks)
    if lines and lines[-1].start == len(text) and len(lines) > 1:
        ends = lines[:-1]
    else:
        ends = lines
    trailing = [i for i, line in enumerate(ends) if line.code and line.comment is None]
    own = list(range(len(lines)))
    sites = [("end", i) for i in trailing] + [("own", i) for i in own]
    chosen = sorted(pick(rng, sites, 0.15), key=lambda s: (s[1], s[0] == "end"))
    edits = []
    n = 0
    for where, i in chosen:
        if where == "end":
            edits.append((lines[i].end, 0, f"  // {MARKER}{n}"))
        else:
            edits.append((lines[i].start, 0, " " * rng.randint(0, 6) + f"// {MARKER}{n}\n"))
        n += 1
    return apply(text, edits)


def perturb_break(rng, text):
    toks = tokenize(text)
    code = [t for t in toks if t.kind != "nl"]
    ctx, has_comma = contexts(toks)
    sites = []
    for a, b in zip(code, code[1:]):
        if a.kind != "code" or b.kind != "code" or "\n" in text[a.end:b.start]:
            continue
        if b.text == "{" or b.text in CLOSERS:
            continue
        if a.text == "," and ctx.get(a.start) in ("(", "["):
            sites.append(a)
        elif a.text in ("(", "[") and has_comma.get(a.start):
            sites.append(a)
    edits = []
    for a in pick(rng, sites, 0.3):
        nxt = next(t for t in code if t.start >= a.end)
        edits.append((a.end, nxt.start - a.end, "\n"))
    return apply(text, edits)


def keywords():
    """The keywords of the spec (§2.2, read as `tools/builtin_names.py` reads them)."""
    global _KEYWORDS
    if _KEYWORDS is None:
        _KEYWORDS = frozenset(builtin_names.keywords(repo.spec_text(ROOT)))
    return _KEYWORDS


_KEYWORDS = None
# Keywords that are operands (§2.2); `_` is an operand too.
OPERAND_WORDS = frozenset(("self", "Self", "true", "false", "_"))


def operand_end(t):
    """`t` ends an operand: a name, a literal, `)`, `]`, `?`."""
    if t.kind != "code":
        return False
    if t.text in (")", "]", "?") or t.text[0] in "\"'0123456789":
        return True
    return IDENT.fullmatch(t.text) is not None and (t.text in OPERAND_WORDS or t.text not in keywords())


def perturb_continue(rng, text):
    """Line breaks that continue a line (§2.5, S-47, R-58): after a binary
    operator between two operands, after the `=` of `let` / `var` / `const` /
    `type`, after a `->`, before `uses`, and before the `.` of a method call
    after `)`. A break in the head of a block leaves its `{` on the head's
    last line (S-202); no break goes before a `{`."""
    toks = tokenize(text)
    lines = lines_of(text, toks)
    sites = []
    for line in lines:
        code = line.code
        for k in range(1, len(code) - 1):
            a, b = code[k], code[k + 1]
            if b.text == "{":
                continue
            spaced = a.end < b.start and code[k - 1].end < a.start  # an operator written apart
            if a.text in continuing() and a.text not in ("=", "->") and operand_end(code[k - 1]) and spaced:
                sites.append((a.end, b.start))
            elif a.text == "=" and code[0].text in ("let", "var", "const", "type") and spaced:
                sites.append((a.end, b.start))
            elif a.text == "->" and spaced:
                sites.append((a.end, b.start))
            elif b.text == "uses" and a.end < b.start:
                sites.append((a.end, b.start))
            elif a.text == ")" and b.text == "." and k + 2 < len(code) and IDENT.fullmatch(code[k + 2].text):
                sites.append((a.end, b.start))
    edits = [(x, y - x, "\n") for x, y in pick(rng, sites, 0.3)]
    return apply(text, edits)


# The tokens of `inside` (spec §2.5): `as` and `at` have no rule of place, and
# inside a bracket a line break before or after them is whitespace, as before
# and after `:`, `=>` and `;` (S-374, S-505); so is one between a keyword in
# an expression and its operand (`if`, `match`, `else if`, `with`, `move`,
# `inout`). The `if` of a guard and the `inout` of a parameter are taken too:
# inside the brackets a line break is whitespace, and the rules of place,
# a closed list, name neither (§2.5).
INSIDE_SYMBOLS = frozenset(("as", "at", ":", "=>", ";"))
INSIDE_KEYWORDS = frozenset(("if", "match", "with", "move", "inout"))


def inside_sites(text):
    """[(a, b)]: the pairs of code tokens between which `inside` may put a
    line break. The gap is one `break_places` counts `removable` (inside a
    bracket of a list, in an element, no line break and no comment there; not
    after a `,` or a `return`, which it does not count), and it is listed:
    before or after a token of INSIDE_SYMBOLS, or after a keyword of
    INSIDE_KEYWORDS followed by a blank (not the `~` of `if~`). Never before a
    `{` (§2.5: it stays on the line of its form), and never after a `.` nor
    after a keyword that follows one: there it is a name (§2.2, `xs.at(0)`),
    and no line break goes after a `.` or before a postfix `(` (§2.5)."""
    code, places = gap_places(text)
    sites = []
    for j, place, nl, _, comment, _ in places:
        a, b = code[j - 1], code[j]
        if place != "removable" or nl or comment or a.text in (",", "return", ".") or b.text == "{":
            continue
        name = j >= 2 and code[j - 2].text == "."
        word = a.text in INSIDE_SYMBOLS or (a.text in INSIDE_KEYWORDS and a.end < b.start)
        if b.text in INSIDE_SYMBOLS or (word and not name):
            sites.append((a, b))
    return sites


def perturb_inside(rng, text):
    """Line breaks inside an element, which fmt removes (S-497), at the
    places of `inside_sites`; 2 in 10 of them a blank line (`spec/tools.md`
    §3.2 removes it too). The blanks round the place go."""
    edits = [(a.end, b.start - a.end, "\n\n" if rng.random() < 0.2 else "\n")
             for a, b in pick(rng, inside_sites(text), 0.3)]
    return apply(text, edits)


def perturb(kind, rng, text):
    if kind == "space":
        return perturb_space(rng, text)
    if kind == "blank":
        return perturb_blank(rng, text)
    if kind == "comment":
        return perturb_comment(rng, text)
    if kind == "break":
        return perturb_break(rng, text)
    if kind == "continue":
        return perturb_continue(rng, text)
    if kind == "inside":
        return perturb_inside(rng, text)
    if kind == "mixed":
        return perturb_space(rng, perturb_blank(rng, perturb_comment(rng, text)))
    raise ValueError(kind)


def inputs_of(path, text, per_kind, version=VERSION):
    """[(label, kind, text)] of a source: itself, then the perturbed inputs."""
    out = [("source", None, text)]
    for kind in KINDS:
        for k in range(per_kind):
            rng = fuzz.seeded_random(version, path, text, kind, str(k))
            p = perturb(kind, rng, text)
            if p != text:
                out.append((f"{kind}#{k}", kind, p))
    return out


# ------------------------------------------------------- comments and lines


def is_doc(comment):
    """`///` (not `////`, §2.1) and `//!` are doc comments."""
    return (comment.startswith("///") and not comment.startswith("////")) or comment.startswith("//!")


def comment_texts(text):
    """(plain comments, doc comments): the texts of the comments in order, without trailing blanks (§2.5)."""
    plain, docs = [], []
    for t in tokenize(text):
        if t.kind == "comment":
            (docs if is_doc(t.text) else plain).append(t.text.rstrip(" \t"))
    return plain, docs


def strip_comments(text):
    """`text` without any comment: a line that held only a comment goes, a comment at the end of a line goes."""
    out = []
    for line in text.split("\n"):
        toks = tokenize(line)
        c = next((t for t in toks if t.kind == "comment"), None)
        if c is None:
            out.append(line)
        elif any(t.kind == "code" for t in toks):
            out.append(line[: c.start].rstrip(" \t"))
    return "\n".join(out)


def strip_markers(text):
    """`text` without the marker comments: a marker line goes, a marker at the end of a line goes."""
    out = []
    for line in text.split("\n"):
        if MARKER_LINE.match(line):
            continue
        out.append(MARKER_END.sub("", line))
    return "\n".join(out)


def unperturb(text):
    """`text` with what the perturbations may add taken out, roughly: no
    comment, no empty line, one space between tokens, and a line joined to the
    one before when that ends in `,` `(` `[` or a continuing operator, or when
    it starts with `.` (for shrinking an input that fmt rejects)."""
    out = []
    for line in strip_comments(strip_markers(text)).split("\n"):
        line = re.sub(" +", " ", line.strip(" "))
        if not line:
            continue
        code = [t.text for t in tokenize(line) if t.kind == "code"]
        prev = [t.text for t in tokenize(out[-1]) if t.kind == "code"] if out else []
        if prev and code and (prev[-1] in (",", "(", "[") or prev[-1] in continuing() or code[0] == "."):
            out[-1] = out[-1] + ("" if prev[-1] in ("(", "[") or code[0] == "." else " ") + line
        else:
            out.append(line)
    return "\n".join(out) + "\n"


def line_key(line_toks):
    """A code line as fmt may rewrite it (`spec/tools.md` §3.2, §3.3): without `,` (which fmt moves
    to the element before it, adds and drops), numbers as `#`. Used to pair the lines of a text with the
    lines of its fmt output. The tokens fmt drops (`return`, parentheses) stay: they are deletions for
    the pairing, and a line of brackets or `return` alone keeps a counterpart (`g(` / `a,` / `) // c`)."""
    code = (t.text for t in line_toks if t.kind == "code")
    return tuple("#" if NUMBER.fullmatch(t) else t for t in code if t != ",")


def code_lines(text):
    """(the lines of `text`, the indices of its lines with code). A line whose
    code is `,` alone is none: fmt moves that `,` to the element before it,
    and the comment at the end of the line stays in its place as a line of a
    comment (`spec/tools.md` §3.2, §3.4, S-529)."""
    lines = lines_of(text, tokenize(text))
    return lines, [i for i, line in enumerate(lines) if any(t.text != "," for t in line.code)]


def pair_lines(before, after):
    """({code line of `before`: the code line of `after` that holds its first
    token}, {...: that holds its last token}), the code lines counted among the
    code lines. The tokens of the two texts are paired by their order and
    their content (`line_key`: what the rewrites of fmt remove is a deletion
    and pairs nothing), which also follows lines that fmt joined (an empty
    body `{` / `}` becomes `{}`, `@fp(relaxed` / `)` becomes `@fp(relaxed)`)."""
    def tokens(text):
        lines, code = code_lines(text)
        return [(key, n) for n, i in enumerate(code) for key in line_key(lines[i].toks)]

    tb, ta = tokens(before), tokens(after)
    first, last = {}, {}
    keys = [k for k, _ in tb], [k for k, _ in ta]
    if keys[0] == keys[1]:  # the same tokens (the common case): no matching to do
        blocks = [(0, 0, len(tb))]
    else:
        blocks = difflib.SequenceMatcher(None, *keys, autojunk=False).get_matching_blocks()
    for i, j, size in blocks:
        for k in range(size):
            n, m = tb[i + k][1], ta[j + k][1]
            first.setdefault(n, m)
            last[n] = m
    return first, last


def comment_places(text):
    """{comment: (where, code line)} of every comment of a text. The comment is
    its text (without trailing spaces) and how many comments of the same text
    come before it; `where` is `end` with the number of its line among the
    code lines, or `own` with the number of the next code line (None at the
    end of the text). A comment at the end of a line of a `,` alone is `own`
    ([`code_lines`])."""
    lines, code = code_lines(text)
    ordinal = {i: n for n, i in enumerate(code)}
    out, seen = {}, {}
    for i, line in enumerate(lines):
        c = line.comment
        if c is None:
            continue
        body = c.text.rstrip(" \t")
        key = (body, seen.get(body, 0))
        seen[body] = key[1] + 1
        if i in ordinal:
            out[key] = ("end", ordinal[i])
        else:
            out[key] = ("own", next((ordinal[j] for j in code if j > i), None))
    return out


def comment_problems(before, after):
    """The comments of `before` that `fmt` (giving `after`) did not keep on the
    line of the same element (R-70, `spec/tools.md` §3.4): a comment at a line end stays at the
    end of the same line; a comment on a line of its own stays on its own line,
    before the same next line (or at the end). The lines are paired by
    `pair_lines`, so a rewrite of fmt (a `return`, a parenthesis) moves nothing.
    A lost comment is the core property's (`comment-text`)."""
    first, last = pair_lines(before, after)
    want, got = comment_places(before), comment_places(after)
    al, ac = code_lines(after)

    def show(n):
        return "the end" if n is None else f"line {ac[n] + 1} `{' '.join(t.text for t in al[ac[n]].code)}`"

    problems = []
    for key, (where, n) in want.items():
        if key not in got:
            continue
        name = key[0] if key[1] == 0 else f"{key[0]} (#{key[1] + 1})"
        h_where, h_n = got[key]
        target = None if n is None else (last if where == "end" else first).get(n, "?")
        if h_where != where:
            problems.append(f"`{name}`: was {'at a line end' if where == 'end' else 'on its own line'}, "
                            f"now {'at a line end' if h_where == 'end' else 'on its own line'}")
        elif target == "?":
            problems.append(f"`{name}`: the line it belonged to has no counterpart in the output")
        elif h_n != target:
            at = "at the end of" if where == "end" else "before"
            problems.append(f"`{name}`: should be {at} {show(target)}, is {at} {show(h_n)}")
    return problems


def item_heads(text):
    """The heads of the items, in order: for each line outside every bracket
    that starts an item (after its attributes `@name(...)` and `pub` / `priv`,
    a keyword of §2.2 that is not an operand), the keyword and the token after
    it (`("fn", "f")`, `("impl", "Show")`). A continued line or a line break
    inside an attribute makes no head."""
    out, depth, last = [], 0, None
    words = keywords() - OPERAND_WORDS - {"pub", "priv"}
    for line in lines_of(text, tokenize(text)):
        code = [t.text for t in line.code]
        # A line that goes on with the line before (§2.5: after a continuing
        # token, or starting with `.` or `uses`) starts no item.
        continued = last in continuing() or (code and code[0] in (".", "uses"))
        if code:
            last = code[-1]
        if code and depth == 0 and not continued:
            k = 0
            while k + 1 < len(code) and code[k] == "@" and IDENT.fullmatch(code[k + 1]):
                k += 2
                if k < len(code) and code[k] == "(":
                    level = 0
                    for m in range(k, len(code)):
                        level += code[m] == "("
                        level -= code[m] == ")"
                        if level == 0:
                            break
                    k = m + 1
            while k < len(code) and code[k] in ("pub", "priv"):
                k += 1
            if k < len(code) and code[k] in words:
                out.append(tuple(code[k:k + 2]))
        for t in line.code:
            if t.text in OPENERS:
                depth += 1
            elif t.text in CLOSERS:
                depth = max(0, depth - 1)
    return out


def sequence_problem(what, want, got):
    """The first difference of two sequences, or None."""
    if want == got:
        return None
    for i, (a, b) in enumerate(zip(want, got)):
        if a != b:
            return f"{what} #{i + 1}: {a!r} became {b!r}"
    if len(want) > len(got):
        return f"{what}: {len(want) - len(got)} lost, from {want[len(got)]!r}"
    return f"{what}: {len(got) - len(want)} more, from {got[len(want)]!r}"


# The places of the line breaks of `break_places`: fmt keeps the writer's
# line break there or not, and adds none (`spec/tools.md` §3.2).
KEPT_PLACES = ("open", "line", "element", "comment", "continue")


def attribute_ends(code):
    """The indices in `code` (the code tokens) of the last token of each
    attribute: the name of `@name`, the `)` of `@name(...)`."""
    ends = set()
    for j, t in enumerate(code[:-1]):
        if t.text != "@" or not IDENT.fullmatch(code[j + 1].text):
            continue
        k = j + 1
        if k + 1 < len(code) and code[k + 1].text == "(" and code[k + 1].start == code[k].end:
            level = 0
            for k in range(k + 1, len(code)):
                level += code[k].text == "("
                level -= code[k].text == ")"
                if level == 0:
                    break
        ends.add(k)
    return ends


def brace_lists(code):
    """{index of a `{` in `code`: whether it opens a list (§3.2) rather than a
    block or a body of items}, read from the text alone: a `,` or a `=>`
    directly inside it (the elements, the arms), a `uses` or a `.` before it
    (an effect row, a `use` list), or a name and a `:` or a `..` first inside
    it (a field: no statement starts so). A `{` of one element without a `:`
    (`S { x }`, `E { A }`) reads as a block: its line breaks are those of its
    brackets."""
    match, stack = {}, []
    for j, t in enumerate(code):
        if t.text in OPENERS:
            stack.append(j)
        elif t.text in CLOSERS and stack:
            match[stack.pop()] = j
    out = {}
    for j, t in enumerate(code):
        if t.text != "{" or j not in match:
            continue
        close, k, direct = match[j], j + 1, []
        while k < close:
            direct.append(code[k].text)
            k = match.get(k, k) + 1
        first = code[j + 1:j + 3]
        out[j] = (
            "," in direct or "=>" in direct
            or (j > 0 and code[j - 1].text in ("uses", "."))
            or (len(first) == 2 and IDENT.fullmatch(first[0].text) is not None and first[1].text == ":")
            or (bool(first) and first[0].text == "..")
        )
    return out


def break_places(text):
    """[(key, place, line break, blank line, comment, line)]: the gap before
    each code token of `text` but the `,` and the `return` (the tokens fmt
    drops or moves, §3.2, §3.3: their gaps join the gap after them), keyed by
    the token (a number as `#`, its spelling may change). The place is one of
    KEPT_PLACES, `removable` or None (fmt may add or remove a line break there):

        None       before a closing bracket (the form, §3.2), after the `{`
                   of a block or a body (fmt adds the line break of a block
                   over more than one line), after an attribute (fmt adds the
                   line break of an item and of an input in the block form,
                   and removes that of a `let`), before an attribute in a list
                   (the block form, S-501);
        open       after an opening bracket of a list or an enclosure (the form);
        line       outside every bracket or in a block or a body (the line
                   breaks that end statements and items, and continuations);
        element    between two elements of a list (a `,` between);
        comment    a comment in the gap (§3.4: the line break after it stays);
        continue   a continuation (§2.5): after a symbol of `continuing()`,
                   before `.` and `uses`;
        removable  any other gap inside an element: fmt removes the line
                   break (S-497, S-505)."""
    code, places = gap_places(text)
    return [("#" if NUMBER.fullmatch(code[j].text) else code[j].text, *rest) for j, *rest in places]


def gap_places(text):
    """(the code tokens of `text`, [(index of the token, place, line break,
    blank line, comment, line)]): [`break_places`] with the index of each
    token in place of its key."""
    toks = tokenize(text)
    code = [t for t in toks if t.kind == "code"]
    # The gap before each code token: line breaks, blank lines, comments.
    gaps, nl, run, blank, comment, line, line_of = [], 0, 0, False, False, 1, []
    for t in toks:
        if t.kind == "nl":
            nl, run, line = nl + 1, run + 1, line + 1
            blank = blank or run >= 2
        elif t.kind == "comment":
            comment, run = True, 0
        else:
            gaps.append((nl > 0, blank, comment))
            line_of.append(line)
            nl, run, blank, comment = 0, 0, False, False
    ends, lists = attribute_ends(code), brace_lists(code)
    out, stack, merged, a = [], [], None, None
    for j, t in enumerate(code):
        g = gaps[j]
        merged = g if merged is None else (merged[0] or g[0], merged[1] or g[1], merged[2] or g[2])
        comma = a is not None and any(code[k].text == "," for k in range(a + 1, j))
        if t.text in (",", "return"):
            pass
        else:
            if a is not None:
                top = stack[-1] if stack else None
                block = top is not None and code[top].text == "{" and not lists.get(top, False)
                if t.text in CLOSERS:
                    place = None
                elif a == top:
                    place = None if block else "open"
                elif a in ends:
                    place = None
                elif top is None or block:
                    place = "line"
                elif t.text == "@":
                    place = None
                elif comma:
                    place = "element"
                elif merged[2]:
                    place = "comment"
                elif code[a].text in continuing() or t.text in (".", "uses"):
                    place = "continue"
                else:
                    place = "removable"
                out.append((j, place, merged[0], merged[1], merged[2], line_of[j]))
            a, merged = j, None
        if t.text in OPENERS:
            stack.append(j)
        elif t.text in CLOSERS and stack:
            stack.pop()
    return code, out


def break_problems(before, after):
    """The places where `after` (fmt of `before`) does not keep the line
    breaks of the writer (`spec/tools.md` §3.2): a line break at a place
    of KEPT_PLACES that is gone or added, a line break inside an element
    (`removable`) that stays or is added, and a blank line between two
    elements of a list that is gone or added (S-499). Without the CST: the
    text, its tokens and its brackets (`break_places`), so the check shares
    no judgement with the formatter. The gaps are paired by their tokens (a
    difference in the tokens, which the rewrites of §3.3 that `break_places`
    leaves out do not make, is a problem too); a gap whose comment moved (the
    failure `comments`) is not judged."""
    want, got = break_places(before), break_places(after)
    keys = [w[0] for w in want], [g[0] for g in got]
    problems = []
    if keys[0] == keys[1]:  # the same tokens (the common case): no matching to do
        blocks = [(0, 0, len(want))]
    else:
        # A rewrite that `break_places` does not leave out: the gaps round it are not judged, so say so.
        problems.append(sequence_problem("token (but `,` and `return`)", *keys))
        blocks = difflib.SequenceMatcher(None, *keys, autojunk=False).get_matching_blocks()
    for i, j, size in blocks:
        for k in range(1 if i or j else 0, size):
            (key, place, nl, blank, comment, line), (_, _, out_nl, out_blank, out_comment, _) = want[i + k], got[j + k]
            if place is None or comment != out_comment:
                continue
            where = f"line {line}, before `{key}` ({place})"
            if place == "removable" and out_nl:
                problems.append(f"{where}: the line break inside an element stays")
            elif place in KEPT_PLACES and nl != out_nl:
                problems.append(f"{where}: the line break of the writer is {'gone' if nl else 'added'}")
            elif place == "element" and nl and blank != out_blank:
                problems.append(f"{where}: the blank line between the elements is {'gone' if blank else 'added'}")
    return problems


# --------------------------------------------------------------- running


@dataclass(frozen=True)
class Failure:
    # unread, perturbation, rejected, internal, ast, idempotence, comment-text,
    # docs, items, depth, breaks, meaning, convergence, comments, cst
    prop: str
    case: str
    label: str
    detail: str
    text: str  # the input


class Onsa:
    def __init__(self, argv, work):
        self.argv = list(argv)
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)

    def run(self, *args):
        """(exit code, stdout bytes, stderr str); the code is None on a timeout."""
        try:
            r = subprocess.run([*self.argv, *map(str, args)], capture_output=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return None, b"", f"more than {TIMEOUT} s"
        return r.returncode, r.stdout, r.stderr.decode("utf-8", "replace")

    def crash(self, cmd, code, err):
        """The crash (internal error, signal, raw panic, time out) of a run, or None."""
        c = fuzz.classify(cmd, code, err, timed_out=code is None)
        return None if c is None else f"{c.command}: {c.signature}"


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(fuzz.encode(text))
    return path


def fmt_text(onsa, path, text):
    """Format `text` written to `path`: (the formatted text or None, the failure or None).
    The failure is ("internal", what) or ("rejected", what)."""
    write(path, text)
    code, _, err = onsa.run("fmt", path)
    crash = onsa.crash(("fmt",), code, err)
    if crash:
        return None, ("internal", crash)
    if code != 0:
        return None, ("rejected", f"fmt exit {code}: " + " | ".join(err.strip().splitlines()[:2]))
    return fuzz.decode(path.read_bytes()), None


@dataclass(frozen=True)
class Baseline:
    path: Path  # the source, written
    formatted: str  # fmt(x)
    tokens: tuple  # written_tokens(fmt(x))
    levels: list  # the levels of the items of x (`dump --levels`), None when they failed


def written_tokens(text):
    """The code tokens of `text` but `,`, which fmt adds and drops by the form
    of a list (`spec/tools.md` §3.2): two outputs of fmt with the same rewrites
    (§3.3) of the same program have the same."""
    return tuple(t.text for t in tokenize(text) if t.kind == "code" and t.text != ",")


def diff_ast(onsa, a, b):
    """The failure of `onsa diff --ast a b` as (prop, detail), or None when there is no difference."""
    code, out, err = onsa.run("diff", "--ast", a, b)
    crash = onsa.crash(("diff", "--ast"), code, err)
    if crash:
        return "internal", crash
    if code != 0:
        return "ast", f"diff --ast exit {code}: " + " | ".join(fuzz.decode(out).strip().splitlines()[:3])
    return None


def check_input(onsa, d, name, case, label, kind, text, base, prop):
    """The failures of one input. `base` is the Baseline of the source (None
    for the source itself). Returns (failures, the Baseline of this input or
    None when fmt did not accept it)."""
    fails = []

    def fail(what, detail):
        fails.append(Failure(what, case, label, detail.strip(), text))

    if prop == "cst":
        code, out, err = onsa.run("dump", "--cst", write(d / "a" / name, text))
        crash = onsa.crash(("dump", "--cst"), code, err)
        if crash:
            fail("internal", crash)
        elif code != 0:
            fail("cst", f"dump --cst exit {code}: " + " | ".join(err.strip().splitlines()[:1]))
        elif out != fuzz.encode(text):
            fail("cst", "the output is not the source")
        return fails, None

    a = write(d / "a" / name, text)
    if base is not None:
        # The perturbation itself changes no program (§2.5).
        problem = diff_ast(onsa, base.path, a)
        if problem:
            fail("perturbation" if problem[0] == "ast" else problem[0], "x and p: " + problem[1])

    b = d / "b" / name
    formatted, problem = fmt_text(onsa, b, text)
    if problem:
        # The caller decides whether the source itself may be unread.
        if problem[0] == "internal" or label != "source":
            fail(*problem)
        return fails, None

    problem = diff_ast(onsa, a, b)
    if problem:
        fail(*problem)
    code, out, err = onsa.run("fmt", "--check", b)
    crash = onsa.crash(("fmt", "--check"), code, err)
    if crash:
        fail("internal", crash)
    elif code != 0:
        fail("idempotence", f"fmt --check exit {code} on fmt(p)")
    # `spec/tools.md` §3.5: the comments keep their texts in their order, and the doc comments
    # and the items stay. `diff --ast` compares the structure alone, not the comments nor the doc
    # comments (S-534): these sequences check those, and the items once more.
    (plain, docs), (f_plain, f_docs) = comment_texts(text), comment_texts(formatted)
    for what, want, got, prop_name in (
        ("comment", plain, f_plain, "comment-text"),
        ("doc comment", docs, f_docs, "docs"),
        ("item", item_heads(text), item_heads(formatted), "items"),
    ):
        problem = sequence_problem(what, want, got)
        if problem:
            fail(prop_name, problem)
    problems = break_problems(text, formatted)
    if problems:
        more = f" (and {len(problems) - 1} more)" if len(problems) > 1 else ""
        fail("breaks", problems[0] + more)
    for problem in comment_problems(text, formatted):
        fail("comments", problem)
    if base is not None:
        convergence_problems(onsa, d / "c" / name, kind, formatted, base, fail)

    # 5 and 8 on `x`, on the inputs with markers, and on an input whose rewrites differ from those of `x`.
    tokens, levels = written_tokens(formatted), None if base is None else base.levels
    if base is None:
        levels, problem = levels_of(onsa, a)
        if not problem and item_heads(text) and not levels:
            levels, problem = None, ("depth", "dump --levels printed no item")
        if problem:
            fail(*problem)
    elif kind not in CONVERGES_STRIPPED and tokens == base.tokens:
        return fails, Baseline(a, formatted, tokens, levels)
    if levels is not None:
        problem = depth_problem(onsa, levels, b)
        if problem:
            fail(*problem)
    if formatted != text:
        problem = meaning_problem(onsa, a, b)
        if problem:
            fail(*problem)
    return fails, Baseline(a, formatted, tokens, levels)


def convergence_problems(onsa, path, kind, formatted, base, fail):
    """The normal form with the comments (7): `fmt(p) == fmt(x)` for space and
    blank; for comment and mixed, `fmt(p)` without the markers, written to
    `path` and formatted again, is `fmt(x)`."""
    if kind in CONVERGES and formatted != base.formatted:
        fail("convergence", "fmt(p) is not fmt(x): " + first_difference(base.formatted, formatted))
    if kind in CONVERGES_STRIPPED:
        again, problem = fmt_text(onsa, path, strip_markers(formatted))
        if problem:
            fail(problem[0], "on fmt(p) without the markers: " + problem[1])
        elif again != base.formatted:
            fail("convergence", "fmt(p) without the markers is not fmt(x): " + first_difference(base.formatted, again))


def levels_of(onsa, path):
    """The levels of each item of `path` (`onsa dump --levels`), or the failure as (prop, detail)."""
    code, out, err = onsa.run("dump", "--levels", path)
    crash = onsa.crash(("dump", "--levels"), code, err)
    if crash:
        return None, ("internal", crash)
    if code != 0:
        return None, ("depth", f"dump --levels exit {code}: " + " | ".join(err.strip().splitlines()[:1]))
    return [int(x) for x in fuzz.decode(out).split()], None


def depth_problem(onsa, want, after):
    """The failure when `after` (fmt of a program whose items have the levels `want`) has an item
    deeper, or None."""
    got, problem = levels_of(onsa, after)
    if problem:
        return problem
    if len(want) != len(got):
        return "depth", f"{len(want)} items before fmt, {len(got)} after"
    for i, (w, g) in enumerate(zip(want, got)):
        if g > w:
            return "depth", f"item {i + 1}: {w} levels before fmt, {g} after"
    return None


# A diagnostic of `onsa check` in the text form: `<path>:<line>:<column>: error[E0401]: ...`.
DIAGNOSTIC = re.compile(r"^\S.*?:\d+:\d+: (?:error|warning)\[([A-Z]\d{4})\]", re.M)


def verdict(onsa, path):
    """`onsa check path` as (its exit code, the codes of its diagnostics in order), or the failure
    as (prop, detail)."""
    code, out, err = onsa.run("check", path)
    crash = onsa.crash(("check",), code, err)
    if crash:
        return None, ("internal", crash)
    codes = DIAGNOSTIC.findall(fuzz.decode(out) + "\n" + err)
    if code == 1 and not codes:
        return None, ("meaning", "onsa check ended with 1 and printed no diagnostic this item reads")
    return (code, codes), None


def meaning_problem(onsa, before, after):
    """The failure when `onsa check` judges `after` (fmt of `before`) otherwise than `before`: its
    exit code or the codes of its diagnostics in their order (not their texts nor their places), or
    None (spec §18.2)."""
    want, problem = verdict(onsa, before)
    if problem:
        return problem
    got, problem = verdict(onsa, after)
    if problem:
        return problem
    if want == got:
        return None

    def show(v):
        return f"exit {v[0]}, " + (" ".join(v[1]) or "no diagnostic")

    return "meaning", f"onsa check before fmt: {show(want)}; after fmt: {show(got)}"


def first_difference(want, got):
    w, g = want.split("\n"), got.split("\n")
    for i in range(max(len(w), len(g))):
        a = w[i] if i < len(w) else "<end>"
        b = g[i] if i < len(g) else "<end>"
        if a != b:
            return f"line {i + 1}: fmt(x) {a!r}, fmt(p) {b!r}"
    return "the same lines"


@dataclass(frozen=True)
class Source:
    path: str  # from the root
    text: str
    unread_ok: str = None  # why fmt may refuse it (None: it must read it)


def sources(root, cmd):
    """[Source] of the case files (`onsa_cases`, in its order), then of `std/`
    and `examples/`. fmt may refuse a case file only when the case is listed in
    `tests/pending.toml` as a whole `test-case`, when the lexer or the parser
    reports a diagnostic on the file (`onsa_cases`, from the compiler's own
    `Parsed::syntax_errors`, the decision of `fmt` itself), or when its mode is
    `none`."""
    root = Path(root)
    entries, _ = pending.load(root / repo.PENDING)  # the item `pending` reports the errors
    whole = {e.target for e in pending.of_kind(entries, "test-case") if "::" not in e.target}
    out = []
    for c in repo.cases_json(root, cmd):
        for f in c["files"]:
            if c["mode"] == "none":
                why = 'a fragment of `mode = "none"`'
            elif c["path"] in whole:
                why = "a pending test case"
            elif f["syntax_errors"]:
                why = "a file with a syntax diagnostic"
            else:
                why = None
            try:
                out.append(Source(f["path"], fuzz.read_input(root / f["path"]), why))
            except OSError:
                continue
    for top in OTHER_SOURCES:
        for p in sorted((root / top).rglob("*.onsa")):
            rel = p.relative_to(root).as_posix()
            if not repo.is_build_output(root, rel):
                out.append(Source(rel, fuzz.read_input(p)))
    return out


def run(root, argv, prop, per_kind, version, jobs, cases_cmd, out=print, target_dir=None,
        time_budget=TIME_BUDGET, minimize=False, show=20, verbose=False, selection=None):
    """The gate item. `selection` (`narrowing.Selection`, None for the whole run)
    picks the sources. Returns the exit code."""
    root = Path(root)
    work = Path(target_dir or root / "target") / "fmt_props"
    tmp = work / f"work-{os.getpid()}"  # one per process: two runs do not share it
    onsa = Onsa(argv, tmp)
    start = time.time()
    deadline = time.monotonic() + time_budget
    try:
        files = sources(root, cases_cmd)
    except (repo.RepoError, KeyError, OSError) as e:
        out(f"fmt-props: cannot list the sources: {e}")
        return 2
    total = len(files)
    picked = None
    if selection:
        # Each source's inputs depend on that source alone (`inputs_of`): the sources narrow after the list.
        try:
            picked = narrowing.pick([(s.path, s.text) for s in files], selection, root,
                                    () if selection.shard else ALWAYS)
        except narrowing.NarrowError as e:
            out(f"fmt-props: cannot narrow the sources: {e}")
            return 2
        files = [s for s in files if s.path in picked.paths]
    try:
        load_symbols(root, cases_cmd)
    except repo.RepoError as e:
        out(f"fmt-props: cannot read the symbols of the lexer: {e}")
        return 2

    def one_source(src):
        if time.monotonic() > deadline:
            return None
        d = Path(tempfile.mkdtemp(dir=tmp))
        name = Path(src.path).name
        try:
            inputs = inputs_of(src.path, src.text, per_kind, version)
            fails, base = check_input(onsa, d / "0", name, src.path, *inputs[0], None, prop)
            if base is None and prop != "cst":
                if fails:  # it failed inside
                    return ("ran", fails, 1)
                if src.unread_ok:
                    return ("skipped", [], 0)
                why = ("fmt does not read it, and it is not a pending test case, a negative example of a "
                       "syntax code or of mode none")
                return ("ran", [Failure("unread", src.path, "source", why, src.text)], 1)
            ran = 1
            for k, (label, kind, p) in enumerate(inputs[1:], 1):
                if time.monotonic() > deadline:
                    return None
                f, _ = check_input(onsa, d / str(k), name, src.path, label, kind, p, base, prop)
                fails += f
                ran += 1
            return ("ran", fails, ran)
        finally:
            shutil.rmtree(d, ignore_errors=True)

    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(one_source, files))

    problems = []
    skipped = [f"{s.path} ({s.unread_ok})" for s, r in zip(files, results) if r and r[0] == "skipped"]
    ran_sources = sum(1 for r in results if r and r[0] == "ran")
    late = sum(1 for r in results if r is None)
    if late:
        problems.append(f"the time budget ({time_budget} s) ran out: {late} of {len(files)} sources did not run")
    if not ran_sources:
        problems.append("no source ran")
    failures = [f for r in results if r for f in r[1]]
    ran = sum(r[2] for r in results if r)
    by_prop = {}
    for f in failures:
        by_prop.setdefault(f.prop, []).append(f)
    out(
        f"fmt-props ({prop}): {ran} inputs from {ran_sources} sources "
        f"({len(skipped)} that fmt may not read, skipped"
        + (f"; picked {picked.describe(total, 'sources')}" if picked else "") + "); "
        + (", ".join(f"{k} {len(v)}" for k, v in sorted(by_prop.items())) or "no failure")
        + f"; {time.time() - start:.1f} s"
    )
    fail_dir = work / "fail" / prop
    shutil.rmtree(fail_dir, ignore_errors=True)
    try:
        for f in failures[:show] if show >= 0 else failures:
            fail_dir.mkdir(parents=True, exist_ok=True)
            saved = fail_dir / (f.case.replace("/", "__").removesuffix(".onsa") + f".{f.label.replace('#', '')}.onsa")
            saved.write_bytes(fuzz.encode(shrink(onsa, f, tmp) if minimize else f.text))
            out(f"FAIL {f.prop}: {f.case} [{f.label}]: {f.detail}\n     input: {saved}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    if show >= 0 and len(failures) > show:
        out(f"... {len(failures) - show} more failures (--show -1 shows all)")
    if verbose:
        for p in skipped:
            out(f"skipped (fmt may not read it): {p}")
    for p in problems:
        out(f"FAIL {p}")
    return 1 if failures or problems else 0


# The properties `shrink` keeps on a smaller input (the others need the source).
SHRINKABLE = (
    "rejected", "internal", "ast", "idempotence", "comment-text", "docs", "items", "depth", "breaks", "meaning",
)
ERROR_CODE = re.compile(r"error\[(E\d{4})\]")


def shrink(onsa, failure, tmp):
    """A smaller input on which the same property fails: for `internal` the
    same crash; for `rejected` the same first code, while the input without
    what the perturbations add (`unperturb`) is still read. The other
    properties need the source: their input stays as it is."""
    if failure.prop not in SHRINKABLE:
        return failure.text
    name = Path(failure.case).name
    tmp.mkdir(parents=True, exist_ok=True)

    def code_of(detail):
        return (ERROR_CODE.findall(detail) or [None])[0]

    def still_fails(candidate):
        d = Path(tempfile.mkdtemp(dir=tmp))
        try:
            if failure.prop == "rejected":
                _, problem = fmt_text(onsa, d / "a" / name, candidate)
                if not problem or problem[0] != "rejected" or code_of(problem[1]) != code_of(failure.detail):
                    return False
                return fmt_text(onsa, d / "b" / name, unperturb(candidate))[1] is None
            fails, _ = check_input(onsa, d, name, failure.case, "shrink", None, candidate, None, "core")
            if failure.prop == "internal":
                return any(f.prop == "internal" and f.detail == failure.detail for f in fails)
            return any(f.prop == failure.prop for f in fails)
        finally:
            shutil.rmtree(d, ignore_errors=True)

    return fuzz.ddmin(failure.text, still_fails)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--property", choices=PROPERTIES, default="core")
    ap.add_argument("--per-kind", type=int, default=PER_KIND, help="perturbed inputs per kind and source")
    ap.add_argument("--version", default=VERSION)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--binary", type=Path, help="the compiler (default: build <target directory>/debug/onsa)")
    ap.add_argument("--time-budget", type=float, default=TIME_BUDGET, help="seconds for the whole run")
    ap.add_argument("--minimize", action="store_true", help="shrink the failing inputs that are shown")
    ap.add_argument("--show", type=int, default=20, help="failures to show (-1: all)")
    ap.add_argument("--verbose", action="store_true", help="also list the sources skipped")
    narrowing.add_arguments(ap)
    args, selection = narrowing.parse(ap, argv)
    if args.per_kind < 0 or args.jobs < 1 or args.time_budget <= 0:
        ap.error("--per-kind must be 0 or more, --jobs 1 or more and --time-budget more than 0")
    target = fuzz.target_directory(args.root)
    if target is None:
        print("fmt-props: cannot read cargo's target directory (cargo metadata)", file=sys.stderr)
        return 2
    binary = args.binary
    if binary is None:
        if not fuzz.build(args.root):
            print("fmt-props: cannot build the compiler (cargo build -p onsa_cli)", file=sys.stderr)
            return 2
        binary = target / "debug" / "onsa"
    return run(
        args.root, [str(binary)], args.property, args.per_kind, args.version, args.jobs, repo.CASES_CMD,
        target_dir=target, time_budget=args.time_budget, minimize=args.minimize, show=args.show,
        verbose=args.verbose, selection=selection,
    )


if __name__ == "__main__":
    sys.exit(main())
