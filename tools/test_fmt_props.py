#!/usr/bin/env python3
"""Self-tests of tools/fmt_props.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_fmt_props.py
"""
import re
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fmt_props  # noqa: E402
import narrowing  # noqa: E402
from selftest_support import entry, TempRepo  # noqa: E402


FAKE_FMT = r"""
import re, sys
args = sys.argv[1:]
def norm(t):
    t = t.replace("\r\n", "\n")
    if "LAYOUT" in t and re.search(r"[,(]$", t, re.M):  # a rewrite that depends on the line breaks
        t = t.replace('"a.b"', '"a. b"')
    lines = [re.sub(r" +([)\],:])", r"\1", re.sub(r"([(\[]) +", r"\1", re.sub(r"[ \t]+", " ", l.strip())))
             for l in t.split("\n")]
    if "KEEP_INDENT" in t:
        lines = [l.rstrip() for l in t.split("\n")]
    if "DROP" in t:
        lines = [l for l in lines if "drop" not in l]
    if "LOSE_COMMENT" in t:
        lines = [re.sub(r" *// lose.*", "", l) for l in lines]
    if "LOSE_DOC" in t:
        lines = [l for l in lines if not l.startswith("///")]
    if "MOVE_COMMENT" in t:  # the comment `// mv` at a line end goes to a line of its own before it
        moved = [re.match(r"(.*\S) +(// mv.*)$", l) for l in lines]
        lines = [y for l, m in zip(lines, moved) for y in ((m.group(2), m.group(1)) if m else (l,))]
    for i in range(len(lines) - 1):  # the line break after it is lost (once: the joined line ends otherwise)
        if lines[i].endswith("JOIN_KEPT = 1"):
            lines[i:i + 2] = [lines[i] + " " + lines[i + 1]]
            break
    return "\n".join(l for l in lines if l).strip("\n") + "\n"
def code(t):
    return re.findall(r"\w+|[^\s\w]", re.sub(r"//[^\n]*", "", t))
def read(p):
    return open(p, encoding="utf-8", newline="").read()
if args[0] in ("fmt", "--fmt"):  # `onsa fmt --check FILE`, `onsa_cases --fmt FILE` (fmt on the standard output)
    path = args[-1]
    t = read(path)
    if "PANIC" in t:
        sys.stderr.write("onsa: internal error: boom\n  = at crates/onsa_syntax/src/fmt.rs:1:1\n")
        sys.exit(101)
    if "REJECT" in t and re.search(r"[ ]$", t, re.M):
        sys.stderr.write(path + ":1:1: error[E0002]: no\n")
        sys.exit(2)
    if args[0] == "--fmt":
        sys.stdout.buffer.write((norm(t) + (" " if "NOT_IDEMPOTENT" in t else "")).encode())
    elif args[1] == "--check":
        sys.exit(0 if norm(t) == t else 1)
    else:  # the item formats no file in place (X-1 U12: it would sync the file to the disk)
        sys.stderr.write("fake onsa: fmt in place\n")
        sys.exit(3)
elif args[0] == "diff":
    a, b = (read(p) for p in args[-2:])
    sys.exit(0 if code(a) == code(b) else 1)
elif args[0] == "check":
    # An E0401 for each `VERDICT` followed by two spaces or more (fmt makes it one: the verdict changes),
    # and for each line with `PLACE` (fmt moves the line: the place changes, not the code).
    t = read(args[-1])
    lines = t.split("\n")
    found = [(1, "the verdict") for _ in re.findall(r"VERDICT {2,}", t)]
    found += [(i + 1, f"at line {i + 1}") for i, l in enumerate(lines) if "PLACE" in l]
    found += [(1, "the string") for _ in re.findall(r'"a\. b"', t)]
    for line, what in found:
        sys.stdout.write(f"{args[-1]}:{line}:1: error[E0401]: {what}\n")
    sys.exit(1 if found or "SILENT" in t else 0)
elif args[0] == "dump" and args[1] == "--levels":
    # one item; the output of fmt (written under b/) is deeper when the source says DEEPER
    t = read(args[-1])
    sys.stdout.write("2\n" if "DEEPER" in t and "/b/" in args[-1].replace("\\", "/") else "1\n")
elif args[0] == "dump":
    t = read(args[-1])
    sys.stdout.write(t.strip() if "CST_BAD" in t else t)
"""


class FmtProps(TempRepo):
    SOURCE = (
        "pub fn f(x: I32, ys: [I32; 2]) -> I32 { // head\n"
        "  let a = g(x, ys[0]) + -x // tail\n"
        "  let s = saw~(a, 1)\n"
        "  buf.push!(x)\n"
        "  let y = x + prev~(^y)\n"
        "  if !done {\n"
        "    \"a // not a comment, (x) [y]\"\n"
        "  } else {\n"
        "    'c'\n"
        "  }\n"
        "\n"
        "  return x *% 2\n"
        "}\n"
    )

    # The answer of the fake `onsa_cases --continuing` (the compiler's is
    # `onsa_tests::inventory::continuing_spellings`, tested there).
    CONTINUING = "+ - * / % == != < > <= >= && || & | ^ << >> +% -% *% +| -| *| ..< ..= = ->".split()
    SYMBOLS = "!== ... ..< ..= === != && *% ** *| +% ++ +| -% -- -> -| .. :: << <= == => >= >> ||".split()

    def cases_cmd(self, listed):
        """A fake `onsa_cases`: the cases `listed`, or the continuing symbols."""
        return (sys.executable, "-B", "-c",
                f"import json, sys; print(json.dumps({self.CONTINUING!r} if '--continuing' in sys.argv else "
                f"{self.SYMBOLS!r} if '--symbols' in sys.argv else {listed!r}))")

    def setUp(self):
        super().setUp()
        self.fake = self.repo.write("fake_onsa.py", FAKE_FMT)
        self.argv = [sys.executable, "-B", str(self.fake)]
        fmt_props.load_symbols(self.repo.root, self.cases_cmd([]))

    def go(self, prop="core", per_kind=1, cases=None, minimize=False):
        """Run the item over `tests/spec/a.onsa` (or `cases`: [(path, mode, syntax_errors)])."""
        cases = cases or [("tests/spec/a.onsa", "check", False)]
        listed = [{"path": p, "kind": "file", "mode": m, "files": [{"path": p, "syntax_errors": s}]}
                  for p, m, s in cases]
        cmd = self.cases_cmd(listed)
        lines = []
        code = fmt_props.run(self.repo.root, self.argv, prop, per_kind, "t", 2, cmd, self.argv, out=lines.append,
                             minimize=minimize)
        return code, "\n".join(lines)

    def gaps(self, text):
        """[(token, gap before the next token: none / space / newline, next token)] of the code tokens."""
        toks = [t for t in fmt_props.tokenize(text) if t.kind == "code"]
        out = []
        for a, b in zip(toks, toks[1:]):
            gap = text[a.end:b.start]
            gap = re.sub(r"//[^\n]*", "", gap)
            out.append((a.text, "newline" if "\n" in gap else "space" if gap else "none", b.text))
        return out

    def test_tokenize(self):
        toks = fmt_props.tokenize('let s = "a // b" // c\nx->y..=z \'"\' +%')
        self.assertEqual(
            [(t.kind, t.text) for t in toks],
            [("code", "let"), ("code", "s"), ("code", "="), ("code", '"a // b"'), ("comment", "// c"), ("nl", "\n"),
             ("code", "x"), ("code", "->"), ("code", "y"), ("code", "..="), ("code", "z"), ("code", "'\"'"),
             ("code", "+%")],
        )
        # The range symbols are one token each (S-257).
        self.assertEqual([t.text for t in fmt_props.tokenize("0..<n 0..=n")], ["0", "..<", "n", "0", "..=", "n"])

    def test_perturbations_keep_the_places_where_whitespace_means_something(self):
        # C-118: no space before a postfix `(` / `[`, around `~` `!` `^` and the prefix `-`; no newline
        # removed, none added before `{` / `else`, nor before an attached `(` / `[`
        before = self.gaps(self.SOURCE)
        comments = [t.text for t in fmt_props.tokenize(self.SOURCE) if t.kind == "comment"]
        inputs = fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 20, "t")[1:]
        # The gaps (by the index of the token after them) that `break_places` counts inside an element.
        removable = {j for j, place, *_ in fmt_props.gap_places(self.SOURCE)[1] if place == "removable"}
        inside = fmt_props.INSIDE_SYMBOLS | fmt_props.INSIDE_KEYWORDS
        # The blanks are the space and the tab, and a line ends with LF or CR LF (§2.5, S-201): the
        # perturbations use both, and never a CR alone.
        self.assertTrue(any("\t" in p for _, _, p in inputs) and any("\r\n" in p for _, _, p in inputs))
        for label, kind, p in inputs:
            with self.subTest(label=label):
                after = self.gaps(p)
                self.assertEqual([(a, b) for a, _, b in after], [(a, b) for a, _, b in before])
                for i, ((a, g0, b), (_, g1, _)) in enumerate(zip(before, after)):
                    if g0 == "newline":
                        self.assertEqual(g1, "newline", (a, b))
                    if g1 == "newline" and g0 != "newline":
                        self.assertIn(kind, ("break", "continue", "inside", "mixed"))
                        self.assertNotIn(b, ("{", "else", "with"))
                        if b in ("(", "["):  # not a postfix one: after a list's opening or `,`, or a type after `:`
                            self.assertIn(a, ("(", "[", ",") if kind != "inside" else inside)
                        if kind == "inside":  # inside an element, before or after a token of §2.5's list
                            self.assertIn(i + 1, removable, (a, b))
                            self.assertTrue(a in inside or b in fmt_props.INSIDE_SYMBOLS, (a, b))
                        else:
                            self.assertTrue(a in ("(", "[", ",", "=") or a in fmt_props.continuing() or b == ".", (a, b))
                    if g0 == "none" and g1 == "space":
                        self.assertTrue(a in ("(", "[", ",") or b in (")", "]", ",", ":"), (a, b))
                self.assertNotRegex(p, r"\r(?!\n)")
                # the string, the character and the comments are untouched (no space after a comment)
                self.assertIn('"a // not a comment, (x) [y]"', p)
                kept = [t.text for t in fmt_props.tokenize(p) if t.kind == "comment" and "fmtprop" not in t.text]
                self.assertEqual(kept, comments)

    def test_the_line_breaks_inside_an_element(self):
        # `inside` (S-497, S-505): only in a gap that `break_places` counts `removable`, before and after `as`
        # `at` `:` `=>` `;`, and after a keyword of an expression followed by a blank (§2.5).
        text = (
            "struct P { @param(min: 0.0) x: F32, y: F32 }\n"
            "fn f[T: Num](x: T, ys: [T; 2]) -> T {\n"
            "  g(x as I64, saw~(a.b, -x)?, if c { 1 } else if d { 2 } else { 3 }, match v { 0 | 1 => 1, _ => 2 })\n"
            "  h(a + b, xs[0], f::[I32](x), fn(y: I32) -> I32 { y }, move m, inout n, if~ c { 1 } else { 2 },\n"
            "    s at clock, S { f: 1 }, !z, 0..<n, xs.at(0), t.as)\n"
            "}\n"
        )
        sites = [(a.text, b.text) for a, b in fmt_props.inside_sites(text)]
        self.assertEqual(sites, [
            ("min", ":"), (":", "0.0"), ("x", ":"), (":", "F32"), ("y", ":"), (":", "F32"),
            ("T", ":"), (":", "Num"), ("x", ":"), (":", "T"), ("ys", ":"), (":", "["), ("T", ";"), (";", "2"),
            ("x", "as"), ("as", "I64"), ("if", "c"), ("if", "d"), ("match", "v"),
            ("1", "=>"), ("=>", "1"), ("_", "=>"), ("=>", "2"),
            ("y", ":"), (":", "I32"), ("move", "m"), ("inout", "n"), ("s", "at"), ("at", "clock"), ("f", ":"), (":", "1"),
        ])
        # Never where §2.5 keeps a token on the line of its neighbour, though the gap is inside an element: a binary
        # operator, a range symbol, the `|` of a pattern, `->`, `?`, a postfix `(` / `[`, `~`, `::`, after `.` and a
        # prefix `!`, `else`, between `else` and `if`, `{`, `fn(`, `@name`, `if~`; and round a keyword after a `.`,
        # which is a name there (§2.2: `xs.at(0)`, `t.as`).
        code, places = fmt_props.gap_places(text)
        removable = {(code[j - 1].text, code[j].text) for j, place, *_ in places if place == "removable"}
        for pair in (("a", "+"), ("0", "..<"), ("0", "|"), (")", "->"), (")", "?"), ("xs", "["), ("]", "("),
                     ("saw", "~"), ("f", "::"), ("::", "["), (".", "b"), ("!", "z"), ("}", "else"), ("else", "if"),
                     ("c", "{"), ("fn", "("), ("@", "param"), ("if", "~"), (".", "at"), ("at", "("), (".", "as")):
            with self.subTest(pair=pair):
                self.assertIn(pair, removable)
                self.assertNotIn(pair, sites)
        # The inputs: line breaks (some of them blank lines) at the sites only; `breaks` finds those that stay, and
        # none in the source, where fmt has removed them all.
        inputs = [p for _, kind, p in fmt_props.inputs_of("tests/spec/a.onsa", text, 10, "t") if kind == "inside"]
        self.assertEqual(len(inputs), 10)
        self.assertTrue(any("\n\n" in p for p in inputs))
        old = {(a, b) for a, gap, b in self.gaps(text) if gap == "newline"}
        for p in inputs:
            with self.subTest(p=p):
                added = {(a, b) for a, gap, b in self.gaps(p) if gap == "newline"} - old
                self.assertTrue(added and added <= set(sites), added)
                problems = fmt_props.break_problems(p, p)
                self.assertTrue(problems and all(x.endswith("the line break inside an element stays") for x in problems))
                self.assertEqual(fmt_props.break_problems(p, text), [])
        # No site: no input.
        kinds = {k for _, k, _ in fmt_props.inputs_of("tests/spec/a.onsa", "fn f() {\n  g(a, b)\n}\n", 3, "t")}
        self.assertNotIn("inside", kinds)

    def test_inputs_are_the_same_for_the_same_tree(self):
        a = fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "1")
        self.assertEqual(a, fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "1"))
        self.assertNotEqual(a, fmt_props.inputs_of("tests/spec/a.onsa", self.SOURCE, 2, "2"))
        self.assertEqual({k for _, k, _ in a[1:]}, set(fmt_props.KINDS))

    def test_strip(self):
        text = "a  // fmtprop-1\n  // fmtprop-2\nb // keep\n"
        self.assertEqual(fmt_props.strip_markers(text), "a\nb // keep\n")
        self.assertEqual(fmt_props.strip_comments("a // x\n// y\n\nb\n"), "a\n\nb\n")
        self.assertEqual(fmt_props.comment_texts("/// d\n//! m\n//// p\na // c\n"), (["//// p", "// c"], ["/// d", "//! m"]))
        self.assertEqual(fmt_props.unperturb("f(a,\n   b)  // c\n\n.g()\nx =\n 1\n"), "f(a, b).g()\nx = 1\n")

    def test_item_heads(self):
        text = "@repr(c)\npub struct P {\n  x: I32,\n}\n@inline pub fn f() {\n  let x = 1\n}\nconst K: Bool =\n  true\n"
        self.assertEqual(fmt_props.item_heads(text), [("struct", "P"), ("fn", "f"), ("const", "K")])

    def test_comment_problems(self):
        before = "fn f() -> I32 { // a\n  // b\n  return 1_0 // c\n}\n"
        # fmt's rewrites (return, the spelling of a number, the alignment) move no comment
        self.assertEqual(fmt_props.comment_problems(before, "fn f() -> I32 { // a\n  // b\n  10 // c\n}\n"), [])
        moved = fmt_props.comment_problems(before, "fn f() -> I32 {\n  // a\n  // b\n  10\n} // c\n")
        self.assertEqual(len(moved), 2, moved)
        self.assertIn("`// a`: was at a line end, now on its own line", moved[0])
        self.assertIn("`// c`: should be at the end of line 4 `10`, is at the end of line 5 `}`", moved[1])
        # the same last tokens on another line: moved (the place counts, not the tokens)
        self.assertTrue(fmt_props.comment_problems("fn f() {\n  g(x) // c\n  h(y)\n}\n", "fn f() {\n  g(x)\n  h(y) // c\n}\n"))
        self.assertTrue(fmt_props.comment_problems("fn f() {\n  a\n  // c\n}\n", "fn f() {\n  // c\n  a\n}\n"))
        # a return in an arm (S-68) and a redundant parenthesis are rewrites: not moves
        arm = "fn f(x: I32) -> I32 {\n  match x {\n    1 => return 2, // c\n    _ => 3,\n  }\n}\n"
        self.assertEqual(fmt_props.comment_problems(arm, arm.replace("return ", "")), [])
        paren = "fn f() {\n  if (a) { // c\n    b\n  }\n}\n"
        self.assertEqual(fmt_props.comment_problems(paren, paren.replace("(a)", "a")), [])
        # an empty body that fmt joins keeps its comment at the end of the joined line
        joined = fmt_props.comment_problems("fn f() {\n  for i in r {\n  } // c\n}\n", "fn f() {\n  for i in r {} // c\n}\n")
        self.assertEqual(joined, [])

    def test_comment_problems_of_a_line_of_brackets_alone(self):
        def body(text):
            return "fn f() -> I32 {\n" + text + "}\n"

        # a line of a bracket, `return` or `move` alone has a counterpart (the pairing keeps them)
        kept = [
            ("  g(\n    a,\n  ) // c\n", None),
            ("  h(\n  ) // c\n", "  h() // c\n"),
            ("  g(\n    a,\n    // c\n  )\n", None),
            ("  let x = {\n    // c\n    return\n  }\n  x\n", None),
            ("  let t =\n    ( // c\n      a,\n    )\n", None),
        ]
        for before, after in kept:
            self.assertEqual(fmt_props.comment_problems(body(before), body(after or before)), [], before)
        attribute = "@fp(relaxed\n)  // c\nfn f() -> F32 {\n  1.0\n}\n"
        self.assertEqual(fmt_props.comment_problems(attribute, attribute.replace("relaxed\n)  ", "relaxed) ")), [])
        # a comment moved away from such a line is still caught
        moved = [
            ("  g(\n    a,\n  ) // c\n", "  g(\n    a, // c\n  )\n", "should be at the end of line 4 `)`"),
            ("  g(\n    a,\n    // c\n  )\n", "  g(\n    a, // c\n  )\n", "was on its own line, now at a line end"),
            ("  g(\n    a,\n    // c\n  )\n", "  g(\n    a,\n  )\n  // c\n", "should be before line 4 `)`"),
            ("  let x = {\n    // c\n    return\n  }\n  x\n", "  let x = {\n    return\n    // c\n  }\n  x\n",
             "should be before line 3 `return`"),
            ("  h( // c\n    a,\n  )\n", "  h(\n    a, // c\n  )\n", "should be at the end of line 2 `h (`"),
        ]
        for before, after, want in moved:
            problems = fmt_props.comment_problems(body(before), body(after))
            self.assertEqual(len(problems), 1, problems)
            self.assertIn(want, problems[0])

    def test_comment_problems_of_s528_and_s529(self):
        def body(text):
            return "fn f() -> I32 {\n" + text + "}\n"

        # S-528: a comment after a closing bracket that fmt moves to a line of its own goes with it, `)` as `]`
        # and `}`; S-529: the comment of a line of a `,` alone stays as a line of a comment in its place
        kept = [
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  ) // c\n  x\n"),
            ("  [\n    1,\n    2]  // c\n", "  [\n    1,\n    2,\n  ] // c\n"),
            ("  if c {\n    a\n    b }  // c\n  x\n", "  if c {\n    a\n    b\n  } // c\n  x\n"),
            ("  g(\n    1\n    , // c2\n    2\n  )\n", "  g(\n    1,\n    // c2\n    2,\n  )\n"),
            ("  g(\n    1 // c1\n    , // c2\n    2\n  )\n", "  g(\n    1, // c1\n    // c2\n    2,\n  )\n"),
            ("  g(\n    1 // c38\n    // c\n    , // c39\n    2\n  )\n",
             "  g(\n    1, // c38\n    // c\n    // c39\n    2,\n  )\n"),
            ("  [\n    1\n    , // c\n  ]\n", "  [\n    1,\n    // c\n  ]\n"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  let xs = [1, // c1\n            // c2\n            2]\n  1\n"),
        ]
        for before, after in kept:
            self.assertEqual(fmt_props.comment_problems(body(before), body(after)), [], before)
        # a comment moved away from those places is still caught
        moved = [
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  )\n  x // c\n", "should be at the end of line 5 `)`"),
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a,\n    b,\n  )\n  // c\n  x\n", "was at a line end"),
            ("  g(\n    a,\n    b)  // c\n  x\n", "  g(\n    a, // c\n    b,\n  )\n  x\n", "should be at the end of line 5 `)`"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  let xs = [1, // c1\n            2] // c2\n  1\n",
             "was on its own line, now at a line end"),
            ("  let xs = [1 // c1\n  , // c2\n  2]\n  1\n", "  // c2\n  let xs = [1, // c1\n            2]\n  1\n",
             "should be before line 4 `2 ]`"),
            ("  [\n    1\n    , // c\n  ]\n", "  [\n    1,\n  ]\n  // c\n", "should be before line 4 `]`"),
        ]
        for before, after, want in moved:
            problems = fmt_props.comment_problems(body(before), body(after))
            self.assertEqual(len(problems), 1, problems)
            self.assertIn(want, problems[0])

    def test_run(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let x = g(a, b) // c\n  x\n}\n")
        code, text = self.go(per_kind=3)
        self.assertEqual(code, 0, text)
        self.assertIn("no failure", text)
        code, text = self.go("cst")
        self.assertEqual(code, 0, text)
        for marker, failure in (
            ("let x = g(a, b) // DROP\n  drop(x)", "FAIL ast: tests/spec/a.onsa [source]"),  # not the same program
            # No normal form: fmt(p) is not fmt(x), and fmt(p) without the markers formatted again is not either.
            ("let KEEP_INDENT = g(a, b)", "FAIL convergence: tests/spec/a.onsa [space#0]: fmt(p) is not fmt(x)"),
            ("let KEEP_INDENT = g(a, b)",
             "FAIL convergence: tests/spec/a.onsa [mixed#0]: fmt(p) without the markers is not fmt(x)"),
            # A comment that fmt moves off the line of its element (R-70).
            ("let MOVE_COMMENT = g(a, b) // mv",
             "FAIL comments: tests/spec/a.onsa [source]: `// mv`: was at a line end, now on its own line"),
            # A rewrite of a perturbed input that is not that of the source: the depth and the meaning run on it.
            ('let LAYOUT = g("a.b", b)',
             "FAIL meaning: tests/spec/a.onsa [break#0]: onsa check before fmt: exit 0, no diagnostic; after fmt: "
             "exit 1, E0401"),
            ("let x = g(a, b) // REJECT", "FAIL rejected: tests/spec/a.onsa ["),  # a perturbed input refused
            ("let x = g(a, b) // NOT_IDEMPOTENT", "FAIL idempotence: tests/spec/a.onsa [source]"),
            ("let x = g(a, b) // lose LOSE_COMMENT", "FAIL comment-text: tests/spec/a.onsa [source]: comment: 1 lost"),
            ("/// d LOSE_DOC\n  let x = 1", "FAIL docs: tests/spec/a.onsa [source]: doc comment: 1 lost"),
            ("let DEEPER = g(a, b)", "FAIL depth: tests/spec/a.onsa [source]: item 1: 1 levels before fmt, 2 after"),
            # The depth and the meaning on an input with markers too (against the levels of the source).
            ("let DEEPER = g(a, b)", "FAIL depth: tests/spec/a.onsa [comment#0]: item 1: 1 levels before fmt, 2 after"),
            ("let VERDICT  = g(a, b)", "FAIL meaning: tests/spec/a.onsa [comment#0]: onsa check before fmt: exit 1"),
            # A rewrite that changes what `onsa check` says (spec §18.2, W3-12/b2 3).
            ("let VERDICT  = g(a, b)",
             "FAIL meaning: tests/spec/a.onsa [source]: onsa check before fmt: exit 1, E0401; after fmt: exit 0, "
             "no diagnostic"),
            # A verdict of 1 with no diagnostic the item reads (another form of the output) fails, not passes.
            ("let SILENT = g(a, b)",
             "FAIL meaning: tests/spec/a.onsa [source]: onsa check ended with 1 and printed no diagnostic"),
            # A line break between two statements, and a blank line between two elements, that fmt lost.
            ("let JOIN_KEPT = 1",
             "FAIL breaks: tests/spec/a.onsa [source]: line 3, before `x` (line): the line break of the writer is gone"),
            ("let y = g(a,\n\n    b)",
             "FAIL breaks: tests/spec/a.onsa [source]: line 4, before `b` (element): the blank line between the elements "
             "is gone"),
        ):
            with self.subTest(marker=marker):
                self.repo.write("tests/spec/a.onsa", f"fn f() {{\n  {marker}\n  x\n}}\n")
                code, text = self.go()
                self.assertEqual(code, 1, text)
                self.assertIn(failure, text)
        self.assertFalse((self.repo.root / "tests" / "spec" / "a.onsa").read_text().count("fmtprop"))

    def test_no_file_is_formatted_in_place(self):
        # X-1 U12: fmt(p) is the standard output of `onsa_cases --fmt`; the compiler is asked `fmt --check` alone
        # (`onsa fmt FILE` would sync the file to the disk), and the item writes the file of fmt(p) itself.
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let x = g( a, b ) // c\n  x\n}\n")
        calls, call = [], fmt_props.Onsa.call

        def spy(argv):
            calls.append(argv)
            return call(argv)

        with mock.patch.object(fmt_props.Onsa, "call", staticmethod(spy)):
            code, text = self.go()
        self.assertEqual(code, 0, text)
        self.assertTrue([a for a in calls if a[-2] == "--fmt"], calls)
        self.assertEqual([a for a in calls if "fmt" in a and "--check" not in a], [])

    def test_the_meaning_compares_the_exit_code_and_the_codes_alone(self):
        # fmt moves the line of the diagnostic (it drops the blank lines): its place and its text change,
        # its code does not, so the meaning holds. The fake `check` of a file fmt does not change is not asked.
        self.repo.write("tests/spec/a.onsa", "fn f() {\n\n\n  let PLACE = 1\n  x\n}\n")
        code, text = self.go()
        self.assertNotIn("FAIL meaning", text)
        self.assertIn("inputs from 1 sources", text)

    def test_the_depth_and_the_meaning_run_on_the_source_and_the_inputs_with_markers(self):
        # A perturbation changes no program, so the rewrites of fmt are those of the source; a comment may
        # stop one (`spec/tools.md` §3.4). The other inputs ask neither `dump --levels` nor `check`.
        source = "fn f() {\n  let x = g(a, b) // c\n  x\n}\n"
        self.repo.write("tests/spec/a.onsa", source)
        inputs = fmt_props.inputs_of("tests/spec/a.onsa", source, 2, "t")
        want = {str(k) for k, (_, kind, _) in enumerate(inputs) if kind in (None, "comment", "mixed")}
        self.assertTrue({"space", "blank", "break", "comment", "mixed"} <= {kind for _, kind, _ in inputs}, inputs)
        asked, run = {"check": set(), "dump": set()}, fmt_props.Onsa.run

        def spy(onsa, *args):
            if args[0] in asked:
                asked[args[0]].add(Path(args[-1]).parent.parent.name)  # <work>/<input>/{a,b}/<name>
            return run(onsa, *args)

        with mock.patch.object(fmt_props.Onsa, "run", spy):
            code, text = self.go(per_kind=2)
        self.assertEqual(code, 0, text)
        self.assertEqual(asked, {"check": want, "dump": want})

    def test_a_narrowed_run(self):
        # X-1: the cases of fmt always, a sample of one source per group (the first 3 parts of the
        # directory), each source's inputs as in the whole run (they depend on that source alone)
        paths = ["tests/spec/fmt/f.onsa"] + [f"tests/spec/q/{i}.onsa" for i in range(4)] + ["tests/spec/r/r.onsa"]
        for p in paths:
            self.repo.write(p, self.SOURCE)
        listed = [{"path": p, "kind": "file", "mode": "check", "files": [{"path": p, "syntax_errors": False}]}
                  for p in paths]
        whole = sum(len(fmt_props.inputs_of(p, self.SOURCE, 1, "t")) for p in paths)
        self.assertEqual(fmt_props.inputs_of(paths[1], self.SOURCE, 1, "t"),
                         fmt_props.inputs_of(paths[1], self.SOURCE, 1, "t"))
        for selection, picked, want in ((narrowing.Selection(sample=1e-9, salt="s"), 3,
                                         "picked 3 of 6 sources (always 1, sample 2)"),
                                        (narrowing.Selection(shard=(0, 1)), 6, "picked 6 of 6 sources (shard 0/1)"),
                                        (None, 6, "skipped); ")):
            with self.subTest(selection=selection):
                lines = []
                code = fmt_props.run(self.repo.root, self.argv, "cst", 1, "t", 2, self.cases_cmd(listed), self.argv,
                                     out=lines.append, selection=selection)
                text = "\n".join(lines)
                self.assertEqual(code, 0, text)
                self.assertIn(f"{whole * picked // 6} inputs from {picked} sources", text)
                self.assertIn(want, text)

    def test_the_continuing_symbols_are_read_once_and_checked(self):
        # Read on the main thread from the injected command, before any
        # perturbation; none or an empty list is a usage error (exit 2).
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  x\n}\n")
        listed = [{"path": "tests/spec/a.onsa", "kind": "file", "mode": "check",
                   "files": [{"path": "tests/spec/a.onsa", "syntax_errors": False}]}]
        for answer in ("[]", "1"):
            with self.subTest(answer=answer):
                cmd = (sys.executable, "-B", "-c",
                       f"import json, sys; print({answer!r} if '--continuing' in sys.argv else json.dumps({listed!r}))")
                lines = []
                code = fmt_props.run(self.repo.root, self.argv, "core", 1, "t", 2, cmd, self.argv, out=lines.append)
                self.assertEqual(code, 2, lines)
                self.assertIn("cannot read the symbols of the lexer", "\n".join(lines))
        fmt_props.load_symbols(self.repo.root, self.cases_cmd([]))
        self.assertEqual(fmt_props.continuing(), frozenset(self.CONTINUING))
        self.assertEqual(set(fmt_props.long_symbols()), set(self.SYMBOLS))

    def test_internal_and_cst_failures(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  PANIC\n}\n")
        code, text = self.go()
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL internal: tests/spec/a.onsa [source]: fmt: internal|crates/onsa_syntax/src/fmt.rs|boom", text)
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  CST_BAD\n}\n")
        code, text = self.go("cst")
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL cst: tests/spec/a.onsa [source]: the output is not the source", text)

    def test_minimize(self):
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let a = 1\n  PANIC\n  let b = 2\n}\n")
        code, text = self.go(per_kind=0, minimize=True)
        self.assertEqual(code, 1, text)
        saved = next((self.repo.root / "target" / "fmt_props" / "fail" / "core").glob("*.onsa"))
        self.assertEqual(saved.read_text(), "PANIC")
        # a refused input shrinks while the input without the perturbation is still read
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  let a = 1\n  REJECT\n  let b = 2\n}\n")
        code, text = self.go(per_kind=1, minimize=True)
        self.assertEqual(code, 1, text)
        small = [p.read_text() for p in (self.repo.root / "target" / "fmt_props" / "fail" / "core").glob("*.onsa")]
        self.assertTrue(small and all("REJECT" in s and len(s) < 20 for s in small), small)

    def test_which_sources_may_be_unread(self):
        refused = "fn f() {\n  REJECT x \n}\n"
        self.repo.write("tests/spec/a.onsa", "fn f() {\n  x\n}\n")
        self.repo.write("tests/spec/b.onsa", refused)
        # a file with a syntax diagnostic, a fragment of mode none, a pending case: skipped
        for mode, syntax, listed in (("check", True, False), ("none", False, False), ("check", False, True)):
            with self.subTest(mode=mode, syntax=syntax, listed=listed):
                self.repo.write("tests/pending.toml", entry("test-case", "tests/spec/b.onsa") if listed else "")
                code, text = self.go(cases=[("tests/spec/a.onsa", "check", False), ("tests/spec/b.onsa", mode, syntax)])
                self.assertEqual(code, 0, text)
                self.assertIn("1 that fmt may not read, skipped", text)
        # any other refusal fails
        self.repo.write("tests/pending.toml", entry("test-case", "tests/spec/b.onsa::t"))
        code, text = self.go(cases=[("tests/spec/a.onsa", "check", False), ("tests/spec/b.onsa", "check", False)])
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL unread: tests/spec/b.onsa [source]", text)
        # nothing ran: a failure
        self.repo.write("tests/pending.toml", "")
        code, text = self.go(cases=[("tests/spec/b.onsa", "none", False)])
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL no source ran", text)

    def test_std_and_examples_are_sources(self):
        self.repo.write("std/core/m.onsa", "fn f() {}\n")
        self.repo.write("examples/e/x.onsa", "fn g() {}\n")
        self.repo.write("examples/e/onsa.toml", "")
        self.repo.write("examples/e/target/out.onsa", "built")
        cmd = (sys.executable, "-B", "-c", "print('[]')")
        paths = [s.path for s in fmt_props.sources(self.repo.root, cmd)]
        self.assertEqual(paths, ["std/core/m.onsa", "examples/e/x.onsa"])

    def test_the_places_of_the_line_breaks(self):
        # Read on the text: the brackets, the elements, the attributes, the comments (`docs/onsa-tools.md` §3.2).
        text = ("@repr(c)\nstruct P { x: F32 }\nfn f() {\n  two(a, // c\n    b +\n    g(x\n    as F64))\n"
                "  match a {\n    0 =>\n      1,\n  }\n}\n")
        places = [(key, place, nl) for key, place, nl, _, _, _ in fmt_props.break_places(text)]
        self.assertEqual(places, [
            ("repr", "line", False), ("(", "line", False), ("c", "open", False), (")", None, False),
            ("struct", None, True), ("P", "line", False), ("{", "line", False), ("x", "open", False),
            (":", "removable", False), ("F32", "removable", False), ("}", None, False),
            ("fn", "line", True), ("f", "line", False), ("(", "line", False), (")", None, False), ("{", "line", False),
            ("two", None, True), ("(", "line", False), ("a", "open", False), ("b", "element", True),
            ("+", "removable", False), ("g", "continue", True), ("(", "removable", False), ("x", "open", False),
            ("as", "removable", True), ("F64", "removable", False), (")", None, False), (")", None, False),
            ("match", "line", True), ("a", "line", False), ("{", "line", False), ("#", "open", True),
            ("=>", "removable", False), ("#", "removable", True), ("}", None, True), ("}", None, True),
        ])

    def test_break_problems(self):
        body = lambda *lines: "fn f() {\n" + "".join(f"  {line}\n" for line in lines) + "}\n"
        for before, after, want in (
            # Kept: between statements, between elements (and the blank line there), after the opening bracket,
            # at a continuation; added there: a failure too.
            (body("let a = 1", "a"), body("let a = 1 a"), ["line 3, before `a` (line): the line break of the "
                                                           "writer is gone"]),
            (body("two(a,", "    b)"), body("two(a, b)"), ["line 3, before `b` (element): the line break of the "
                                                         "writer is gone"]),
            (body("two(a, b)"), body("two(a,", "    b)"), ["line 2, before `b` (element): the line break of the "
                                                          "writer is added"]),
            (body("two(a,", "", "    b)"), body("two(a,", "    b)"), ["line 4, before `b` (element): the blank line "
                                                                     "between the elements is gone"]),
            (body("two(", "    a, b,", "  )"), body("two(a, b)"), ["line 3, before `a` (open): the line break of the "
                                                                   "writer is gone"]),
            (body("two(a +", "    b, c)"), body("two(a + b, c)"), ["line 3, before `b` (continue): the line break of "
                                                                   "the writer is gone"]),
            # Removed: inside an element (S-497, S-505); one that stays is a failure.
            (body("g(x", "    as F64)"), body("g(x as F64)"), []),
            (body("g(x", "    as F64)"), body("g(x", "    as F64)"), ["line 3, before `as` (removable): the line "
                                                                       "break inside an element stays"]),
            (body("let s = S { f", "    : a }"), body("let s = S { f: a }"), []),
            # Not counted: what fmt adds or removes by the form, round attributes and the rewrites of §3.3.
            ("@repr(c) struct P { x: F32 }\n", "@repr(c)\nstruct P { x: F32 }\n", []),
            ("flow g() {\n  @mem(bulk)\n  let d = 1\n}\n", "flow g() {\n  @mem(bulk) let d = 1\n}\n", []),
            ("fn h() { g(a, b\n) }\n", "fn h() {\n  g(a, b)\n}\n", []),
            (body("two(a", "    , b)"), body("two(a,", "    b)"), []),
            (body("two(a // c", "    , b)"), body("two(a, // c", "    b)"), []),
            ("fn f() -> I32 {\n  return 1\n}\n", "fn f() -> I32 {\n  1\n}\n", []),
            # Another token changed: said, and the gaps round it are not judged.
            (body("g(x", "    as F64)"), body("g(y", "    as F64)"), ["token (but `,` and `return`) #7: 'x' became 'y'"]),
        ):
            with self.subTest(before=before, after=after):
                self.assertEqual(fmt_props.break_problems(before, after), want)


if __name__ == "__main__":
    unittest.main(verbosity=1)
