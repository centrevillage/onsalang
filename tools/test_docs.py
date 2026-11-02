#!/usr/bin/env python3
"""Self-tests of tools/docs.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_docs.py
"""
import datetime
import io
import os
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / "hooks"))
import check_spec_examples as cse  # noqa: E402
import claude_hook  # noqa: E402
import default_inits  # noqa: E402
import docs as docs_tool  # noqa: E402
import gap_marks  # noqa: E402
import gate_steps  # noqa: E402
import keywords  # noqa: E402
import pending  # noqa: E402
import repo  # noqa: E402
import spec_blocks  # noqa: E402
import spec_sections  # noqa: E402
from selftest_support import entry, quiet, quiet_out, git_in, NEW_LAYOUT, split_spec  # noqa: E402


# A sentence of 100 characters, and others: a line of three is longer than docs.LONG.
S = "あ" * 99 + "。"
T = "い" * 99 + "。"
LONG_SENTENCE = "う" * 299 + "。"


class DocsTool(unittest.TestCase):
    """tools/docs.py (X-2 U1): `fmt`, `swaps`, `check`, and the documents they read."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def main(self, *argv):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main([*argv, "--root", str(self.root)])
        return code, out.getvalue()

    def fmt(self, text):
        new, wrapped, left = docs_tool.fmt_text(text)
        # idempotent: a second run changes nothing; the round trip gives the text back
        self.assertEqual(docs_tool.fmt_text(new)[:2], (new, []))
        return new.split("\n"), wrapped, left

    # ------------------------------------------------ fmt

    def test_fmt_breaks_after_a_sentence_and_packs_to_the_width(self):
        lines, wrapped, left = self.fmt("intro\n- " + S + S + T + "\nend")
        self.assertEqual(lines, ["intro", "- " + S + S, "  " + T, "end"])
        self.assertEqual((wrapped, left), ([2], []))

    def test_fmt_goes_on_at_the_indentation_of_the_item(self):
        cases = {
            "> " + S * 3: "> ",  # a quote
            "1. " + S * 3: "   ",  # a numbered item
            "  - " + S * 3: "    ",  # a nested item
            "    " + S * 3: "    ",  # a line that goes on an item
            S * 3: "",  # a paragraph
        }
        for line, cont in cases.items():
            lines, wrapped, _ = self.fmt(line)
            self.assertEqual(lines, [line[: len(line) - 100], cont + S], line[:4])
            self.assertEqual(wrapped, [1])

    def test_fmt_leaves_the_blocks_and_the_kept_lines(self):
        long = S * 3
        text = "\n".join([
            "+++", f'title = "{long}"', "+++",
            "```", long, "```", "  ~~~~ x", long, "  ~~~", long, "~~~~",
            f"| {long} |", f"# {long}", f"欠番: {long}", f"<!-- {long} -->", "<!--", long, "-->",
        ])  # fmt: skip
        new, wrapped, left = docs_tool.fmt_text(text)
        self.assertEqual((new, wrapped, left), (text, [], []))
        # a head field that does not close keeps the whole file (the check of the head fields reports it)
        self.assertEqual(docs_tool.fmt_text("+++\n" + long)[0], "+++\n" + long)

    def test_fmt_breaks_only_at_the_depth_0_outside_code_and_bold(self):
        for inner in ("（" + S * 2 + "）", "`" + S * 2 + "`", "`` a`b " + S * 2 + " ``", "**" + S * 2 + "**", "「" + S * 2 + "」"):
            lines, wrapped, left = self.fmt(inner + S)
            self.assertEqual((wrapped, left), ([], [(1, len(inner) + 100)]), inner[:4])
        # an escaped backtick opens no code span (the backtick after it has no partner); a closed bracket
        # comes back to the depth 0
        middle = "（あ。）" + "え" * 50 + "。"
        tail = "お`" + "お" * 97 + "。"
        lines, wrapped, _ = self.fmt("\\`" + S + middle + tail)
        self.assertEqual(lines, ["\\`" + S + middle, tail])

    def test_fmt_never_starts_a_line_like_a_block(self):
        for start in ("- x", "* x", "+ x", "> x", "| x", "# x", "```x", "~~~x", "<b>", "=== x", "___", "12. x", "3) x", " x"):
            piece = start + "え" * (99 - len(start)) + "。"
            lines, wrapped, left = self.fmt(S * 2 + piece + T)
            self.assertEqual(lines, [S, S + piece, T], start)
            for line in lines[1:]:
                self.assertIsNone(docs_tool.NO_START.match(line), line[:6])

    def test_fmt_reports_the_lines_with_no_place_to_break(self):
        lines, wrapped, left = self.fmt("x\n- " + LONG_SENTENCE)
        self.assertEqual((wrapped, left), ([], [(2, 302)]))
        lines, wrapped, left = self.fmt(S + LONG_SENTENCE)  # broken, but a piece is still long
        self.assertEqual((lines, wrapped, left), ([S, LONG_SENTENCE], [1], [(1, 300)]))

    def test_fmt_writes_checks_and_lists(self):
        doc = self.write("rules/a.md", "# a\n\n- " + S * 3 + "\n")
        self.write("rules/b.md", "short\n")
        code, out = self.main("fmt", "--check")
        self.assertEqual(code, 1)
        self.assertIn("rules/a.md: 1 line(s) would be wrapped (lines 3)", out)
        self.assertEqual(self.main("fmt", "--list")[0], 0)
        self.assertEqual(doc.read_text(encoding="utf-8"), "# a\n\n- " + S * 3 + "\n")
        code, out = self.main("fmt")
        self.assertEqual(code, 0, out)
        self.assertEqual(doc.read_text(encoding="utf-8"), "# a\n\n- " + S * 2 + "\n  " + S + "\n")
        self.assertEqual(self.main("fmt", "--check"), (0, "docs fmt: 0 line(s) in 0 file(s) would be wrapped; "
                                                          "0 long line(s) have no place to break\n"))  # fmt: skip
        # a long line with no place to break is shown, and is not a change
        self.write("rules/c.md", LONG_SENTENCE)
        code, out = self.main("fmt", "--check")
        self.assertEqual(code, 0)
        self.assertIn("rules/c.md:1: 300 characters left on one line (no place to break)", out)

    def test_fmt_leaves_out_the_spec_unless_asked(self):
        for rel in ("rules/a.md", "spec/03-ops.md", "spec/tools.md", "spec/02-lexical.md", "README.md"):
            self.write(rel, S * 3)
        out = self.main("fmt", "--check")[1]
        self.assertEqual(sorted(re.findall(r"^(\S+): 1 line", out, re.M)), ["README.md", "rules/a.md"])
        out = self.main("fmt", "--check", "--spec")[1]
        self.assertEqual(len(re.findall(r"^\S+: 1 line", out, re.M)), 5)
        code, out = self.main("fmt", str(self.root / "spec/03-ops.md"))
        self.assertEqual(code, 0)
        self.assertIn("spec/03-ops.md: skipped, the spec (pass --spec)", out)
        self.assertEqual((self.root / "spec/03-ops.md").read_text(encoding="utf-8"), S * 3)
        # a path given: only that document
        self.assertEqual(self.main("fmt", str(self.root / "README.md"))[0], 0)
        self.assertEqual((self.root / "README.md").read_text(encoding="utf-8"), S * 2 + "\n" + S)
        self.assertEqual((self.root / "rules/a.md").read_text(encoding="utf-8"), S * 3)

    def test_fmt_writes_nothing_when_the_round_trip_breaks(self):
        a = self.write("rules/a.md", S * 3)
        b = self.write("rules/b.md", T * 3)
        real = docs_tool.wrap

        def broken(line):  # breaks the round trip of the second file only
            return ([line[:5], line[6:]], "") if line.startswith("い") else real(line)

        with mock.patch.object(docs_tool, "wrap", side_effect=broken):
            code, out = self.main("fmt")
        self.assertEqual(code, 2)
        self.assertIn("does not give the line back; nothing is written", out)
        self.assertEqual((a.read_text(encoding="utf-8"), b.read_text(encoding="utf-8")), (S * 3, T * 3))

    def test_fmt_does_not_write_a_file_open_in_vim(self):
        a = self.write("rules/a.md", S * 3)
        b = self.write("rules/b.md", T * 3)
        self.write("rules/.a.md.swo", "")
        code, out = self.main("fmt")
        self.assertEqual(code, 1)
        self.assertIn("rules/a.md: skipped, the swap file .a.md.swo", out)
        self.assertEqual(a.read_text(encoding="utf-8"), S * 3)
        self.assertEqual(b.read_text(encoding="utf-8"), T * 2 + "\n" + T)

    def test_fmt_keeps_the_bytes_and_skips_cr(self):
        a = self.write("rules/a.md", "x")
        a.write_bytes((S * 3 + "\r\n").encode("utf-8"))
        code, out = self.main("fmt")
        self.assertEqual(code, 0)
        self.assertIn("rules/a.md: skipped, it has CR line ends", out)
        self.assertEqual(a.read_bytes(), (S * 3 + "\r\n").encode("utf-8"))
        self.write("rules/b.md", "x").write_bytes(b"\xff")
        self.assertEqual(self.main("fmt")[0], 2)

    # ------------------------------------------------ swaps

    def test_swaps(self):
        for rel in ("docs/.a.md.swp", ".x.swo", "rules/.r.md.swn", "target/.t.swp", ".git/.g.swp",
                    ".claude/worktrees/w/.w.md.swp", "crates/c/target/.c.swp", "docs/a.swp", "docs/.a.md.swpx"):
            self.write(rel, "")
        self.write("crates/c/Cargo.toml", "")
        code, out = self.main("swaps")
        self.assertEqual(code, 1)
        self.assertEqual(out, ".x.swo\ndocs/.a.md.swp\nrules/.r.md.swn\ndocs swaps: 3 swap file(s)\n")
        self.assertEqual(docs_tool.swap_files_of(self.root / "docs/a.md"), [self.root / "docs/.a.md.swp"])
        for rel in (".x.swo", "docs/.a.md.swp", "rules/.r.md.swn"):
            (self.root / rel).unlink()
        self.assertEqual(self.main("swaps"), (0, "docs swaps: 0 swap file(s)\n"))

    # ------------------------------------------------ check and the documents

    def test_check_counts_the_cells_of_the_tables(self):
        self.write("rules/a.md", "\n".join([
            "| a | b |", "|---|:-:|", "| 1 | 2 |", "| 1 | 2 | 3 |", "| 1 |", "| `x|y` | a \\| b |", "| ``a`|`b`` | c",
            "", "| a | b |", "|---|---|---|", "| 1 | 2 |",
            "", "```", "| a | b |", "|---|---|", "| 1 |", "```",
            "<!--", "| a | b |", "|---|---|", "| 1 |", "-->",
            "- item", "  | x | y |", "  |---|---|", "  | 1 |",
            "", "| t | u |", "", "| 1 | 2 |",
        ]))  # fmt: skip
        code, out = self.main("check")
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), [
            "== tables",
            "rules/a.md:4: the row has 3 cells, the header 2",
            "rules/a.md:5: the row has 1 cells, the header 2",
            "rules/a.md:10: the delimiter row has 3 cells, the header 2",
            "rules/a.md:26: the row has 1 cells, the header 2",
            "rules/a.md:28: table rows with no header and delimiter row before them",
            "rules/a.md:30: table rows with no header and delimiter row before them",
            "heads, refs, relations: no directory of the new layout",
            "docs check: 6 problem(s) (tables 6, heads 0, refs 0, relations 0, links 0, tools 0)",
        ])  # fmt: skip

    def test_check_passes_and_fails_on_an_open_fence(self):
        self.write("rules/a.md", "| a | b |\n|---|---|\n| 1 | 2 |\n")
        none = "heads, refs, relations: no directory of the new layout\n"
        self.assertEqual(self.main("check"), (0, none + "docs check: no problem in 1 document(s) "
                                                        "(tables, heads, refs, relations, links, tools)\n"))  # fmt: skip
        self.write("rules/b.md", "x\n````\n| a |\n```\n")
        self.assertEqual(self.main("check"), (1, "== tables\nrules/b.md:2: the code fence is not closed\n" + none +
                                                 "docs check: 1 problem(s) (tables 1, heads 0, refs 0, relations 0, "
                                                 "links 0, tools 0)\n"))  # fmt: skip

    def test_check_with_no_document_is_an_error(self):
        self.write("history/a.md", "| a |\n| 1 | 2 |\n")
        code, out = self.main("check")
        self.assertEqual(code, 2)
        self.assertIn("no document found", out)
        self.assertEqual(self.main("fmt", "--check")[0], 2)

    def test_the_documents_by_the_layout(self):
        # X-2 DT-7: the files under the directories of DOC_DIRS and the root's README and CLAUDE; `docs/`, the
        # older specs at the root, `history/` and the files that are not Markdown are never read
        read = ["CLAUDE.md", "README.md", "decisions/S/S-1.md", "design/03-types.md", "issues/R/R-1.md", "rules/common.md",
                "spec/02-lexical.md", "spec/README.md", "spec/tools.md", "tasks/W/W1-01.md"]  # fmt: skip
        unread = ["docs/a.md", "docs/onsa-tools.md", "onsa-lang-spec-0.3.md", "onsa-lang-spec-0.2.md", "kumi-lang-spec.md",
                  "docs/sub/x.md", "docs/f.toml", "history/h.md", "rules/f.toml"]  # fmt: skip
        for rel in read + unread:
            self.write(rel, "| a |\n|---|\n| 1 | 2 |\n")
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root)], read)
        self.assertEqual([p.as_posix() for p in repo.doc_files(self.root, spec=False)],
                         [r for r in read if not r.startswith("spec/")])  # fmt: skip
        out = self.main("check")[1]
        self.assertEqual(re.findall(r"^(\S+):3:", out, re.M), read)


class DocsDue(unittest.TestCase):
    """`docs.py due` (X-9 U1, the gate's `docs-due`) in a made-up git repository."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        git_in(self.root, "init", "-q")
        for rel in ("rules/a.md", "crates/x.rs", "issues/X/X-1.md", "decisions/S/README.md", "history/h.md"):
            self.write(rel, "a\n")
        self.commit("base")

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def commit(self, message):
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-q", "--allow-empty", "-m", message)
        return git_in(self.root, "rev-parse", "--short=7", "HEAD").strip()

    def mark(self, *values):
        """A commit taking in checks of `values` (default: `P..P (X-3, onsa-docs)` of its parent P, the check of
        the uncommitted changes) as `Docs-Checked:` trailers."""
        parent = git_in(self.root, "rev-parse", "--short=7", "HEAD").strip()
        values = values or (f"{parent}..{parent} (X-3, onsa-docs)",)
        return self.commit("take in the docs check\n\n" + "\n".join(f"Docs-Checked: {v}" for v in values))

    def due(self, *argv):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main(["due", *argv, "--root", str(self.root)])
        return code, out.getvalue().splitlines()

    def test_the_documents_watched(self):
        self.assertEqual(docs_tool.DUE_DOCS, (
            "rules/", "spec/", ".claude/agents/", "README.md", "CLAUDE.md",
            ":(glob)decisions/README.md", ":(glob)decisions/*/README.md", ":(glob)issues/README.md",
            ":(glob)issues/*/README.md", ":(glob)tasks/README.md", ":(glob)tasks/*/README.md",
            ":(glob)design/README.md", ":(glob)design/*/README.md"))  # fmt: skip
        m = self.mark()
        watched = ("rules/b/c.md", "spec/foreign-forms.toml", ".claude/agents/onsa-x.md", "README.md", "CLAUDE.md",
                   "decisions/README.md", "issues/R/README.md", "tasks/W/README.md", "design/README.md")  # fmt: skip
        for rel in watched + ("decisions/S/S-1.md", "decisions/S/x/README.md", "history/README.md", "x/README.md",
                              "tools/README.md", "spec.md"):  # fmt: skip
            self.write(rel, "b\n")
        self.commit("change")
        code, out = self.due()
        self.assertEqual(code, gate_steps.PARENT, out)
        self.assertEqual(out[1:-1], [f"parent: {p}: changed after the docs check {m}" for p in sorted(watched)])

    def test_no_mark(self):
        # a `Docs-Checked:` in the subject or a body line that is not a trailer is no mark
        self.write("rules/a.md", "b\n")
        self.commit("Docs-Checked: a..b (X-3, onsa-docs)\n\nDocs-Checked: inside\nthe body")
        code, out = self.due()
        self.assertEqual((code, out[0]), (gate_steps.PARENT, "parent: no commit from HEAD has a `Docs-Checked:` trailer"))
        code, out = self.due("--stage-end", "W4")
        self.assertEqual((code, out[0]), (1, "no commit from HEAD has a `Docs-Checked:` trailer"))
        self.assertIn("(fails at the stage end W4)", out[-1])

    def test_after_the_mark(self):
        self.write("rules/a.md", "b\n")  # changed in the commit of the mark: checked
        self.commit("rules before the check")  # in the range P..P that ends at the parent of the mark: checked
        self.write("rules/a.md", "b2\n")
        parent = git_in(self.root, "rev-parse", "--short=7", "HEAD").strip()
        m = self.mark()
        head = f"docs due: the last docs check is {m} (Docs-Checked: {parent}..{parent} (X-3, onsa-docs))"
        self.assertEqual(self.due(), (0, [head, "docs due: no document changed after the docs check"]))
        # only the code, the history and a file of an ID change: nothing is due
        for rel in ("crates/x.rs", "history/h.md", "issues/X/X-1.md", "crates/new.rs"):
            self.write(rel, "c\n")
        self.commit("code")
        self.write("crates/x.rs", "d\n")
        self.assertEqual(self.due()[0], 0)
        self.assertEqual(self.due("--stage-end", "W4")[0], 0)
        # a rule changed in a commit, a field table not committed, a rule untracked, a rule removed
        self.write("rules/a.md", "c\n")
        self.commit("rules")
        self.write("decisions/S/README.md", "c\n")
        self.write("rules/new.md", "c\n")
        self.write("rules/.a.md.swo", "c\n")  # a vim swap file: not a document
        code, out = self.due()
        self.assertEqual(code, gate_steps.PARENT, out)
        self.assertEqual(out, [head, f"parent: decisions/S/README.md: changed after the docs check {m}",
                               f"parent: rules/a.md: changed after the docs check {m}",
                               f"parent: rules/new.md: untracked after the docs check {m}",
                               "docs due: run the check of onsa-docs and take it in with `work.py commit --docs-checked "
                               "<range> <work>`"])  # fmt: skip
        code, out = self.due("--stage-end", "W4")
        self.assertEqual(code, 1)
        self.assertEqual(out[1], f"decisions/S/README.md: changed after the docs check {m}")
        self.assertFalse(any(x.startswith("parent:") for x in out))
        # a newer mark: the changes before it are checked; a removed rule after it is due
        m2 = self.mark()
        self.assertEqual(self.due()[0], 0)
        (self.root / "rules/a.md").unlink()
        self.assertEqual(self.due()[1][1:-1], [f"parent: rules/a.md: changed after the docs check {m2}"])

    def test_out_of_the_range(self):
        # X-12: a check of A..B taken in by T; the documents changed between B and T are due, T's own are not
        a = git_in(self.root, "rev-parse", "--short=7", "HEAD").strip()
        self.write("rules/a.md", "in the range\n")
        b = self.commit("checked")
        self.write("rules/b.md", "out\n")
        self.write("spec/s.md", "out\n")
        c1 = self.commit("out of the range")
        self.write("crates/x.rs", "code\n")
        self.commit("code only")
        self.write("rules/b.md", "out again\n")
        c2 = self.commit("out of the range again")
        self.write("rules/c.md", "the fix of the check\n")
        t = self.mark(f"{a}..{b} (X-3, onsa-docs)")
        out_of = f"after the docs check of ..{b} (out of its range, before {t})"
        tail = "docs due: run the check of onsa-docs and take it in with `work.py commit --docs-checked <range> <work>`"
        code, out = self.due()
        self.assertEqual((code, out), (gate_steps.PARENT, [
            f"docs due: the last docs check is {t} (Docs-Checked: {a}..{b} (X-3, onsa-docs))",
            f"parent: rules/b.md: changed in {c1} {c2} {out_of}", f"parent: spec/s.md: changed in {c1} {out_of}", tail]))
        # the hook of the session start counts them as documents of `docs.py due`
        self.assertTrue(all(claude_hook.DUE_DOC.match(x) for x in out[1:-1]))
        # --stage-end: the exit code and the last line as before
        code, out = self.due("--stage-end", "W4")
        self.assertEqual((code, out[1], out[-1]), (1, f"rules/b.md: changed in {c1} {c2} {out_of}",
                                                   tail + " (fails at the stage end W4)"))  # fmt: skip
        # a change after T of a path out of the range shows as after T; a new path after T joins
        self.write("rules/b.md", "after\n")
        self.write("rules/d.md", "new\n")
        self.assertEqual(self.due()[1][1:-1], [f"parent: rules/b.md: changed after the docs check {t}",
                                               f"parent: rules/d.md: untracked after the docs check {t}",
                                               f"parent: spec/s.md: changed in {c1} {out_of}"])  # fmt: skip

    def test_several_values(self):
        # two trailers in one commit: a commit that an end of either reaches is checked
        a = git_in(self.root, "rev-parse", "--short=7", "HEAD").strip()
        self.write("rules/a.md", "1\n")
        b1 = self.commit("first half")
        self.write("rules/b.md", "2\n")
        b2 = self.commit("second half")
        self.write("rules/c.md", "3\n")
        c = self.commit("out of both")
        t = self.mark(f"{a}..{b1} (X-3, onsa-docs)", f"{b1}..{b2} (X-3, onsa-docs)")
        value = f"{a}..{b1} (X-3, onsa-docs); {b1}..{b2} (X-3, onsa-docs)"
        self.assertEqual(self.due()[1], [
            f"docs due: the last docs check is {t} (Docs-Checked: {value})",
            f"parent: rules/c.md: changed in {c} after the docs check of ..{b1} ..{b2} (out of its range, before {t})",
            "docs due: run the check of onsa-docs and take it in with `work.py commit --docs-checked <range> <work>`"])
        self.assertEqual(docs_tool.last_docs_check(self.root)[1], value)  # what work.py commit compares

    def test_values_not_read(self):
        # a value not read is not counted as a check: a line says so, the readable values of the commit count
        self.write("rules/a.md", "1\n")
        first = self.mark()
        self.write("crates/x.rs", "2\n")
        p = self.commit("code")
        git_in(self.root, "checkout", "-q", "-b", "side")
        self.write("rules/a.md", "side\n")
        side = self.commit("a commit out of the history of HEAD")
        git_in(self.root, "checkout", "-q", "-")
        bad = ["a..b (X-3, onsa-docs)", f"{p} (X-3, onsa-docs)", f"{first}...{p} (X-3, onsa-docs)", f"..{p}",
               f"{first}..{side} (X-3, onsa-docs)", f"{p}..HEAD (X-3, onsa-docs)", f"-q..{p}", f"{p}:x.md..{p}"]
        note = "docs due: {} has `Docs-Checked: {}`, not <A>..<B> of two commits with B its parent or an ancestor of it; " \
               "not counted as a check"  # fmt: skip
        self.write("rules/b.md", "the fix of the check\n")
        t = self.mark(*bad, f"{p}..{p} (X-3, onsa-docs)")
        code, out = self.due()
        self.assertEqual(out[:len(bad)], [note.format(t, v) for v in bad])
        self.assertEqual((code, out[len(bad):]), (0, [
            f"docs due: the last docs check is {t} (Docs-Checked: {'; '.join(bad)}; {p}..{p} (X-3, onsa-docs))",
            "docs due: no document changed after the docs check"]))  # fmt: skip
        # no value read: the commit is passed over for the check before it, and its own changes are due
        self.write("rules/c.md", "the fix of a check not read\n")
        t2 = self.mark("a..b (X-3, onsa-docs)", f"{p}..HEAD")
        code, out = self.due()
        n = 2 + len(bad)  # the notes of t2, then of t again
        self.assertEqual((code, out[:n]), (gate_steps.PARENT, [
            note.format(t2, "a..b (X-3, onsa-docs)"), note.format(t2, f"{p}..HEAD"), *[note.format(t, v) for v in bad]]))
        self.assertEqual(out[n:-1], [
            f"docs due: the last docs check is {t} (Docs-Checked: {'; '.join(bad)}; {p}..{p} (X-3, onsa-docs))",
            f"parent: rules/c.md: changed after the docs check {t}"])

    def test_no_value_read(self):
        # no commit with a value read: as no mark, the notes first
        self.write("rules/a.md", "b\n")
        t = self.mark("a..b (X-3, onsa-docs)")
        code, out = self.due("--stage-end", "W4")
        self.assertEqual((code, out[:2]), (1, [
            f"docs due: {t} has `Docs-Checked: a..b (X-3, onsa-docs)`, not <A>..<B> of two commits with B its parent "
            "or an ancestor of it; not counted as a check",
            "no commit from HEAD has a `Docs-Checked:` trailer that reads"]))  # fmt: skip
        self.assertIn("(fails at the stage end W4)", out[-1])

    def test_not_a_git_tree(self):
        plain = Path(self.tmp.name) / "rules"  # inside the tree, not its top
        code, out = quiet_out(docs_tool.main, ["due", "--root", str(plain)])
        self.assertEqual((code, out), (2, [f"docs.py due: {plain} is not the top of a git tree"]))


class DocsTree(unittest.TestCase):
    """A made-up tree of documents in a temporary directory (the base of DocsLayout and DocsCommands)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def layout(self, files=NEW_LAYOUT):
        for rel, text in files.items():
            self.write(rel, text)

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text(encoding="utf-8")
        self.assertEqual(text.count(old), 1, old)
        p.write_text(text.replace(old, new), encoding="utf-8")


class DocsLayout(DocsTree):
    """X-2 U2: the IDs and their paths, the kinds read from their directories, the spec as one text, the head
    fields, the field tables of the READMEs, `docs check` (a), (b), (c), (e), and the readers of the new layout."""

    def check(self):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main(["check", "--root", str(self.root)])
        lines = [x for x in out.getvalue().splitlines() if not x.startswith(("== ", "docs check: "))]
        return code, lines

    def assertOne(self, rel, old, new, finding):
        """Broken by one edit, `docs check` finds exactly `finding`; the edit undone, nothing."""
        self.edit(rel, old, new)
        self.assertEqual(self.check(), (1, [finding]), (rel, new))
        self.edit(rel, new, old)

    # ------------------------------------------------ the IDs and their paths

    def test_the_forms_of_the_ids_are_the_kinds(self):
        # X-2 U7c: the reasons of tests/pending.toml and the IDs of the SPEC-GAP marks are spelled by repo.KINDS
        for form, good, bad in ((pending.REASON, ("S-1", "R-22"), ("A-1", "RF-1", "S-1a", "S-", "W1-01", "xS-1")),
                                (gap_marks.ID, ("S-1", "R-22", "A-3"), ("RF-1", "D-1", "S-1 ", "NEW"))):  # fmt: skip
            self.assertEqual([x for x in good if form.fullmatch(x)], list(good))
            self.assertEqual([x for x in bad if form.fullmatch(x)], [])
        self.assertEqual(pending.REASON.pattern, repo.id_form("S", "R").pattern)
        self.assertEqual((pending.PHASE2, repo.kind_of(repo.PHASE2).name), (repo.PHASE2, repo.PHASE2))

    def test_the_cells_of_a_row(self):
        # X-2 U7c: one way to read a row (repo.table_cells): `\|` and a `|` in a code span do not divide
        self.assertEqual(repo.table_cells("| a | `b | c` | d \\| e |"), ["a", "`b | c`", "d \\| e"])
        self.assertEqual(repo.table_cells("a | b"), ["a", "b"])
        self.assertEqual([repo._first_cell(x) for x in ("| `W|1` | x |", "| W2", "W3 | x", "|")], ["`W|1`", "W2", "", ""])
        text = "| コード | 内容 | M |\n|---|---|---|\n| E0700 | `a | b` | 第 2 期 |\n| E0705 | x | y \\| 第 2 期 |\n"
        self.assertEqual(repo.phase2_codes(text), {"E0700"})

    def test_the_kinds_and_the_paths(self):
        self.assertEqual([repo.kind_of(i).name for i in ("RF-3", "R-3", "W3-13", "T5-8", "PH2", "C-40", "S-01")],
                         ["RF", "R", "W", "T", "PH2", "C", "S"])  # fmt: skip
        self.assertIsNone(repo.kind_of("S-1a"))
        self.assertEqual(repo.ID_RE.findall("UTF-8 RF-3 _S-1 S-2 W3-13/t S-345a PH2 T5-8 xR-9 `S-6`"),
                         ["RF-3", "S-2", "W3-13", "S-345", "T5-8", "S-6"])  # fmt: skip
        self.assertEqual(repo.path_of("S-537"), Path("decisions/S/S-537.md"))
        self.assertEqual(repo.path_of("S-537", draft=True), Path("decisions/S/S-537.draft.md"))
        self.assertEqual(repo.path_of("W3-13"), Path("tasks/W/W3-13.md"))
        for bad, draft in (("W3-13", True), ("C-40", False), ("PH2", False), ("x", False)):
            with self.assertRaises(repo.RepoError):
                repo.path_of(bad, draft)
        with self.assertRaisesRegex(repo.RepoError, "not split"):
            repo.section_path(self.root, "§2.1")
        self.layout()
        self.assertEqual([repo.section_path(self.root, s).as_posix() for s in ("§2.1", "§3", "§0.1", "§1", "tools.md §1")],
                         ["spec/02-a.md", "spec/03-b.md", "spec/README.md", "spec/README.md", "spec/tools.md"])  # fmt: skip
        for bad in ("§7", "6.1", "§"):
            with self.assertRaises(repo.RepoError):
                repo.section_path(self.root, bad)

    # ------------------------------------------------ the kinds read from their directories (X-2 DT-7)

    def test_t_is_never_read(self):
        """T has no directory: the history keeps it. `known`, `where` and `check` read no T work, also with the
        plan §4 of the old layout beside the files."""
        self.layout()
        self.write("docs/implementation-tasks.md", "# plan\n## 4. 作業\n| ID | 作業 |\n|---|---|\n| T1-1 | t |\n")
        self.assertIsNone(docs_tool.Index.of(self.root).known("T"))
        history = "not found (a kind with no file: the history or the second phase)"
        self.assertEqual(docs_tool.Ids(self.root).where("T1-1").place(), history)
        self.assertEqual(self.check(), (0, []))  # T5-8 of S-1 is not checked

    def test_the_foreign_forms_where_they_are(self):
        self.write("docs/foreign-forms.toml", '[[form]]\nid = "a"\n')  # the old place is not read
        self.assertEqual(pending.foreign_form_ids(self.root), "`spec/foreign-forms.toml` does not exist")
        self.write(repo.FOREIGN_FORMS, '[[form]]\nid = "b"\n')
        self.assertEqual(pending.foreign_form_ids(self.root), {"b"})

    # ------------------------------------------------ the spec as one text

    def test_the_spec_joined_from_its_chapters(self):
        self.layout()
        doc = repo.spec_doc(self.root)
        readme = NEW_LAYOUT["spec/README.md"]
        one = readme[: readme.index(repo.SPEC_INDEX_HEAD)] + NEW_LAYOUT["spec/02-a.md"] + NEW_LAYOUT["spec/03-b.md"]
        self.assertEqual(doc.text, one)
        self.assertEqual(repo.spec_text(self.root), one)
        line = one.split("\n").index("### 3.1 群") + 1
        self.assertEqual((doc.where(1), doc.where(line), doc.where(13)), ("spec/README.md:1", "spec/03-b.md:3", "spec/02-a.md:1"))
        self.assertEqual(spec_blocks.headings(doc.text), ["0", "0.1", "1", "2", "2.1", "2.2", "3", "3.1"])
        # the round trip: a spec of one file cut into chapters is joined back to the same text
        other = Path(self.tmp.name) / "cut"
        split_spec(one, other)
        self.assertEqual(repo.spec_text(other), one)
        self.assertEqual(repo.tools_text(self.root), NEW_LAYOUT["spec/tools.md"])

    def test_the_spec_that_cannot_be_joined(self):
        self.layout()
        readme = NEW_LAYOUT["spec/README.md"]
        for rel, text, error in (
            ("spec/README.md", readme.replace(repo.SPEC_INDEX_HEAD, "## 章"), "expected one line .*found 0"),
            ("spec/README.md", readme + repo.SPEC_INDEX_HEAD + "\n", "found 2"),
            ("spec/03-b.md", "## 4. 演算子\n", "spec/03-b.md:1: a chapter file starts with its heading `## 3. `"),
            ("spec/02-a.md", NEW_LAYOUT["spec/02-a.md"].rstrip("\n"), "spec/02-a.md: does not end with a line end"),
            ("spec/notes.md", "x\n", "spec/notes.md: not a chapter file"),
            ("spec/02-b.md", "## 2. x\n", "the chapter 2 is also spec/02-a.md"),
        ):
            before = (self.root / rel).read_text(encoding="utf-8") if (self.root / rel).exists() else None
            self.write(rel, text)
            with self.assertRaisesRegex(repo.RepoError, error):
                repo.spec_text(self.root)
            if before is None:
                (self.root / rel).unlink()
            else:
                self.write(rel, before)
        self.assertEqual(repo.spec_text(self.root)[:6], "# Spec")
        for rel in ("spec/02-a.md", "spec/03-b.md"):
            (self.root / rel).unlink()
        with self.assertRaisesRegex(repo.RepoError, "spec/: no chapter file"):
            repo.spec_text(self.root)

    PART = "### 0.5 細則\n\n#### 0.5.1 P2（一意性）\n\n一文。\n\n```onsa\nlet a = 1\n```\n\n"

    def with_part(self):
        """NEW_LAYOUT with §0.2 and a block in §1 in the README, and §0.5 in a file of its own."""
        self.layout()
        self.edit("spec/README.md", "### 0.1 原則\n\n---\n\n## 1. 全体\n",
                  "### 0.1 原則\n\n### 0.2 帰結\n\n---\n\n## 1. 全体\n\n```onsa\nlet b = 1\n```\n")  # fmt: skip
        self.write("spec/00-principles.md", self.PART)

    def test_a_part_of_the_spec_in_a_file_of_its_own(self):
        self.with_part()
        self.assertEqual(repo.SPEC_PARTS, {"0.5": Path("spec/00-principles.md")})
        doc, readme = repo.spec_doc(self.root), self.read_("spec/README.md")
        head = readme[: readme.index(repo.SPEC_INDEX_HEAD)]
        cut = head.index("## 1. 全体")
        one = head[:cut] + self.PART + head[cut:] + NEW_LAYOUT["spec/02-a.md"] + NEW_LAYOUT["spec/03-b.md"]
        self.assertEqual(doc.text, one)
        self.assertEqual(spec_blocks.headings(doc.text), ["0", "0.1", "0.2", "0.5", "0.5.1", "1", "2", "2.1", "2.2", "3", "3.1"])
        self.assertEqual([doc.where(n) for n in (10, 11, 13, 20, 21, 24, 29)], [
            "spec/README.md:10", "spec/00-principles.md:1", "spec/00-principles.md:3", "spec/00-principles.md:10",
            "spec/README.md:11", "spec/README.md:14", "spec/02-a.md:1"])  # fmt: skip
        self.assertEqual(sorted(repo.chapters(self.root)), [2, 3])  # the part is not the chapter 0
        self.assertEqual([repo.section_path(self.root, s).as_posix() for s in ("§0.5", "§0.5.1", "§0.2", "§0", "§1")],
                         ["spec/00-principles.md"] * 2 + ["spec/README.md"] * 3)  # fmt: skip
        # the round trip with the part
        other = Path(self.tmp.name) / "cut"
        split_spec(one, other)
        self.assertEqual(((other / "spec/00-principles.md").read_text(encoding="utf-8"), repo.spec_text(other)), (self.PART, one))
        # the readers: docs path and check, spec_sections, check_spec_examples
        code, out = quiet_out(docs_tool.main, ["path", "§0.5.1", "§0.5", "§0.2", "§1", "--root", str(self.root)])
        self.assertEqual((code, out), (0, ["spec/00-principles.md:3", "spec/00-principles.md:1", "spec/README.md:7", "spec/README.md:11"]))
        self.assertEqual(self.check(), (0, []))
        s1 = "decisions/S/S-1.md"
        self.edit(s1, '["§2.1"]', '["§2.1", "§0.5.1"]')
        self.edit(s1, "§3 と §2", "§3 と §0.5.1")
        self.assertEqual(self.check(), (0, []))
        self.assertOne(s1, "§3 と §0.5.1", "§3 と §0.5.2", f"{s1}:9: §0.5.2 is not a numbered heading of the spec")
        cases = [{"path": "tests/a.onsa", "spec": ["§0.5.1", "§0.2"]}, {"path": "tests/b.onsa", "spec": ["§0.5.2"]}]
        with mock.patch.object(repo, "cases_json", return_value=cases):
            code, out = quiet_out(spec_sections.main, ["--check"], root=self.root)
        self.assertEqual((code, [x for x in out if "§" in x]), (1, ["tests/b.onsa: [test] spec names §0.5.2, which is not "
                                                                   f"a numbered heading of {repo.SPEC_SHOWN}"]))  # fmt: skip
        problems, _ = cse.check(repo.spec_doc(self.root), self.root / "tests" / "spec", self.root / repo.PENDING, self.root)
        self.assertEqual([p.split("  ")[0] for p in problems], ["spec/00-principles.md:8", "spec/README.md:14", "spec/03-b.md:6"])

    def test_a_part_of_the_spec_that_cannot_be_joined(self):
        self.with_part()
        for rel, old, new, error in (
            ("spec/README.md", "### 0.2 帰結\n", "### 0.2 帰結\n\n### 0.5 古い\n",
             r"^spec/README.md:9: the heading of §0.5 is not in its file spec/00-principles.md$"),
            ("spec/README.md", "### 0.2 帰結\n", "### 0.2 帰結\n\n#### 0.5.3 古い\n", "^spec/README.md:9: the heading of §0.5.3"),
            ("spec/00-principles.md", "一文。\n", "一文。\n\n### 0.6 外\n",
             r"^spec/00-principles.md:7: the heading of §0.6 is not in its file spec/README.md$"),
            ("spec/00-principles.md", "### 0.5 細則\n", "前置き\n\n### 0.5 細則\n",
             r"^spec/00-principles.md:1: the file of §0.5 starts with its heading$"),
            ("spec/00-principles.md", "let a = 1\n```\n\n", "let a = 1\n```", "^spec/00-principles.md: does not end with a line end$"),
            ("spec/02-a.md", "### 2.2 キーワード", "### 3.2 キーワード", r"^spec/02-a.md:9: the heading of §3.2 is not in its file spec/03-b.md$"),
            ("spec/02-a.md", "### 2.2 キーワード", "### 5.2 キーワード", r"^spec/02-a.md:9: the heading of §5.2 is not in its file \(no file"),
        ):
            self.edit(rel, old, new)
            with self.assertRaisesRegex(repo.RepoError, error):
                repo.spec_text(self.root)
            self.edit(rel, new, old)
        self.assertEqual(spec_blocks.headings(repo.spec_text(self.root))[3:5], ["0.5", "0.5.1"])
        # without the file of the part, nothing is joined and §0.5 is in no file
        (self.root / "spec/00-principles.md").unlink()
        self.assertNotIn("0.5", spec_blocks.headings(repo.spec_text(self.root)))

    def read_(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    # ------------------------------------------------ the head fields

    def test_read_the_head_fields(self):
        head = docs_tool.read_head(NEW_LAYOUT["decisions/S/S-1.md"])
        self.assertEqual(head.values, {"status": "DECIDED", "spec": ["§2.1"], "tasks": ["W1-01"],
                                       "decided": datetime.date(2026, 10, 15)})  # fmt: skip
        self.assertEqual((head.key_lines["decided"], head.heading), (5, (7, "# S-1 字句")))
        self.assertEqual(docs_tool.read_head(NEW_LAYOUT["issues/R/R-1.md"]).values["aspect"], 1)
        for text, error, line in (("# S-1\n", docs_tool.NO_HEAD, 1), ("+++\nstatus = 1\n", docs_tool.NOT_CLOSED, 1),
                                  ("+++\n", docs_tool.NOT_CLOSED, 1), ('+++\na = "x"\nb = OPEN\n+++\n', "Invalid value", 3),
                                  ('+++\na = "x"\na = "y"\n+++\n', "Cannot overwrite a value", 4)):  # where tomllib stops  # fmt: skip
            head = docs_tool.read_head(text)
            self.assertEqual((head.values, head.error, head.error_line), (None, error, line), text)

    def test_write_the_head_fields_in_the_normal_form(self):
        self.layout()
        order = docs_tool.field_table(docs_tool.Tree(self.root, []), repo.KIND["S"]).order
        body = "# S-3 x\n\n本文 `+++` と\n+++\n末尾\n"
        p = self.write("decisions/S/S-3.md", "+++\ndecided=2026-10-15\n  status  =  'OPEN'\ntasks=['W1-01','W1-02']\n+++\n" + body)
        values = docs_tool.read_head(p.read_text(encoding="utf-8")).values
        docs_tool.write_head(self.root, "decisions/S/S-3.md", values, order)
        self.assertEqual(p.read_bytes().decode(), '+++\nstatus = "OPEN"\ntasks = ["W1-01", "W1-02"]\ndecided = 2026-10-15\n+++\n' + body)
        new = docs_tool.head_update(self.root, "decisions/S/S-3.md", {**values, "decided": None, "group": 3}, order)
        self.assertEqual(new, '+++\nstatus = "OPEN"\ntasks = ["W1-01", "W1-02"]\ngroup = 3\n+++\n' + body)
        # a file with no head fields gets them; the closing line with no line end gets one
        self.write("decisions/S/S-4.md", "# S-4\n")
        self.assertEqual(docs_tool.head_update(self.root, "decisions/S/S-4.md", {"status": "OPEN"}, order),
                         '+++\nstatus = "OPEN"\n+++\n# S-4\n')  # fmt: skip
        self.write("decisions/S/S-5.md", '+++\nstatus = "OPEN"\n+++')
        self.assertEqual(docs_tool.head_update(self.root, "decisions/S/S-5.md", {"status": "DROPPED"}, order),
                         '+++\nstatus = "DROPPED"\n+++\n')  # fmt: skip
        # nothing is written: a key not in the table, a value TOML has but the form not, a swap file,
        # head fields that cannot be read, CR line ends
        before = p.read_bytes()
        for values, error in (({"color": "x"}, "`color` is not a field"), ({"status": True}, "cannot write True")):
            with self.assertRaisesRegex(docs_tool.DocsError, error):
                docs_tool.write_head(self.root, "decisions/S/S-3.md", values, order)
        self.write("decisions/S/.S-3.md.swp", "")
        with self.assertRaisesRegex(docs_tool.DocsError, "swap file"):
            docs_tool.write_head(self.root, "decisions/S/S-3.md", {"status": "OPEN"}, order)
        self.assertEqual(p.read_bytes(), before)
        self.write("decisions/S/S-6.md", "+++\nstatus = OPEN\n+++\n# S-6\n")
        with self.assertRaisesRegex(docs_tool.DocsError, "S-6.md:2: Invalid value; fix the head fields by hand"):
            docs_tool.head_update(self.root, "decisions/S/S-6.md", {"status": "OPEN"}, order)
        (self.root / "decisions/S/S-7.md").write_bytes(b'+++\r\nstatus = "OPEN"\r\n+++\r\n')
        with self.assertRaisesRegex(docs_tool.DocsError, "CR line ends"):
            docs_tool.head_update(self.root, "decisions/S/S-7.md", {"status": "OPEN"}, order)

    # ------------------------------------------------ docs check

    def test_check_passes_on_the_new_layout(self):
        self.layout()
        code, lines = self.check()
        self.assertEqual((code, lines), (0, []))

    def test_check_heads(self):
        self.layout()
        s1, w2, r1, a1 = "decisions/S/S-1.md", "tasks/W/W1-02.md", "issues/R/R-1.md", "decisions/A/A-1.md"
        self.assertOne(s1, 'status = "DECIDED"', "status = DECIDED", f"{s1}:2: Invalid value")
        self.assertOne(s1, "+++\n#", "#", f"{s1}:1: {docs_tool.NOT_CLOSED}")
        self.assertOne(a1, '+++\nstatus = "DECIDED"\n+++\n', "<!-- x -->\n", f"{a1}:1: {docs_tool.NO_HEAD}")
        self.assertOne(a1, '"DECIDED"', '"DECIDED"\ncolor = "red"', f"{a1}:3: `color` is not a field of decisions/README.md")
        self.assertOne(a1, 'status = "DECIDED"', 'group = 1', f"{a1}:1: the field `status` is required (decisions/README.md)")
        self.assertOne(a1, '"DECIDED"', '"DONE"', f"{a1}:2: `status` has \"DONE\", not one of OPEN / DECIDED / DROPPED")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'tasks = "W1-01"', f"{s1}:4: `tasks` is not an array; its form is ID の並び（W、T、PH2）")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'tasks = ["S-2"]', f"{s1}:4: `tasks` has \"S-2\", not an ID of W、T、PH2")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'before = "S-2"', f"{s1}:4: `before` has \"S-2\", not an ID of W、段、PH2")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'before = "x4"', f"{s1}:4: `before` has \"x4\", not an ID of W、段、PH2")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'before = "W1-"', f"{s1}:4: `before` has \"W1-\", not an ID of W、段、PH2")
        self.assertOne(s1, 'tasks = ["W1-01"]', 'tasks = ["W1"]', f"{s1}:4: `tasks` has \"W1\", not an ID of W、T、PH2")
        self.assertOne(s1, '["§2.1"]', '["2.1"]', f"{s1}:3: `spec` has \"2.1\", not a section (`§6.1`, `tools.md §3.2`)")
        self.assertOne(s1, "2026-10-15", '"2026-10-15"', f"{s1}:5: `decided` has \"2026-10-15\", not a date")
        self.assertOne(r1, "aspect = 1", 'aspect = "1"', f"{r1}:4: `aspect` has \"1\", not one of 1 / 2 / 3")
        self.assertOne(w2, '["基盤"]', '["基盤", "危険"]', f"{w2}:5: `marks` has \"危険\", not one of 基盤 / メモ")
        self.assertOne(a1, "# A-1 is_some", "# A-2 is_some", f"{a1}:4: the first line after the head fields is not `# A-1 <title>`")
        self.assertOne(a1, "# A-1 is_some", "A-1", f"{a1}:4: the first line after the head fields is not `# A-1 <title>`")
        self.write("decisions/S/S1.md", "x")
        self.write("decisions/S/R-1.md", "x")
        code, lines = self.check()
        self.assertEqual(lines, ["decisions/S/R-1.md:1: the name is not an ID of S (decisions/S/<ID>.md)",
                                 "decisions/S/S1.md:1: the name is not an ID of S (decisions/S/<ID>.md)"])  # fmt: skip
        (self.root / "decisions/S/S1.md").unlink()
        (self.root / "decisions/S/R-1.md").unlink()
        (self.root / "decisions/K").mkdir()
        self.assertEqual(self.check(), (1, ["decisions/K: no file of an ID; the checks would pass reading nothing"]))
        (self.root / "decisions/K").rmdir()
        # X-2 U7c: the stage of a work (its ID) is a stage of the table of the stages
        self.write("tasks/W/W3-01.md", '+++\nstatus = "PLAN"\n+++\n# W3-01 x\n')
        self.assertEqual(self.check(), (1, ["tasks/W/W3-01.md:1: W3: not a stage of tasks/stages.md (W1, W2, M5, M9); the stage of W3-01"]))

    def test_check_a_broken_field_table_is_one_finding(self):
        self.layout()
        readme = "tasks/W/README.md"
        # the files of the directory are not checked (W1-02 is broken too); the others still are
        self.edit("tasks/W/W1-02.md", 'size = "M"', 'size = "XL"')
        for old, new, what in (
            ("| `size` | 閉じた値 | `S` / `M` / `L` | いいえ | 大きさ |", "| `size` | 閉じた値 | `S` / `M` / `L` | いいえ |", "8: the field table: 4 cells, not 5"),
            ("| `depends` | ID の並び（W、段） |", "| `depends` | ID の列（W、段） |", "9: the field table: the form `ID の列（W、段）` is not known"),
            ("| `depends` | ID の並び（W、段） |", "| `depends` | ID の並び（W、Z） |", "9: the field table: the form `ID の並び（W、Z）` names a kind"),
            ("`S` / `M` / `L`", "`S` /  / `L`", "8: the field table: the values `S` /  / `L`"),
            ("`S` / `M` / `L`", "`S` / `S`", "8: the field table: the values `S` / `S`"),
            ("| `commit` | 文字列 | — |", "| `commit` | 文字列 | x |", "12: the field table: the values x of the form 文字列"),
            ("| コミット |", "| コミット |\n| `Commit` | 文字列 | — | いいえ | x |", "13: the field table: the key `Commit`"),
            ("| コミット |", "| コミット |\n| `size` | 文字列 | — | いいえ | x |", "13: the field table: the key `size` is given twice"),
            ("| `size` | 閉じた値 | `S` / `M` / `L` | いいえ |", "| `size` | 閉じた値 | `S` / `M` / `L` | yes |", "8: the field table: 要る is `yes`"),
            ("| キー | 形 | 値 | 要る | 意味 |", "| キー | 型 | 値 | 要る | 意味 |", "5: the field table: the header is not"),
            ("## 頭の欄\n\n", "## 頭の欄\n\n## 次\n\n", "3: the field table: no table under the heading"),
            ("# 作業\n", "# 作業\n\n## 頭の欄\n", "5: the field table: a second `## 頭の欄`"),
        ):
            self.edit(readme, old, new)
            code, lines = self.check()
            if "cells" in what:  # the check of the tables (d) finds the row too
                self.assertEqual(lines.pop(0), f"{readme}:8: the row has 4 cells, the header 5")
            self.assertEqual(len(lines), 1, (what, lines))
            self.assertTrue(lines[0].startswith(f"{readme}:{what}"), (what, lines))
            self.edit(readme, new, old)
        (self.root / readme).unlink()
        self.assertEqual(self.check()[1], ["tasks/W/README.md: no field table (`## 頭の欄` in tasks/W/README.md or tasks/README.md)"])

    def test_check_refs(self):
        self.layout()
        s1, s2, w2 = "decisions/S/S-1.md", "decisions/S/S-2.md", "tasks/W/W1-02.md"
        self.assertOne(s2, '["W1-02", "PH2"]', '["W1-09", "PH2", "T9-9"]', f"{s2}:3: tasks: W1-09 is not found (tasks/W/)")
        self.assertOne(s2, "found_by = \"W1-01/t\"", "found_by = \"W1-08/t\"", f"{s2}:4: found_by: W1-08 is not found (tasks/W/)")
        self.assertOne(s2, "R-1 と A-1", "R-1 と A-1、R-1、A-2、A-2", f"{s2}:7: A-2 is not found (decisions/A/)")
        self.assertOne(w2, '["W1-01"]', '["W1-08"]', f"{w2}:4: depends: W1-08 is not found (tasks/W/)")
        # `depends` a stage (U5e): there when the table of the stages has it (X-2 U6), with or without a work
        for stage in ("W1", "W2", "M5"):
            self.edit(w2, '["W1-01"]', f'["{stage}", "W1-01"]')
            self.assertEqual(self.check(), (0, []), stage)
            self.edit(w2, f'["{stage}", "W1-01"]', '["W1-01"]')
        self.assertOne(w2, '["W1-01"]', '["W1-01", "W3"]', f"{w2}:4: depends: W3: not a stage of tasks/stages.md (W1, W2, M5, M9)")
        self.assertOne(w2, '["W1-01"]', '["X4"]', f"{w2}:4: depends: X4: not a stage of tasks/stages.md (W1, W2, M5, M9)")
        for bad in ("W1-", "PH2", "W"):
            self.assertOne(w2, '["W1-01"]', f'["{bad}"]', f'{w2}:4: `depends` has "{bad}", not an ID of W、段')
        self.assertOne(s1, '["§2.1"]', '["§2.1", "§9.9"]', f"{s1}:3: spec: §9.9 is not a numbered heading of the spec")
        self.assertOne(s1, "§3 と §2", "§3 と §2、§7", f"{s1}:9: §7 is not a numbered heading of the spec")
        self.assertOne(s1, "`tools.md §1`", "`tools.md §1・§2`", f"{s1}:9: tools.md §2 is not a numbered heading of the spec of the tools")
        # `before`: a stage is there when the table has it (W2 and M5 have no work); PH2 is not checked; `W2` in the
        # text is not an ID
        for due in ("W1", "W2", "M5", "M9", "PH2", "W1-02"):
            self.edit(s2, 'found_by = "W1-01/t"', f'found_by = "W1-01/t"\nbefore = "{due}"')
            self.assertEqual(self.check(), (0, []), due)
            self.edit(s2, f'found_by = "W1-01/t"\nbefore = "{due}"', 'found_by = "W1-01/t"')
        self.assertOne(s2, 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W3"', f"{s2}:5: before: W3: not a stage of tasks/stages.md (W1, W2, M5, M9)")
        self.assertOne(s2, 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W2-01"', f"{s2}:5: before: W2-01 is not found (tasks/W/)")
        self.edit(s2, "R-1 と A-1", "R-1 と A-1、W2 まで")
        self.assertEqual(self.check(), (0, []))
        self.edit(s2, "R-1 と A-1、W2 まで", "R-1 と A-1")
        # a kind whose directory is not there is not checked (as D, K, Q; `Index.known`): R-1 of S-2
        for rel in ("issues/R/R-1.md", "issues/R/README.md"):
            (self.root / rel).unlink()
        (self.root / "issues/R").rmdir()
        self.assertEqual(self.check(), (0, []))

    def test_check_relations(self):
        self.layout()
        s1, s2, r1, w1 = "decisions/S/S-1.md", "decisions/S/S-2.md", "issues/R/R-1.md", "tasks/W/W1-01.md"
        self.assertOne(s2, '["W1-02", "PH2"]', '["W1-01"]', f"{s2}:2: OPEN, but every work of `tasks` is DONE (W1-01)")
        self.assertOne(r1, 'fix = ["W1-02"]', 'fix = ["W1-01"]', f"{r1}:2: OPEN, but every work of `fix` is DONE (W1-01)")
        self.assertOne(w1, 'commit = "abc"', 'doing = ["U1/i"]', f"{w1}:3: `doing` on a work that is DONE, not DOING")
        # X-2 U7b: an ID field the README adds needs its direction in RESTS_ON (`graph`)
        row = "| `found_by` | 文字列 | — | いいえ | 見つけた票 |\n"
        self.assertOne("decisions/README.md", row, row + "| `see` | ID の並び（S） | — | いいえ | 見る |\n",
                       "decisions/README.md:11: the ID field `see` has no direction in `docs.RESTS_ON` (`graph` needs it)")  # fmt: skip

    def test_the_stages_of_the_works(self):
        # X-2 U7c: (a) looks at the stage of every work, and each is in the table (the real tree's ID fields and
        # the label 持ち越し are the cross-check item's, W4-18 U10b)
        self.layout()
        tree = docs_tool.Tree(self.root, [])
        seen = []
        real = docs_tool._missing

        def spy(idx, ref, which):
            seen.append((ref, which))
            return real(idx, ref, which)

        with mock.patch.object(docs_tool, "_missing", spy):
            found = [str(f) for f in docs_tool.check_heads(tree) if "not a stage" in f.message]
        stages = [ref for ref, which in seen if which == docs_tool.STAGE_KIND]
        self.assertEqual(len(stages), len(tree.index.files["W"]))
        self.assertGreater(len(stages), 0)
        self.assertEqual(found, [])

    def test_amends_is_no_field(self):
        # X-2 U7a: `amends` and `amended_by` are out of the field table and of the tool; written, (a) finds them
        self.layout()
        s1, s2 = "decisions/S/S-1.md", "decisions/S/S-2.md"
        self.assertOne(s2, 'found_by = "W1-01/t"', 'amends = ["S-1"]\nfound_by = "W1-01/t"',
                       f"{s2}:4: `amends` is not a field of decisions/README.md")  # fmt: skip
        self.assertOne(s1, "decided = 2026-10-15", 'amended_by = ["S-2"]\ndecided = 2026-10-15',
                       f"{s1}:5: `amended_by` is not a field of decisions/README.md")  # fmt: skip
        self.assertNotIn("amend", docs_tool.COMMANDS)

    def test_check_links(self):
        self.layout()
        self.assertOne("README.md", "[仕様](spec/README.md)", "[仕様](spec/README.md)、[無い](docs/none.md#x)", "README.md:3: the link docs/none.md#x is not found")
        self.assertOne("rules/README.md", "(common.md)", "(commons.md)", "rules/README.md:3: the link commons.md is not found")

    def test_check_tools(self):
        # X9-9: the tools, their commands and arguments named in a code span of the rules and the definitions
        self.layout()
        self.write("tools/cmd.py", "import repo\n\nC = repo.Command\nCOMMANDS = {\n"
                   "    'run': C(lambda p: p.add_argument('--go', action='store_true'), None, ('i',), 'a', 'b', 'cmd.py run'),\n"
                   "    'stop': C(lambda p: p.add_argument('--now'), None, ('i',), 'a', 'b', 'cmd.py stop'),\n}\n"
                   "if __name__ == '__main__':\n    raise SystemExit(3)\n")  # fmt: skip
        self.write("tools/hooks/plain.sh", "# plain.sh [--quick] run\n")
        self.write("tools/tuple.py", "COMMANDS = (('check',),)  # not of repo.Command: its text\n# --fast\n")
        self.write("tools/broken.py", "COMMANDS = {\n")
        good = ("`cmd.py run --go`、`python3 -B tools/cmd.py stop --now=1`、`cmd.py`、`cmd.py <命令> --go`、`cmd.py --now`、"
                "`cmd.py run --help`、`cmd.py help --role i`、`cmd.py stop … -h`、`tools/hooks/plain.sh --quick <ID>`、"
                "`plain.sh nosuch [--quick]`、`tuple.py --fast`、`git log --oneline`、`onsa check --x`、`x.rs`、"
                "`cmd.py run -- --other`、`python3 -B tools/cmd.py run 'a --b'`\n")  # fmt: skip
        self.write("rules/x.md", f"# x\n\n{good}\n```sh\ncmd.py nosuch --bad\n```\n")
        self.write(".claude/agents/onsa-x.md", "定義 `tools/cmd.py stop`\n")
        self.write("CLAUDE.md", "`plain.sh`\n")
        self.assertEqual(self.check(), (0, []))
        for rel, old, new, found in (
            ("rules/x.md", "`x.rs`", "`nosuch.py`", "no tool nosuch.py (tools/nosuch.py, tools/hooks/nosuch.py)"),
            ("rules/x.md", "`cmd.py`、", "`cmd.py walk <ID>`、", "walk is not a command of cmd.py"),
            ("rules/x.md", "stop --now=1", "stop --go", "--go is not an argument of tools/cmd.py stop"),
            ("rules/x.md", "`cmd.py --now`", "`cmd.py --later`", "--later is not an argument of cmd.py"),
            ("rules/x.md", "help --role i", "help --roles i", "--roles is not an argument of cmd.py help"),
            ("rules/x.md", "plain.sh --quick <ID>", "plain.sh --qui <ID>", "--qui is not an argument of tools/hooks/plain.sh"),
            ("rules/x.md", "`x.rs`", "`broken.py run`", "broken.py cannot be read: SyntaxError: '{' was never closed (…"),
            (".claude/agents/onsa-x.md", "tools/cmd.py stop", "tools/hooks/cmd.py stop", "no tool tools/hooks/cmd.py (…"),
            ("CLAUDE.md", "`plain.sh`", "`plain.sh -x`", "-x is not an argument of plain.sh"),
        ):  # fmt: skip
            with self.subTest(new=new):
                self.edit(rel, old, new)
                code, lines = self.check()
                self.assertEqual((code, len(lines)), (1, 1), lines)
                line = 3 if rel == "rules/x.md" else 1
                self.assertTrue(lines[0].startswith(f"{rel}:{line}: `"), lines)
                self.assertIn(found.split("(…")[0], lines[0])
                self.edit(rel, new, old)

    # ------------------------------------------------ the readers of the current tools

    def test_load_docs_reads_the_files_of_the_ids(self):
        self.layout()
        new = pending.load_docs(self.root)
        self.assertEqual((new.works, new.done, new.reasons), ({"W1-01", "W1-02"}, {"W1-01"}, {"S-1", "S-2", "R-1"}))
        self.assertEqual((new.works_at, new.reasons_at, new.sections), ("tasks/W/", "decisions/S/, issues/R/",
                                                                         {"0", "0.1", "1", "2", "2.1", "2.2", "3", "3.1"}))
        self.assertEqual(gap_marks.api_ids(self.root), {"A-1"})
        text, doc = repo.diag_text(self.root)
        self.assertEqual((repo.retired_codes(text, doc), repo.phase2_codes(text, doc)), ({"E0611"}, {"E0612", "E0613"}))
        self.assertEqual(repo.diag_text(self.root)[1], repo.DIAG_CODES)
        with self.assertRaisesRegex(repo.RepoError, "tasks/diag-codes.md: no row of the table is `第 2 期`"):
            repo.phase2_codes("| E0001 | x |\n", repo.DIAG_CODES)
        # a directory with no file of an ID is an error, not an empty table
        for rel in ("tasks/W/W1-01.md", "tasks/W/W1-02.md"):
            (self.root / rel).unlink()
        with self.assertRaisesRegex(pending.DocsError, "tasks/W/: no file of an ID"):
            pending.load_docs(self.root)

    def test_the_readers_of_the_spec_in_the_new_layout(self):
        self.layout()
        # spec_sections: a section only the chapters have
        cases = [{"path": "tests/a.onsa", "spec": ["§3.1"]}, {"path": "tests/b.onsa", "spec": ["§9.9"]}]
        with mock.patch.object(repo, "cases_json", return_value=cases):
            out = io.StringIO()
            with mock.patch.object(sys, "stdout", out):
                code = spec_sections.main(["--check"], root=self.root)
        self.assertEqual(code, 1)
        self.assertIn("tests/b.onsa: [test] spec names §9.9", out.getvalue())
        self.assertNotIn("§3.1", out.getvalue())
        # keywords: §2.2 of the chapter 2
        with mock.patch.object(repo, "cases_json", return_value=["fn", "let"]):
            self.assertEqual(quiet(keywords.main, ["--root", str(self.root)]), 0)
        # default_inits: the lines of the blocks in their files
        srcs = default_inits.sources(self.root)[0]
        self.assertEqual([(s.shown, s.first) for s in srcs], [("spec/03-b.md", 6), ("spec/tools.md", 6)])
        # check_spec_examples: the lines of the blocks in their files
        problems, _ = cse.check(repo.spec_doc(self.root), self.root / "tests" / "spec", self.root / repo.PENDING, self.root)
        self.assertEqual([p.split("  ")[0] for p in problems], ["spec/03-b.md:6"])


class DocsCommands(DocsTree):
    """X-2 U3: the commands of `docs.py` that read (path, back, refs; show, list, changes, ticket) and
    write (set, note, new, draft), on NEW_LAYOUT."""

    def setUp(self):
        super().setUp()
        patcher = mock.patch.object(docs_tool, "today", return_value=datetime.date(2026, 10, 16))
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_(self, *argv):
        out = io.StringIO()
        with mock.patch.object(sys, "stdout", out), mock.patch.object(sys, "stderr", out):
            code = docs_tool.main([*argv, "--root", str(self.root)])
        return code, out.getvalue().splitlines()

    def read(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    def assertRefused(self, argv, lines, unchanged=()):
        """`docs.py <argv>` writes nothing, prints `lines`, and exits 1."""
        before = {rel: self.read(rel) for rel in unchanged}
        code, out = self.run_(*argv)
        self.assertEqual((code, out), (1, [*lines, f"docs {argv[0]}: nothing is written"]), argv)
        self.assertEqual({rel: self.read(rel) for rel in unchanged}, before)

    # ------------------------------------------------ path, back, refs

    def test_path(self):
        self.layout()
        self.assertEqual(self.run_("path", "S-1", "W1-02", "R-1", "A-1", "§2.1", "§0.1", "§3", "tools.md §1"), (0, [
            "decisions/S/S-1.md", "tasks/W/W1-02.md", "issues/R/R-1.md", "decisions/A/A-1.md", "spec/02-a.md:3",
            "spec/README.md:5", "spec/03-b.md:1", "spec/tools.md:3"]))  # fmt: skip
        self.assertEqual(self.run_("path", "S-9", "S-2", "§9.9", "tools.md §2", "C-40", "D-1"), (1, [
            "S-9: not found (decisions/S/)", "decisions/S/S-2.md", "§9.9: not found (not a numbered heading of the spec)",
            "tools.md §2: not found (not a numbered heading of the spec of the tools)",
            "C-40: not found (a kind with no file: the history or the second phase)", "D-1: not found (no decisions/D/)"]))  # fmt: skip
        self.assertEqual(self.run_("path", "--abs", "S-1"), (0, [(self.root / "decisions/S/S-1.md").resolve().as_posix()]))
        code, out = self.run_("path", "S-1", "x")
        self.assertEqual((code, out[-1]), (2, "docs.py path: x: not an ID or a section (`S-537`, `§6.1`, `tools.md §3.2`)"))

    def test_back(self):
        self.layout()
        self.write("history/old.md", "S-2 と S-22\n")
        long = "あ" * 100 + "S-2" + "い" * 100
        self.write("rules/common.md", f"# 共通\n\n{long}\n")
        self.assertEqual(self.run_("back", "S-2"), (0, [
            "== keys", "issues/R/R-1.md:5: decisions",
            "== text", "decisions/S/S-1.md:10: - 経緯: C-40 と T5-8 と D-15 は確かめない。`decisions/S/S-2.md` も指す。",
            "rules/common.md:3: …" + "あ" * 60 + "S-2" + "い" * 60 + "…",
            "docs back: S-2: 1 key(s), 2 line(s) of text in 3 file(s)"]))  # fmt: skip
        code, out = self.run_("back", "S-2", "--history")
        self.assertEqual(out[-2:], ["history/old.md:1: S-2 と S-22", "docs back: S-2: 1 key(s), 3 line(s) of text in 4 file(s)"])
        # a key of the head fields: in a string (`found_by`) too; a work in the second phase
        self.assertEqual(self.run_("back", "W1-01")[1][:3], ["== keys", "decisions/S/S-1.md:4: tasks", "decisions/S/S-2.md:4: found_by"])
        self.assertEqual(self.run_("back", "PH2")[1], ["== keys", "decisions/S/S-2.md:3: tasks", "docs back: PH2: 1 key(s), 0 line(s) of text in 1 file(s)"])
        self.assertEqual(self.run_("back", "S-99")[1], ["docs back: S-99: 0 key(s), 0 line(s) of text in 0 file(s)"])
        self.assertEqual(self.run_("back", "x")[0], 2)

    def test_refs(self):
        self.layout()
        rows = [
            "W1-01\tDONE\ttasks/W/W1-01.md\tgate", "W1-02\tDOING\ttasks/W/W1-02.md\t式",
            "C-40\t-\tnot found (a kind with no file: the history or the second phase)\t-",
            "T5-8\t-\tnot found (a kind with no file: the history or the second phase)\t-",
            "D-15\t-\tnot found (no decisions/D/)\t-", "S-2\tOPEN\tdecisions/S/S-2.md\tR-1 と A-1。",
            "S-77\t-\tnot found (decisions/S/)\t-",
            "docs refs: decisions/S/S-1.md: 7 ID(s), 4 not found",
        ]  # fmt: skip
        self.assertEqual(self.run_("refs", "decisions/S/S-1.md"), (0, rows))
        self.assertEqual(self.run_("refs", "S-1"), (0, rows))
        self.assertEqual(self.run_("refs", str(self.root / "decisions/S/S-1.md")), (0, rows))
        # head fields that cannot be read are read as text; the draft is not its S
        self.assertEqual(self.run_("refs", "decisions/S/S-2.draft.md")[1][:2], ["S-3\t-\tnot found (decisions/S/)\t-", "S-999\t-\tnot found (decisions/S/)\t-"])
        self.assertEqual(self.run_("refs", "docs/none.md"), (1, ["docs/none.md: not found"]))
        self.assertEqual(self.run_("refs", "S-9"), (1, ["S-9: not found (decisions/S/)"]))
        self.assertEqual(self.run_("refs", "/elsewhere/a.md")[0], 2)

    # ------------------------------------------------ graph (X-2 U7b)

    def graph_layout(self):
        """NEW_LAYOUT with `before` (a work, a stage), S-1 and S-2 naming each other (S-2 itself too), a rule
        naming S-1, W1-01 naming S-1 and S-2 naming W1-01 in the text too (the typed edge, then `text(key)`, is
        shown), and W2-01 that depends on its own stage (the stage rests on its works: a cycle)."""
        self.layout()
        self.edit("tasks/W/W1-01.md", "# W1-01 gate\n", "# W1-01 gate\n\nS-1 の作業。\n")
        self.edit("decisions/S/S-1.md", "decided = 2026-10-15", 'before = "W1-02"\ndecided = 2026-10-15')
        self.edit("decisions/S/S-2.md", "- 空白: R-1 と A-1。\n", "- 空白: R-1 と A-1。\n- 経緯: S-1 と S-2 と W1-01（`found_by` の作業）。\n")
        self.edit("decisions/A/A-1.md", 'status = "DECIDED"', 'status = "DECIDED"\nbefore = "W2"')
        self.write("rules/common.md", "# 共通\n\nS-1 を見る。\n")
        self.write("tasks/W/W2-01.md", '+++\nstatus = "PLAN"\ndepends = ["W2"]\n+++\n# W2-01 輪\n')

    def test_graph_edges(self):
        self.graph_layout()
        edges = docs_tool.edges(docs_tool.Ids(self.root, repo.doc_files(self.root)))
        # the ID fields turned by RESTS_ON and the stages: `on -> base`
        self.assertEqual({e for e in edges if docs_tool.typed_edge(e[2])}, {
            ("W1-01", "S-1", "tasks"), ("W1-02", "S-1", "before"), ("W1-02", "S-2", "tasks"), ("PH2", "S-2", "tasks"),
            ("R-1", "S-2", "decisions"), ("W1-02", "R-1", "fix"), ("W1-02", "W1-01", "depends"), ("W2-01", "W2", "depends"),
            ("W2", "A-1", "before"), ("W1", "W1-01", "stage"), ("W1", "W1-02", "stage"), ("W2", "W2-01", "stage")})  # fmt: skip
        self.assertLessEqual({("S-2", "W1-01", "text(found_by)"), ("R-1", "W1-02", "text(found_by)"), ("S-1", "S-2", "text"),
                              ("S-2", "S-1", "text"), ("W1-01", "S-1", "text"), (Path("rules/common.md"), "S-1", "text"),
                              (Path("decisions/S/S-2.draft.md"), "S-3", "text")}, edges)  # fmt: skip
        self.assertFalse([e for e in edges if e[0] == e[1] or isinstance(e[1], Path)])  # no edge to itself; a path is a leaf

    def test_graph(self):
        self.graph_layout()
        start = "0\tS-2\t-\t-\tOPEN\tR-1 と A-1。"
        one = ["1\tS-1\ttext\tS-2\tDECIDED\t字句", "1\tR-1\tdecisions\tS-2\tOPEN\t候補", "1\tW1-02\ttasks\tS-2\tDOING\t式",
               "1\tPH2\ttasks\tS-2\t-\t-"]  # fmt: skip
        two = ["2\tW1-01\ttasks\tS-1\tDONE\tgate", "2\tW1\tstage\tW1-02\t残り 1\t-", "2\trules/common.md\ttext\tS-1\t-\t-",
               "2\ttasks/diag-codes.md\ttext\tS-1\t-\t-"]  # fmt: skip
        self.assertEqual(self.run_("graph", "S-2", "--back"), (0, [
            start, *one, "docs graph: S-2 --back: 4 node(s) at depth ≤ 1 (3 typed, 1 text); 4 more at depth 2"]))
        self.assertEqual(self.run_("graph", "S-2", "--back", "--depth", "2"), (0, [
            start, *one, *two, "docs graph: S-2 --back: 8 node(s) at depth ≤ 2 (5 typed, 3 text); 0 more at depth 3"]))
        self.assertEqual(self.run_("graph", "S-2", "--back", "--depth", "5")[1][-1],
                         "docs graph: S-2 --back: 8 node(s) at depth ≤ 5 (5 typed, 3 text); 0 more at depth 6")
        # --typed: S-1 (named in the text only) and the paths are gone
        self.assertEqual(self.run_("graph", "S-2", "--back", "--typed", "--depth", "2"), (0, [
            start, *one[1:], "2\tW1\tstage\tW1-02\t残り 1\t-",
            "docs graph: S-2 --back --typed: 4 node(s) at depth ≤ 2 (4 typed, 0 text); 0 more at depth 3"]))
        # forward: S-1 and S-2 name each other (a cycle), each node once; `text(found_by)` is counted as text
        self.assertEqual(self.run_("graph", "S-1", "--depth", "2")[1][1:], [
            "1\tS-2\ttext\tS-1\tOPEN\tR-1 と A-1。", "1\tS-77\ttext\tS-1\t-\t-", "1\tD-15\ttext\tS-1\t-\t-",
            "1\tW1-02\ttext\tS-1\tDOING\t式", "1\tC-40\ttext\tS-1\t-\t-", "1\tT5-8\ttext\tS-1\t-\t-",
            "2\tA-1\ttext\tS-2\tDECIDED\tis_some", "2\tR-1\ttext\tS-2\tOPEN\t候補", "2\tW1-01\ttext(found_by)\tS-2\tDONE\tgate",
            "docs graph: S-1: 9 node(s) at depth ≤ 2 (0 typed, 9 text); 0 more at depth 3"])  # fmt: skip
        # the stage and `depends` make a cycle; the next depth counts only the new nodes
        self.assertEqual(self.run_("graph", "W2-01", "--back", "--depth", "5")[1], [
            "0\tW2-01\t-\t-\tPLAN\t輪", "1\tW2\tstage\tW2-01\t残り 1\t-",
            "docs graph: W2-01 --back: 1 node(s) at depth ≤ 5 (1 typed, 0 text); 0 more at depth 6"])  # fmt: skip
        self.assertEqual(self.run_("graph", "W2", "--depth", "5")[1], [
            "0\tW2\t-\t-\t残り 1\t-", "1\tA-1\tbefore\tW2\tDECIDED\tis_some", "1\tW2-01\tstage\tW2\tPLAN\t輪",
            "docs graph: W2: 2 node(s) at depth ≤ 5 (2 typed, 0 text); 0 more at depth 6"])  # fmt: skip
        self.assertEqual(self.run_("graph", "W1-01", "--back")[1][1:], [
            "1\tS-2\ttext(found_by)\tW1-01\tOPEN\tR-1 と A-1。", "1\tW1-02\tdepends\tW1-01\tDOING\t式",
            "1\tW1\tstage\tW1-01\t残り 1\t-", "docs graph: W1-01 --back: 3 node(s) at depth ≤ 1 (2 typed, 1 text); 3 more at depth 2"])  # fmt: skip
        # a start with no file: one line, and on; a stage with no work
        self.assertEqual(self.run_("graph", "C-40", "--back"), (0, [
            "C-40: not found (a kind with no file: the history or the second phase)", "1\tS-1\ttext\tC-40\tDECIDED\t字句",
            "docs graph: C-40 --back: 1 node(s) at depth ≤ 1 (0 typed, 1 text); 5 more at depth 2"]))  # fmt: skip
        self.assertEqual(self.run_("graph", "M5"), (0, ["0\tM5\t-\t-\t-\t-", "docs graph: M5: 0 node(s) at depth ≤ 1 (0 typed, 0 text); 0 more at depth 2"]))
        # the errors of the use (exit 2)
        for argv, why in ((("S-2", "--depth", "0"), "--depth 0: not 1 to 5"), (("S-2", "--depth", "6"), "--depth 6: not 1 to 5"),
                          (("x",), "x: not an ID or a stage of tasks/stages.md"), (("W7",), "W7: not an ID or a stage of tasks/stages.md")):  # fmt: skip
            self.assertEqual(self.run_("graph", *argv), (2, [f"docs.py graph: {why}"]), argv)
        self.assertEqual(docs_tool.GRAPH_DEPTH_MAX, 5)
        self.assertIn(f"--depth N (1 to {docs_tool.GRAPH_DEPTH_MAX})", docs_tool.__doc__)
        # an ID field with no direction stops it
        row = "| `found_by` | 文字列 | — | いいえ | 見つけた票 |\n"
        self.edit("decisions/README.md", row, row + "| `see` | ID の並び（S） | — | いいえ | 見る |\n")
        self.assertEqual(self.run_("graph", "S-2"), (2, ["docs.py graph: no direction in docs.RESTS_ON for the ID field(s) `see` of decisions/README.md"]))

    # ------------------------------------------------ show, list, changes, ticket

    def test_show(self):
        self.layout()
        self.write("tests/pending.toml", entry("spec-example", "§2.1 0123abcd: x", reasons=("S-2", "R-1")) + entry("gate", "g", reasons=("S-1",)))
        code, out = self.run_("show", "S-2")
        self.assertEqual((code, out), (0, [
            "== decisions/S/S-2.md", *NEW_LAYOUT["decisions/S/S-2.md"].splitlines()[:6], "== relations",
            "tasks\tW1-02\tDOING\t式\t-", "tasks\tPH2\t-\t-\t-", "issue\tR-1\tOPEN\t候補\t-",
            "pending\tspec-example\t§2.1 0123abcd: x\tuntil W3-07", "== body", "- 空白: R-1 と A-1。"]))  # fmt: skip
        self.assertEqual(self.run_("show", "W1-02", "--relations")[1][-4:], [
            "== relations", "decision\tS-2\tOPEN\tR-1 と A-1。\t-", "fixes\tR-1\tOPEN\t候補\t-", "waiting\tS-2\tOPEN\tR-1 と A-1。\t-"])  # fmt: skip
        self.assertEqual(self.run_("show", "W1-01")[1][-3:], ["== relations", "decision\tS-1\tDECIDED\t字句\t§2.1", "depended_by\tW1-02\tDOING\t式\t-"])
        self.assertEqual(self.run_("show", "R-1")[1][-3:], ["== relations", "fix\tW1-02\tDOING\t式\t-", "decisions\tS-2\tOPEN\tR-1 と A-1。\t-"])
        # a work waits for a decision due before it, too
        self.edit("decisions/S/S-2.md", 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W1-01"')
        self.assertEqual(self.run_("show", "W1-01")[1][-1], "waiting\tS-2\tOPEN\tR-1 と A-1。\t-")
        self.write("tests/pending.toml", "x = 1\n")
        self.assertEqual(self.run_("show", "S-2", "--relations")[1][-1], "pending\ttests/pending.toml: 1 error(s); `pending.py` shows them")
        self.assertEqual(self.run_("show", "S-9"), (1, ["S-9: not found (decisions/S/)"]))
        self.assertEqual(self.run_("show", "D-1"), (2, ["docs.py show: D: not in the new layout (no decisions/D/)"]))
        self.assertEqual(self.run_("show", "C-1")[0], 2)

    def test_list(self):
        self.layout()
        s1, s2 = "S-1\tDECIDED\ttasks=W1-01 spec=§2.1\t字句", "S-2\tOPEN\ttasks=W1-02,PH2\tR-1 と A-1。"
        self.assertEqual(self.run_("list", "S"), (0, [s1, s2, "docs list: 2 of 2 S"]))
        self.assertEqual(self.run_("list", "S", "--status", "OPEN"), (0, [s2, "docs list: 1 of 2 S"]))
        self.assertEqual(self.run_("list", "S", "--count"), (0, ["S\tOPEN 1, DECIDED 1 (2)", "docs list: 2 of 2 S"]))
        self.assertEqual(self.run_("list", "W", "--count"), (0, ["W1\tDOING 1, DONE 1 (2)", "docs list: 2 of 2 W"]))
        # X-2 U7c: the stages in the order of the table, then the ones not in it
        for rel in ("tasks/W/W2-01.md", "tasks/W/W3-01.md", "tasks/W/W10-01.md"):
            self.write(rel, '+++\nstatus = "PLAN"\n+++\n# x\n')
        self.edit("tasks/stages.md", "| W1 | 基盤 |\n| W2 | 直し |\n", "| W2 | 直し |\n| W1 | 基盤 |\n")
        self.assertEqual(self.run_("list", "W", "--count"), (0, ["W2\tPLAN 1 (1)", "W1\tDOING 1, DONE 1 (2)", "W3\tPLAN 1 (1)",
                                                                  "W10\tPLAN 1 (1)", "docs list: 5 of 5 W"]))  # fmt: skip
        self.edit("tasks/stages.md", "| W2 | 直し |\n| W1 | 基盤 |\n", "| W1 | 基盤 |\n| W2 | 直し |\n")
        for rel in ("tasks/W/W2-01.md", "tasks/W/W3-01.md", "tasks/W/W10-01.md"):
            (self.root / rel).unlink()
        w2 = "W1-02\tDOING\tsize=M depends=W1-01 doing=U2/i\t式"
        self.assertEqual(self.run_("list", "W", "--waiting"), (0, [w2, "docs list: 1 of 2 W"]))
        self.assertEqual(self.run_("list", "W", "--stage", "W2")[1], ["docs list: 0 of 2 W"])
        self.assertEqual(self.run_("list", "S", "--stage", "W1")[1][-1], "docs list: 2 of 2 S")
        self.assertEqual(self.run_("list", "R", "--no-fix")[1], ["docs list: 0 of 1 R"])
        self.assertEqual(self.run_("list", "R")[1][0], "R-1\tOPEN\tseverity=中 fix=W1-02 decisions=S-2\t候補")
        # `before` this work or an earlier one; the group
        self.edit("decisions/S/S-2.md", 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W1-02"\ngroup = 3')
        s2 = "S-2\tOPEN\ttasks=W1-02,PH2 before=W1-02 group=3\tR-1 と A-1。"
        for before, rows in (("W1-02", [s2]), ("W2-01", [s2]), ("W1-01", [])):
            self.assertEqual(self.run_("list", "S", "--before", before)[1][:-1], rows, before)
        self.assertEqual(self.run_("list", "S", "--group", "3")[1], [s2, "docs list: 1 of 2 S"])
        # the title of an S with none: the head of its 空白
        self.edit("decisions/S/S-2.md", "- 空白: R-1 と A-1。", "- 空白: " + "あ" * 50)
        self.assertEqual(self.run_("list", "S", "--status", "OPEN")[1][0].split("\t")[-1], "あ" * 40)
        for argv, error in ((("S", "--waiting"), "--waiting is for W, not S"), (("W", "--group", "1"), "--group is for S, D"),
                            (("S", "--status", "DONE"), "--status DONE: not one of OPEN / DECIDED / DROPPED"),
                            (("S", "--stage", "4"), "4: not a stage"), (("S", "--before", "S-1"), "--before S-1: not a work or a stage"),
                            (("S", "--before", "PH2"), "--before PH2: not a work or a stage"), (("W", "--stage", "PH2"), "PH2: not a stage of tasks/stages.md (W1, W2, M5, M9)"),
                            (("R", "--stage", "PH2"), "PH2: not a stage of tasks/stages.md (W1, W2, M5, M9)"), (("S", "--stage", "W3"), "W3: not a stage of tasks/stages.md (W1, W2, M5, M9), or PH2"),
                            (("D",), "D: not in the new layout"), (("Z",), "Z: not an ID or a kind of S, D")):  # fmt: skip
            code, out = self.run_("list", *argv)
            self.assertEqual(code, 2, argv)
            self.assertIn(error, out[-1])

    def test_the_stage_of_a_work_and_the_order_of_the_stages(self):
        # RF-18 (A), (C2): the one place that reads a stage out of a work's ID, and the one order of the stages
        works = ("W3-05", "W10-1", "W3", "M5-1", "T5-8", "W3-", "W3-x", "PH2", "S-1", None, 3)
        self.assertEqual([repo.split_work(x) for x in works], [("W3", 5), ("W10", 1)] + [None] * 9)
        order = ("W2", "W1", "M5", "PH2", "M7", "W3", "W10", "?", "x")
        self.assertEqual(sorted(reversed(order), key=lambda s: repo.stage_key(s, ("W2", "W1", "M5"))), list(order))
        # two names of one number are two keys: the order does not follow the input's
        for names in (["W11", "W011"], ["W011", "W11"]):
            self.assertEqual(sorted(names, key=lambda s: repo.stage_key(s, ())), ["W011", "W11"])

    def test_the_statuses_of_the_heads(self):
        # RF-18 (C1): `Index.statuses` reads the `status` of the heads once; `work_done` is read from it
        self.layout()
        self.write("decisions/S/S-3.md", "+++\ngroup = 1\n+++\n# S-3 t\n")
        index = docs_tool.Index.of(self.root)
        self.assertEqual(index.statuses("S"), {"S-1": "DECIDED", "S-2": "OPEN", "S-3": None})
        self.assertEqual(index.work_done(), {w: s == "DONE" for w, s in index.statuses("W").items()})
        self.assertIn(True, index.work_done().values())
        with self.assertRaisesRegex(repo.RepoError, "no directory"):
            index.statuses("D")

    def test_the_order_of_before(self):
        # the stages in the order of the table (X-2 U6), an M stage after the W ones, PH2 after every stage
        stages = ("W1", "W2", "W10", "M5")
        order = ["W1-02", "W1-10", "W1-99", "W1", "W2-01", "W2", "W10-01", "W10", "M5", "PH2"]
        keys = [docs_tool.due_key(d, stages) for d in order]
        self.assertEqual(keys, sorted(keys))
        self.assertEqual(len(set(keys)), len(keys))
        self.assertLess(docs_tool.due_key("W2", ("W2", "W1")), docs_tool.due_key("W1-01", ("W2", "W1")))
        for other in ("S-1", "T1-1", "X4", "W3", "W3-01", "M5-1", "W", "W1-", None, 3):
            self.assertIsNone(docs_tool.due_key(other, stages), other)

    def test_list_by_the_stage_and_before(self):
        self.layout()
        for n, due in ((3, "W1"), (4, "W2-01"), (5, "PH2"), (6, "W2"), (7, "M5")):  # W2 and M5 have no work
            self.write(f"decisions/S/S-{n}.md", f'+++\nstatus = "OPEN"\nbefore = "{due}"\n+++\n# S-{n} t\n')
        self.edit("decisions/S/S-2.md", 'found_by = "W1-01/t"', 'found_by = "W1-01/t"\nbefore = "W1-02"')

        def ids(*argv):
            code, out = self.run_("list", "S", *argv)
            self.assertEqual(code, 0, argv)
            return [line.split("\t")[0] for line in out[:-1]]

        # `--before` a work: a stage is due at its end; PH2 is after every W
        for before, want in (("W1-01", []), ("W1-02", ["S-2"]), ("W1-99", ["S-2"]), ("W1", ["S-2", "S-3"]),
                             ("W2-01", ["S-2", "S-3", "S-4"]), ("W2", ["S-2", "S-3", "S-4", "S-6"]),
                             ("M5", ["S-2", "S-3", "S-4", "S-6", "S-7"]), ("M9", ["S-2", "S-3", "S-4", "S-6", "S-7"])):  # fmt: skip
            self.assertEqual(ids("--before", before), want, before)
        # `--stage`: `tasks` or `before` of the stage (a work of it, or the stage); PH2 for the decisions
        self.assertEqual(ids("--stage", "W1"), ["S-1", "S-2", "S-3"])
        self.assertEqual(ids("--stage", "W2"), ["S-4", "S-6"])
        self.assertEqual(ids("--stage", "PH2"), ["S-2", "S-5"])
        self.assertEqual(ids("--stage", "M5"), ["S-7"])
        self.assertEqual(ids("--stage", "M9"), [])
        self.assertEqual(self.run_("list", "S", "--before", "W3-01")[0], 2)  # its stage is not in the table
        self.assertEqual(self.run_("list", "S", "--stage", "PH2")[1][1], "S-5\tOPEN\tbefore=PH2\tt")
        # `--waiting`: a stage or PH2 in `before` makes no work wait; a work in `before` does
        w2 = "W1-02\tDOING\tsize=M depends=W1-01 doing=U2/i\t式"
        self.assertEqual(self.run_("list", "W", "--waiting")[1], [w2, "docs list: 1 of 2 W"])
        self.assertNotIn("waiting", " ".join(self.run_("show", "W1-01", "--relations")[1]))
        self.edit("decisions/S/S-3.md", 'before = "W1"', 'before = "W1-01"')
        self.assertEqual(self.run_("show", "W1-01", "--relations")[1][-1], "waiting\tS-3\tOPEN\tt\t-")

    def test_set_before(self):
        self.layout()
        s2 = "decisions/S/S-2.md"
        for due in ("W1", "PH2", "W1-02"):
            self.assertEqual(self.run_("set", "S-2", f"before={due}"), (0, [f'{s2}: before = "{due}"']), due)
            self.assertEqual(self.run_("check")[0], 0, due)
        self.assertRefused(("set", "S-2", "before=W99"), [f"{s2}:5: before: W99: not a stage of tasks/stages.md (W1, W2, M5, M9)"], [s2])
        self.assertRefused(("set", "S-2", "before=x4"), ['`before` has "x4", not an ID of W、段、PH2'], [s2])
        # a work that is not there is refused too (the head fields, (b))
        self.assertRefused(("set", "S-2", "before=W1-09"), [f"{s2}:5: before: W1-09 is not found (tasks/W/)"], [s2])
        self.assertRefused(("set", "S-2", "tasks=W1-02,W1-09"), [f"{s2}:3: tasks: W1-09 is not found (tasks/W/)"], [s2])
        # the text is not looked at: a broken reference there does not stop a write of the head fields
        self.edit(s2, "R-1 と A-1。", "R-1 と A-9。")
        self.assertEqual(self.run_("set", "S-2", "before=W1")[0], 0)

    def test_changes(self):
        self.layout()
        self.write("decisions/S/S-3.md", '+++\nstatus = "DECIDED"\nspec = ["§3.1"]\ndecided = 2026-10-16\n+++\n# S-3 群\n')
        s1, s3 = "S-1\t2026-10-15\t§2.1\t字句", "S-3\t2026-10-16\t§3.1\t群"
        note = "note: A-1 is DECIDED with no `decided`"
        self.assertEqual(self.run_("changes"), (0, [s3, s1, note, "docs changes: 2 decision(s); 1 DECIDED with no `decided`"]))
        self.assertEqual(self.run_("changes", "--since", "2026-10-16")[1][:2], [s3, note])
        self.assertEqual(self.run_("changes", "--section", "§2")[1][:1], [s1])
        self.assertEqual(self.run_("changes", "--section", "§3.1")[1][:1], [s3])
        self.assertEqual(self.run_("changes", "--stage", "W1")[1], [s1, "docs changes: 1 decision(s); 0 DECIDED with no `decided`"])
        self.assertEqual(self.run_("changes", "--section", "3")[0], 2)
        with self.assertRaises(SystemExit):  # argparse: a date
            self.run_("changes", "--since", "16 Oct")

    def test_ticket(self):
        self.layout()
        self.edit("decisions/S/S-2.md", 'status = "OPEN"', 'status = "OPEN"\nspec = ["§3.1", "§2.2"]')
        self.edit("issues/R/R-1.md", 'aspect = 1', 'aspect = 1\nspec = ["§3.1", "tools.md §1"]')
        self.write("tasks/W/W1-02.md", self.read("tasks/W/W1-02.md") + "\n- 持ち越し:\n  - W1-01/b の報告: x\n")
        fields = [f"- {f}: {g}".rstrip() for f, g in docs_tool.TICKET_FIELDS]
        expected = [
            "# 作業 W1-02 U2/i: 式", "", "- 作業のファイル: tasks/W/W1-02.md（`docs.py show W1-02`）", "- 状態: DOING（doing: U2/i）",
            "- 規模: M", "- 依存: W1-01（DONE）", "- 実現する決定（1 件）:", "  - S-2 OPEN R-1 と A-1。（§3.1, §2.2）",
            "- 直す R:", "  - R-1 OPEN 候補（§3.1, tools.md §1）", "- 仕様の節: §2.2、§3.1、tools.md §1",
            "- 持ち越し: 作業のファイルの `持ち越し` を読む", "- ぶつかりうる事例: なし", "- 役割と単位: U2/i",
            *fields,
        ]  # fmt: skip
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i"), (0, expected))
        self.assertEqual([fields[1], fields[2].split(": <")[0]], ["- しない:", "- 後の単位の構造に頼る決定"])
        out = self.root / "t.md"
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i", "--out", str(out)), (0, [str(out)]))
        self.assertEqual(out.read_text(encoding="utf-8"), "\n".join(expected) + "\n")
        self.assertRefused(("ticket", "W1-02", "U2/b", "--out", str(out)), [f"{out}: there already"], ["t.md"])
        self.assertEqual(self.run_("ticket", "W1-01", "U1/t")[1][4:8], ["- 規模: -", "- 依存: なし", "- 実現する決定（1 件）:", "  - S-1 DECIDED 字句（§2.1）"])
        self.assertEqual(self.run_("ticket", "W1-01", "U1/i-fix1")[1][-len(docs_tool.TICKET_FIELDS) - 1:],
                         ["- 役割と単位: U1/i-fix1", *fields])  # fmt: skip
        self.edit("decisions/S/S-1.md", 'tasks = ["W1-01"]\n', "")
        self.assertEqual(self.run_("ticket", "W1-01", "U1/t")[1][6:7], ["- 実現する決定: なし"])
        self.assertEqual(self.run_("ticket", "W1-02", "U2")[0], 2)
        self.assertEqual(self.run_("ticket", "S-1", "U2/i")[0], 2)
        self.assertEqual(self.run_("ticket", "W1-09", "U2/i"), (1, ["W1-09: not found (tasks/W/)"]))

    def test_ticket_cases_and_handover(self):
        """X9-67 b, d: the lines of `tests/` that name an ID of the ticket as a word, at most CASES_SHOWN per ID;
        the fields of a handover with their guides."""
        self.layout()
        self.write("tests/spec/a.onsa", "// SPEC-GAP(S-2): x\nS-20 と S-200 と R-10\n")
        self.write("tests/pending.toml", '[[item]]\nreasons = ["R-1"]\n')
        self.write("tests/many.onsa", "R-1\n" * 7)
        (self.root / "tests/b.bin").write_bytes(b"S-2\0")  # not text
        (self.root / "tests/c.onsa").write_bytes("S-2 \udcff".encode("utf-8", "surrogatepass"))  # not UTF-8
        shown = "、".join(f"tests/many.onsa:{n}" for n in range(1, 6))
        cases = ["- ぶつかりうる事例:", "  - S-2: tests/spec/a.onsa:1", f"  - R-1: {shown} ほか 3 件"]
        out = self.run_("ticket", "W1-02", "U2/i")[1]
        self.assertEqual(out[12:15], cases)
        self.assertEqual(out[15], "- 役割と単位: U2/i")
        handover = self.run_("ticket", "W1-02", "U2/i-handover")[1]
        self.assertEqual(handover[: len(out)], [out[0].replace("U2/i", "U2/i-handover"), *out[1:15], "- 役割と単位: U2/i-handover", *out[16:]])
        self.assertEqual(handover[len(out) :], [f"- {f}: {g}" for f, g in docs_tool.HANDOVER_FIELDS])
        self.assertEqual([x.split(":")[0] for x in handover[len(out) :]], [
            "- 読む順", "- 状態の基", "- 道具", "- 前の gate の要約と知られた失敗", "- 古くなった注記とぶつかる事例",
            "- 戻す事例と保留の事例", "- 引き継ぎの記録"])  # fmt: skip
        self.assertIn("`work.py sync --apply <パッチ>`", handover[len(out) + 1])
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i-fix2-handover")[1][len(out) :], handover[len(out) :])
        for unit in ("U2/i-handover-fix1", "U2/x-handover", "U2/i-hand"):
            self.assertEqual(self.run_("ticket", "W1-02", unit)[0], 2, unit)
        shutil.rmtree(self.root / "tests")  # not "なし" when there is nothing to read
        self.assertEqual(self.run_("ticket", "W1-02", "U2/i"), (2, ["docs.py ticket: tests/: no directory (the lines of the cases)"]))

    def test_stale(self):
        """X-21 P-2: the lines of the `持ち越し` of the works not DONE (`--all`: every work) that name a DECIDED S beside
        決める, or a DONE R beside 決める or 直す, with no mark of a thing done on the line, on the next line of its
        item, or at the head of its item or an item above it; past forms and compounds are not the verbs."""
        self.layout()
        self.write("issues/R/R-2.md", '+++\nstatus = "DONE"\n+++\n# R-2 済んだ\n')
        carried = [
            "- 内容: S-1 を決める（節の外）。",
            "- 持ち越し:",
            "  - **U2 の終わり（2026-10-28）:** S-1 を U3 の前に決める。",
            "    S-2 を決める。R-1 を直す。",  # OPEN
            "    R-2 は U2 の直しで直す。（済み: U2、`728ebb7`）",
            "    U3b へ: S-1 を決める。",
            "    （済み: U3b、`0eb4575`。事例は x）",  # the line before it, broken by `fmt`
            "    R-2 を見直す。S-1 は決めた。R-2 を直した。S-1 の取り決め。",
            "    S-1 を直す。",  # a decided S may wait to be put in
            "  - （済み: U3a2、`4c9d682`）R-2 の判断が二か所にあり、直す。",
            "    S-1 も決める。",
            "    - S-1 の残りを決める。",
            "  - U3a2（済み、`4c9d682`）: R-2 を直す。",
            "  - **U4 から（`x` は済み: U5a）:** R-2 を直す。",
            "  - R-2 を直さない。S-1 の前に決める（済みでない）。",  # not the shape of a mark: `済み` before `:、）`
            "",
            "    R-2 を決めれば。",
            "- 結果: S-1 を決める（節の外）。",
        ]  # fmt: skip
        self.write("tasks/W/W1-02.md", self.read("tasks/W/W1-02.md") + "\n".join(carried) + "\n")
        self.edit("tasks/W/W1-01.md", "# W1-01 gate\n", "# W1-01 gate\n- 持ち越し: S-1 を決める。\n")
        at = {x.strip(): n for n, x in enumerate(self.read("tasks/W/W1-02.md").split("\n"), 1)}
        rows = [f"{ids}\ttasks/W/W1-02.md:{at[x]}\t{x}" for ids, x in (
            ("S-1 DECIDED", "- **U2 の終わり（2026-10-28）:** S-1 を U3 の前に決める。"),
            ("R-2 DONE, S-1 DECIDED", "- R-2 を直さない。S-1 の前に決める（済みでない）。"),
            ("R-2 DONE", "R-2 を決めれば。"))]  # fmt: skip
        self.assertEqual(self.run_("stale"), (0, [*rows, "docs stale: 3 line(s) in the `持ち越し` of 1 work(s)"]))
        self.assertEqual(self.run_("stale", "--all"), (0, [
            "S-1 DECIDED\ttasks/W/W1-01.md:6\t- 持ち越し: S-1 を決める。", *rows,
            "docs stale: 4 line(s) in the `持ち越し` of 2 work(s) (DONE too)"]))  # fmt: skip
        # The four places the 81st check of the documents found by hand in the `持ち越し` of W4-05, with their marks
        # (`target/notes/81/handback/onsa-docs-ad1740d45a6d9e4bf-001.md`, 5): taken out, the one that says 決める is
        # found; the three others name no verb of STALE (`U3b へ:`, `事例で守る`, `U3 で扱う`).
        for id_, status in (("S-137", "DECIDED"), ("S-140", "DECIDED"), ("S-748", "DECIDED"), ("R-320", "DONE")):
            self.write(repo.path_of(id_).as_posix(), f'+++\nstatus = "{status}"\n+++\n# {id_} x\n')
        marks = ["（済み: U3b、`0eb4575`。`rule` の文は `c84ec93`）", "（済み: U3a、`86d463a`）",
                 "（済み: 第 72 組、`4474022`。`A.N` の辺は U3a、`86d463a`）"]  # fmt: skip
        w405 = "\n".join([
            '+++\nstatus = "PLAN"\n+++\n# W1-03 型\n',
            "- 持ち越し:",
            "  - **U3a の終わり（2026-10-29、80 回目、`86d463a`）:** S-748・S-752 を入れた。",
            "    U3b へ: S-137（対象の型引数）、S-140（`impl Copy for`・`impl Dup for` は §4.6 で E0020）、"
            f"R-320（タプルなどの対象の E0307）。{marks[0]}",
            "    総称の別名の E0307 の候補（`type AR = R[F32]` の `impl AR`）は今は出ないが、元の名前 `R[F32]` を候補にすると"
            " S-137 の E0307 になる。U3b で候補を出さないことを事例で守る。",
            "    （済み: U3b、`0eb4575`。事例は `tests/spec/module/impl_on_alias_of_generic_without_candidate.onsa`）",
            "  - **U2 から（2026-10-28、79 回目）:** U2/i は +486 −83（見積もり 200 の 2.43 倍）で止まった。",
            "    E0307 の `impl` のメンバを型の位置から読む形に、U2 から E0302 が足された。S-748 と一緒に U3 で扱う。"
            f"{marks[1]}",
            "    U3 へ: 別名を頭にした `A.N` は計算した長さの E0200 のまま。"
            f"S-748（E0307 の `impl` のメンバを E0304 の相手に数えるか）を U3 の前に決める。{marks[2]}",
        ]) + "\n"  # fmt: skip
        self.write("tasks/W/W1-03.md", w405)
        self.assertEqual(self.run_("stale")[1][3:], ["docs stale: 3 line(s) in the `持ち越し` of 2 work(s)"])
        bare = "\n".join(x for x in w405.split("\n") if not x.strip().startswith("（済み"))
        for m in marks:
            bare = bare.replace(m, "")
        self.write("tasks/W/W1-03.md", bare)
        found = "S-748（E0307 の `impl` のメンバを E0304 の相手に数えるか）を U3 の前に決める。"
        n = next(n for n, x in enumerate(bare.split("\n"), 1) if x.endswith(found))
        self.assertEqual(self.run_("stale")[1][3:], [
            f"S-748 DECIDED\ttasks/W/W1-03.md:{n}\tU3 へ: 別名を頭にした `A.N` は計算した長さの E0200 のまま。{found}",
            "docs stale: 4 line(s) in the `持ち越し` of 2 work(s)"])  # fmt: skip
        shutil.rmtree(self.root / "tasks")
        self.assertEqual(self.run_("stale")[0], 2)  # no W: not the new layout

    def test_depends_a_stage(self):
        """U5e: a stage in `depends` is every work of it: `ticket` shows its state, `show` the works that
        depend on the stage of a work as `depended_by` too."""
        self.layout()
        self.write("tasks/W/W2-01.md", '+++\nstatus = "PLAN"\ndepends = ["W1", "W1-02"]\n+++\n# W2-01 後\n')
        self.write("tasks/W/W2-02.md", '+++\nstatus = "PLAN"\ndepends = ["W2"]\n+++\n# W2-02 後の後\n')
        self.assertEqual(self.run_("check")[0], 0)
        self.assertEqual(self.run_("ticket", "W2-01", "U1/i")[1][5], "- 依存: W1（残り 1）、W1-02（DOING）")
        self.assertEqual(self.run_("ticket", "W2-02", "U1/i")[1][5], "- 依存: W2（残り 2）")
        self.edit("tasks/W/W1-02.md", 'status = "DOING"', 'status = "DONE"')
        self.edit("tasks/W/W1-02.md", 'doing = ["U2/i"]\n', "")
        self.assertEqual(self.run_("ticket", "W2-01", "U1/i")[1][5], "- 依存: W1（DONE）、W1-02（DONE）")
        # once each, in order; a work is not its own (W2-02 names its stage W2)
        self.assertEqual(self.run_("show", "W1-01", "--relations")[1][-2:], ["depended_by\tW1-02\tDONE\t式\t-", "depended_by\tW2-01\tPLAN\t後\t-"])
        self.assertEqual(self.run_("show", "W1-02", "--relations")[1][-2:-1], ["depended_by\tW2-01\tPLAN\t後\t-"])
        self.assertEqual(self.run_("show", "W2-01", "--relations")[1][-1:], ["depended_by\tW2-02\tPLAN\t後の後\t-"])
        self.assertEqual(self.run_("show", "W2-02", "--relations")[1][-1:], ["== relations"])
        # a stage of no work (check (b) finds it)
        self.edit("tasks/W/W2-02.md", '["W2"]', '["W3"]')
        self.assertEqual(self.run_("ticket", "W2-02", "U1/i")[1][5], "- 依存: W3（-）")

    def test_the_commands_need_the_directory_of_the_kind(self):
        self.layout()
        shutil.rmtree(self.root / "decisions" / "S")
        for argv in (("show", "S-1"), ("list", "S"), ("set", "S-1", "status=OPEN"), ("note", "S-1", "補い", "x"), ("new", "S"),
                     ("draft", "S-1", "--group", "1")):  # fmt: skip
            code, out = self.run_(*argv)
            self.assertEqual((code, out[-1]), (2, f"docs.py {argv[0]}: S: not in the new layout (no decisions/S/)"), argv)

    # ------------------------------------------------ set, note, new, draft

    def test_set(self):
        self.layout()
        w2 = "tasks/W/W1-02.md"
        self.assertEqual(self.run_("set", "W1-02", "size=L", "doing="), (0, [f'{w2}: size = "L"; doing removed']))
        self.assertEqual(self.read(w2), '+++\nstatus = "DOING"\nsize = "L"\ndepends = ["W1-01"]\nmarks = ["基盤"]\n+++\n# W1-02 式\n')
        self.assertEqual(self.run_("set", "W1-02", "doing=U2/i, U2/b")[1], [f'{w2}: doing = ["U2/i", "U2/b"]'])
        self.assertEqual(self.run_("set", "S-1", "decided=2026-10-17", "group=4")[0], 0)
        self.assertIn("group = 4\ndecided = 2026-10-17\n+++", self.read("decisions/S/S-1.md"))
        # the values do not fit the field table
        self.assertRefused(("set", "W1-02", "size=XL", "marks=基盤,,メモ", "color=red", "size=M", "depends=S-1"), [
            '`size` has "XL", not one of S / M / L', "`marks` has an empty item: 基盤,,メモ",
            "`color` is not a field of tasks/W/README.md (status, size, depends, marks, doing, commit)", "`size` is given twice",
            '`depends` has "S-1", not an ID of W、段'], [w2])  # fmt: skip
        self.assertRefused(("set", "S-1", "decided=17 Oct"), ['`decided` has "17 Oct", not a date'], ["decisions/S/S-1.md"])
        # after the write, the file or a partner breaks a relation, or a required field is gone
        self.assertRefused(("set", "W1-02", "status=DONE"), [
            "issues/R/R-1.md:2: OPEN, but every work of `fix` is DONE (W1-02)",
            "tasks/W/W1-02.md:6: `doing` on a work that is DONE, not DOING"], [w2, "issues/R/R-1.md"])  # fmt: skip
        self.assertRefused(("set", "W1-02", "status=DONE", "doing="), ["issues/R/R-1.md:2: OPEN, but every work of `fix` is DONE (W1-02)"], [w2])
        self.assertRefused(("set", "W1-02", "status=", "doing="), ["tasks/W/W1-02.md:1: the field `status` is required (tasks/W/README.md)"], [w2])
        # in order, both are written
        self.assertEqual(self.run_("set", "R-1", "status=DONE")[0], 0)
        self.assertEqual(self.run_("set", "W1-02", "status=DONE", "doing=")[0], 0)
        self.assertEqual(self.run_("check")[0], 0)
        # a file open in vim; not an ID's file; not KEY=VALUE
        self.write("tasks/W/.W1-02.md.swp", "")
        self.assertRefused(("set", "W1-02", "size=S"), [f"{w2}: the swap file .W1-02.md.swp (open in vim?)"], [w2])
        self.assertEqual(self.run_("set", "W1-09", "size=S"), (1, ["W1-09: not found (tasks/W/)"]))
        self.assertEqual(self.run_("set", "W1-01", "size")[0], 2)

    def test_note(self):
        self.layout()
        r1 = "issues/R/R-1.md"
        self.assertEqual(self.run_("note", "R-1", "判断", "直す。"), (0, [f"{r1}: - 判断（2026-10-16、親）: 直す。"]))
        self.assertEqual(self.run_("note", "R-1", "判断", "直さない。", "--by", "利用者")[0], 0)
        self.assertEqual(self.read(r1), NEW_LAYOUT[r1] + "- 判断（2026-10-16、親）: 直す。\n- 判断（2026-10-16、利用者）: 直さない。\n")
        self.write("decisions/A/A-1.md", NEW_LAYOUT["decisions/A/A-1.md"].rstrip("\n"))
        self.assertEqual(self.run_("note", "A-1", "補い", "x")[0], 0)
        self.assertEqual(self.read("decisions/A/A-1.md"), NEW_LAYOUT["decisions/A/A-1.md"] + "- 補い（2026-10-16、親）: x\n")
        self.assertRefused(("note", "R-1", "判断", "a\nb"), ["the label, the text and the writer are each one line, not empty"], [r1])
        self.assertRefused(("note", "R-1", "", "x"), ["the label, the text and the writer are each one line, not empty"], [r1])
        self.write("issues/R/.R-1.md.swo", "")
        self.assertRefused(("note", "R-1", "判断", "x"), [f"{r1}: the swap file .R-1.md.swo (open in vim?)"], [r1])
        self.assertEqual(self.run_("note", "R-9", "判断", "x"), (1, ["R-9: not found (issues/R/)"]))

    def test_new(self):
        self.layout()
        # the next number counts the drafts (S-2.draft.md); the head fields in the normal form
        self.assertEqual(self.run_("new", "S", "--title", "新しい", "tasks=W1-02", "spec=§3.1"), (0, [
            "decisions/S/S-3.md", "== the other S of §3.1 (or under) or of the family -: 0"]))  # fmt: skip
        self.assertEqual(self.read("decisions/S/S-3.md"), '+++\nstatus = "OPEN"\nspec = ["§3.1"]\ntasks = ["W1-02"]\n+++\n# S-3 新しい\n')
        self.write("decisions/S/S-7.draft.md", "")
        # the labels of the body from the README
        self.edit("decisions/README.md", "# 決定\n", "# 決定\n\n## 本文のラベル\n\n- `空白`: 論点\n- `決定`: 決めたこと\n  - 字下げは読まない\n")
        self.assertEqual(self.run_("new", "S")[1], ["decisions/S/S-8.md"])
        self.assertEqual(self.read("decisions/S/S-8.md"), '+++\nstatus = "OPEN"\n+++\n# S-8\n\n- 空白:\n- 決定:\n')
        self.assertEqual(self.run_("new", "W", "--stage", "W1", "--title", "次")[1], ["tasks/W/W1-03.md"])
        self.assertEqual(self.read("tasks/W/W1-03.md"), '+++\nstatus = "PLAN"\n+++\n# W1-03 次\n')
        # X-2 U7c: a stage not in the table of the stages is refused; so is a work of `depends` that is not there
        self.assertEqual(self.run_("new", "W", "--stage", "W12"), (2, ["docs.py new: W12: not a stage of tasks/stages.md (W1, W2, M5, M9)"]))
        self.assertRefused(("new", "W", "--stage", "W1", "depends=W1-09"), ["tasks/W/W1-04.md:3: depends: W1-09 is not found (tasks/W/)"])
        self.assertFalse(any((self.root / "tasks/W").glob("W12-*")) or (self.root / "tasks/W/W1-04.md").exists())
        self.assertEqual(self.run_("check")[0], 0)
        # nothing is written: a field required, a value, a relation, the title, a swap file
        self.edit("issues/R/README.md", "高 / 中 / 低 | いいえ", "高 / 中 / 低 | はい")
        self.assertRefused(("new", "R"), ["the field `severity` is required (issues/R/README.md)"])
        self.assertRefused(("new", "S", "status=MAYBE"), ['`status` has "MAYBE", not one of OPEN / DECIDED / DROPPED'])
        self.assertRefused(("new", "S", "tasks=W1-01"), ["decisions/S/S-9.md:2: OPEN, but every work of `tasks` is DONE (W1-01)"])
        self.assertRefused(("new", "S", "--title", "a\nb"), ["the title is one line, not empty"])
        self.write("decisions/S/.S-9.md.swp", "")
        self.assertRefused(("new", "S"), ["decisions/S/S-9.md: the swap file .S-9.md.swp (open in vim?)"])
        self.assertFalse((self.root / "decisions/S/S-9.md").exists() or (self.root / "issues/R/R-2.md").exists())
        self.assertEqual(self.run_("new", "R", "severity=中")[1], ["issues/R/R-2.md"])
        # usage: the stage of W; in a git worktree, the parent gives the numbers
        for argv in (("new", "W"), ("new", "S", "--stage", "W1"), ("new", "W", "--stage", "4")):
            self.assertEqual(self.run_(*argv)[0], 2, argv)
        with mock.patch.object(repo, "tree_kind", return_value="worktree"):
            self.assertEqual(self.run_("new", "S"), (2, ["docs.py new: the numbers are given in the main tree only "
                                                         "(this is a git worktree; write NEW)"]))  # fmt: skip

    def test_new_shows_the_akin(self):
        """X9-12: `new S` with `spec` or `family` lists the other S of a section of it or one under it, or of the
        family, and tells when the family has another OPEN S and no S `族: <family>`; it writes all the same."""
        self.layout()
        self.edit("decisions/README.md", "| `group` |", "| `family` | 文字列 | — | いいえ | 族 |\n| `group` |")
        self.write("decisions/S/S-3.md", '+++\nstatus = "OPEN"\nspec = ["§2.2", "§3.1"]\nfamily = "行頭"\n+++\n# S-3 三\n')
        self.write("decisions/S/S-4.md", '+++\nstatus = "OPEN"\nspec = ["§3"]\n+++\n# S-4 四\n')
        head = "== the other S of {} (or under) or of the family {}: {}"
        self.assertEqual(self.run_("new", "S", "spec=§2"), (0, [
            "decisions/S/S-5.md", head.format("§2", "-", 2), "S-1\tDECIDED\t§2.1\t字句\tspec", "S-3\tOPEN\t§2.2, §3.1\t三\tspec"]))  # fmt: skip
        note = "note: the family 行頭 has 1 more OPEN S and no S `族: 行頭`; register it (rules/process.md 8.6, the flow of the gaps, 2)"
        self.assertEqual(self.run_("new", "S", "spec=§2.1", "family=行頭")[1], [
            "decisions/S/S-6.md", head.format("§2.1", "行頭", 2), "S-1\tDECIDED\t§2.1\t字句\tspec", "S-3\tOPEN\t§2.2, §3.1\t三\tfamily", note])  # fmt: skip
        self.assertTrue((self.root / "decisions/S/S-6.md").exists())
        self.assertEqual(self.run_("new", "S", "family=他")[1], ["decisions/S/S-7.md", head.format("-", "他", 0)])
        # the S of the family: the new one, or one there
        self.assertEqual(self.run_("new", "S", "--title", "族: 行頭", "family=行頭")[1][-1], "S-6\tOPEN\t§2.1\t-\tfamily")
        self.assertEqual(self.run_("new", "S", "family=行頭")[1][-1], "S-8\tOPEN\t-\t族: 行頭\tfamily")
        self.assertEqual(self.run_("new", "S", "spec=§3.1", "--title", "x")[1], [
            "decisions/S/S-10.md", head.format("§3.1", "-", 1), "S-3\tOPEN\t§2.2, §3.1\t三\tspec"])  # fmt: skip
        self.assertEqual(self.run_("new", "S", "tasks=W1-02")[1], ["decisions/S/S-11.md"])
        self.assertEqual(self.run_("new", "R", "spec=§2")[1], ["issues/R/R-2.md"])

    def test_draft(self):
        self.layout()
        self.assertEqual(self.run_("draft", "S-1", "S-2", "--group", "3"), (0, [
            "decisions/S/S-2.draft.md: there already; not written", "decisions/S/S-1.draft.md"]))  # fmt: skip
        self.assertEqual(self.read("decisions/S/S-1.draft.md"), "+++\ngroup = 3\ndrafted = 2026-10-16\n+++\n# S-1 字句\n\n" +
                         "".join(f"- {label}:\n" for label in docs_tool.DRAFT_LABELS))  # fmt: skip
        self.assertEqual(self.read("decisions/S/S-2.draft.md"), NEW_LAYOUT["decisions/S/S-2.draft.md"])
        self.write("decisions/S/S-3.md", '+++\nstatus = "OPEN"\n+++\n# S-3\n')
        self.write("decisions/S/S-4.md", '+++\nstatus = "OPEN"\n+++\n# S-4\n')
        self.assertRefused(("draft", "S-3", "S-9", "--group", "4"), ["S-9: not found (decisions/S/)"])
        self.write("decisions/S/.S-4.draft.md.swp", "")
        self.assertRefused(("draft", "S-3", "S-4", "--group", "4"), ["decisions/S/S-4.draft.md: the swap file .S-4.draft.md.swp (open in vim?)"])
        self.assertFalse((self.root / "decisions/S/S-3.draft.md").exists())
        self.assertEqual(self.run_("draft", "S-3", "--group", "4"), (0, ["decisions/S/S-3.draft.md"]))
        self.assertTrue(self.read("decisions/S/S-3.draft.md").endswith("+++\n# S-3\n\n- 決定済みで戻さないもの:\n" + "".join(f"- {x}:\n" for x in docs_tool.DRAFT_LABELS[1:])))
        self.assertEqual(self.run_("draft", "W1-01", "--group", "1")[0], 2)
        with self.assertRaises(SystemExit):  # argparse: --group is required
            self.run_("draft", "S-3")

    # ------------------------------------------------ blind, answers (X9-65, X9-66)

    DRAFT_HEAD = "+++\ngroup = {}\ndrafted = 2026-10-16\n+++\n"
    S3 = """\
# S-3 題

| ID | 論点 | 推奨 | 確度 |
|---|---|---|---|
| S-3 | a \\| b | (a) | 高 |

- **論点:** x
- **推奨と理由:** (a)。
  - あわせて決めること

    深い行
- **影響:** 推奨なら W1-02。
- 回答:

(a) で。

- 独立のレビュー: 一致
"""
    S4 = "# S-4\n\n- 推奨と理由: (b)\n- 回答（2026-10-16、利用者）: (b) で。\n  続き\n@centrevillage: (c) にする\n続きの行\n\n次の段落\n"

    def drafts(self):
        self.layout()
        for n, group, body in ((3, 5, self.S3), (4, 5, self.S4), (10, 5, "# S-10 十\n\n- 論点: y\n- 回答:\n"), (5, 6, "# S-5\n")):
            self.write(f"decisions/S/S-{n}.draft.md", self.DRAFT_HEAD.format(group) + body)

    def test_blind(self):
        self.drafts()
        out = self.root / "blind.md"
        self.assertEqual(set(docs_tool.BLIND_LABELS) - set(docs_tool.DRAFT_LABELS), set())
        code, lines = self.run_("blind", "--group", "5", "--out", str(out))
        self.assertEqual((code, lines), (0, [
            "decisions/S/S-3.draft.md:16: - **影響:** 推奨なら W1-02。",
            f"docs blind: {out}: 3 file(s), 6 item(s) and 2 column(s) left out; 1 kept line(s) with 推奨 or 確度 (above)"]))  # fmt: skip
        head = self.DRAFT_HEAD.format(5)
        self.assertEqual(out.read_text(encoding="utf-8"), "\n".join([
            head + "# S-3 題\n\n| ID | 論点 |\n| --- | --- |\n| S-3 | a \\| b |\n\n- **論点:** x\n- **影響:** 推奨なら W1-02。\n",
            head + "# S-4\n\n@centrevillage: (c) にする\n続きの行\n\n次の段落\n", head + "# S-10 十\n\n- 論点: y\n"]))  # fmt: skip
        # not over a file; FILE... (as given) in the order given
        self.assertRefused(("blind", "--group", "5", "--out", str(out)), [f"{out}: there already"], ["blind.md"])
        s4 = str(self.root / "decisions/S/S-4.draft.md")
        self.assertEqual(self.run_("blind", s4, "--out", str(b4 := self.root / "b4.md"))[1], [
            f"docs blind: {b4}: 1 file(s), 2 item(s) and 0 column(s) left out; 0 kept line(s) with 推奨 or 確度 (above)"])  # fmt: skip
        self.assertEqual(self.read("b4.md"), head + "# S-4\n\n@centrevillage: (c) にする\n続きの行\n\n次の段落\n")
        # one of the two, a group with drafts, `--out`
        for argv in (("blind", s4, "--group", "5", "--out", "x"), ("blind", "--out", "x"), ("blind", "--group", "7", "--out", "x")):
            self.assertEqual(self.run_(*argv)[0], 2, argv)
        with self.assertRaises(SystemExit):
            self.run_("blind", "--group", "5")

    def test_answers(self):
        self.drafts()
        self.assertEqual(self.run_("answers", "--group", "5"), (0, [
            "S-3\tdecisions/S/S-3.draft.md:17\t(a) で。",
            "S-4\tdecisions/S/S-4.draft.md:8\t(b) で。", "  続き",
            "S-4\tdecisions/S/S-4.draft.md:10\t(c) にする", "  続きの行",
            "S-10\tdecisions/S/S-10.draft.md:5\t回答なし",
            "docs answers: 2 item(s) with an answer, 1 with none (回答なし); 0 answer(s) under no item"]))  # fmt: skip
        # the items of a file of the history: `### <ID>`, `- **<ID>**`; an answer under no item
        gaps = self.write("gaps.md", "# 組\n\n### S-7（確認だけ） 七\n- 回答:\n### 付録\n- 回答: 外\n- **S-8** 八\n  回答: 了承\n"
                                     "- **S-9 の調べ:** x\n  - 回答:\n")  # fmt: skip
        self.assertEqual(self.run_("answers", str(gaps))[1], [
            f"S-7\t{gaps}:3\t回答なし", f"S-8\t{gaps}:8\t了承", f"-\t{gaps}:6\t外",
            "docs answers: 1 item(s) with an answer, 1 with none (回答なし); 1 answer(s) under no item"])  # fmt: skip

    # ------------------------------------------------ the old places are not read (X-2 DT-7, U7a)

    # What the old layout had, made to change the results if it were read: the tables of the IDs (S-9, T1-1,
    # W9-01, R-9, A-9), the codes, the spec of the tools, the foreign forms, a broken table, the spec file of
    # the root, and the history.
    BAIT = {
        "docs/implementation-tasks.md": "# plan\n## 2. S\n| ID | 項目 |\n|---|---|\n| S-9 | x |\n## 3. x\n## 4. 作業\n"
                                        "| ID | 作業 |\n|---|---|\n| T1-1 | t |\n## 5. 診断コード\n| コード | 内容 | 段 | M |\n"
                                        "|---|---|---|---|\n| E0700 | x | — | 第 2 期 |\n\n欠番: E0701。\n## 6. 例\n",
        "docs/rework-phase1.md": "## 3. 作業\n| ID | 作業 |\n|---|---|\n| W9-01 | x |\n## 4. 残り\n",
        "docs/review-impl-phase1.md": "## 8. 決定の記録\n| ID | 内容 |\n|---|---|\n| R-9 | x |\n",
        "docs/api-candidates.md": "| ID | 候補 |\n|---|---|\n| A-9 | x |\n",
        "docs/onsa-tools.md": "# tools\n\n## 1. graph\n\n```onsa\nprev~(x, 0.0)\n```\n\n## 2. old\n",
        "docs/foreign-forms.toml": '[[form]]\nid = "old"\n',
        "docs/x.md": "| a |\n| 1 | 2 |\nS-1\n",
        "onsa-lang-spec-0.3.md": "# s\n\n## 9. old\n\n```onsa\nprev~(x, 0)\n```\n",
        "history/h.md": "| a |\n| 1 | 2 |\nS-1\n",
    }

    def results(self):
        """What the tools read from the tree, and the files under it they opened."""
        opened, real = [], io.open

        def spy(file, *args, **kw):
            if isinstance(file, (str, os.PathLike)):
                opened.append(Path(file))
            return real(file, *args, **kw)

        with mock.patch("io.open", spy), mock.patch("builtins.open", spy):
            docs = pending.load_docs(self.root)
            inits = default_inits.sources(self.root)
            out = {
                "check": self.run_("check"),
                "load_docs": (docs.works, docs.done, docs.reasons, docs.sections, docs.stages, docs.works_at, docs.reasons_at),
                "api_ids": gap_marks.api_ids(self.root),
                "diag": repo.diag_text(self.root),
                "spec": (repo.spec_doc(self.root), repo.tools_doc(self.root)),
                "foreign": pending.foreign_form_ids(self.root),
                "inits": ([(s.shown, s.text, s.first) for s in inits[0]], inits[1:]),
                "path": self.run_("path", "S-1", "S-9", "T1-1", "W9-01", "R-9", "A-9", "§9", "§2.1", "tools.md §1", "tools.md §2"),
                "refs": [self.run_("refs", x) for x in ("S-1", "decisions/S/S-2.md")],
                "back": [self.run_("back", x) for x in ("S-1", "S-9", "T1-1")],
                "graph": [self.run_("graph", "S-1", "--back", "--depth", "2"), self.run_("graph", "S-9", "--back")],
            }
        root = self.root.resolve()
        rels = {p.resolve().relative_to(root) for p in opened if p.resolve().is_relative_to(root)}
        return out, sorted(r.as_posix() for r in rels if r.parts[0] in ("docs", "history") or len(r.parts) == 1 and r.suffix == ".md")

    def test_the_old_places_are_never_read(self):
        self.layout()
        self.write(repo.FOREIGN_FORMS, '[[form]]\nid = "a"\n')
        want, opened = self.results()
        check = "docs check: no problem in 19 document(s) (tables, heads, refs, relations, links, tools)"  # the .md of NEW_LAYOUT
        self.assertEqual(want["check"], (0, [check]))
        self.assertEqual((want["foreign"], want["path"][0]), ({"a"}, 1))  # S-9 and the others are not found
        self.assertIn("1\tW1-01\ttasks\tS-1\tDONE\tgate", want["graph"][0][1])
        self.assertEqual(want["graph"][1][1][-1], "docs graph: S-9 --back: 0 node(s) at depth ≤ 1 (0 typed, 0 text); 0 more at depth 2")
        self.assertEqual(opened, ["README.md"])  # the root's README is a document
        for rel, text in self.BAIT.items():
            self.write(rel, text)
        got, opened = self.results()
        self.assertEqual(got, want)
        self.assertEqual(opened, ["README.md"])
        # only `back --history` reads the history, when it is asked
        self.assertIn("history/h.md:3: S-1", self.run_("back", "S-1", "--history")[1])

    def test_no_tool_names_the_old_places(self):
        """The tools (not their self-tests) name no `docs/`, and name `history/` only to read it when it is asked
        (`back --history`) and to leave it out (`narrowing`). The comments are read too."""
        tools = Path(__file__).resolve().parent
        docs_dir = re.compile(r"""Path\(\s*["']docs["']\s*\)|["']docs/""")
        history_dir = re.compile(r"""["']history["'/]""")
        found_docs, found_history = [], []
        for p in sorted(tools.rglob("*.py")):
            if p.name.startswith("test_"):
                continue
            rel = p.relative_to(tools).as_posix()
            for i, line in enumerate(p.read_text(encoding="utf-8").split("\n"), 1):
                if docs_dir.search(line):
                    found_docs.append(f"{rel}:{i}")
                if history_dir.search(line):
                    found_history.append((rel, line.strip()))
        self.assertGreater(len(list(tools.rglob("*.py"))), 20)
        self.assertEqual(found_docs, [])
        self.assertEqual(found_history, [
            ("docs.py", 'files += sorted(p.relative_to(root) for p in (root / "history").rglob("*.md") if p.is_file())'),
            ("narrowing.py", 'EXCLUDED_FROM_CODES = ("tests/", "tools/", "rules/", "decisions/", "issues/", "tasks/", "history/")'),
        ])  # fmt: skip


class ToolHelp(unittest.TestCase):
    """The help by role (X9-7, X-9 U2): `repo.ROLES`, `repo.Command`, and `docs.py help [--role R] [COMMAND]`."""

    def help(self, *argv):
        code, lines = quiet_out(docs_tool.main, ["help", *argv])
        self.assertEqual(code, 0, lines)
        return lines

    def test_every_command_has_its_help(self):
        self.assertGreater(len(docs_tool.COMMANDS), 10)
        for name, c in docs_tool.COMMANDS.items():
            with self.subTest(name=name):
                self.assertIsInstance(c, repo.Command)
                for text in (c.purpose, c.when, c.example):
                    self.assertTrue(text.strip() and "\n" not in text, text)
                self.assertTrue(c.roles)
                self.assertEqual([r for r in c.roles if r not in repo.ROLES], [])
                self.assertRegex(c.example, rf"^docs\.py {re.escape(name)}( |$)")

    def test_roles_are_the_definitions(self):
        agents = Path(__file__).resolve().parent.parent / ".claude" / "agents"
        self.assertEqual(sorted(d for d in repo.ROLES.values() if d), sorted(p.stem for p in agents.glob("onsa-*.md")))
        self.assertEqual([r for r, d in repo.ROLES.items() if d is None], ["parent"])

    def test_help_by_role(self):
        names = list(docs_tool.COMMANDS)
        self.assertEqual([x.split()[0] for x in self.help() if x[:1].isalpha()][: len(names)], names)
        for role in repo.ROLES:
            with self.subTest(role=role):
                lines = self.help("--role", role)
                want = [n for n, c in docs_tool.COMMANDS.items() if role in c.roles]
                self.assertTrue(want)  # `show` is every role's
                self.assertEqual([x.split()[0] for x in lines if not x.startswith(" ")], want)
                self.assertEqual(sum(x.startswith("  時機: ") for x in lines), len(want))
                self.assertEqual([x.split(maxsplit=2)[1] for x in lines if x.startswith("  例:")], ["docs.py"] * len(want))

    def test_help_of_a_command(self):
        for name, c in docs_tool.COMMANDS.items():
            with self.subTest(name=name):
                text = "\n".join(self.help(name))
                for part in (c.purpose, c.when, " ".join(c.roles), c.example, f"usage: docs.py {name}"):
                    self.assertIn(part, text)
        self.assertIn("--relations  the head fields and the relations, no body", "\n".join(self.help("show")))
        self.assertNotIn("使わない", "\n".join(self.help("--role", "i", "show")))
        self.assertIn("  （役割 b はこの命令を使わない）", self.help("--role", "b", "ticket"))

    def test_unknown_role_or_command(self):
        for argv in (["--role", "impl"], ["nosuch"], ["--role", "i", "nosuch"], ["--role", "x", "show"]):
            with self.subTest(argv=argv), self.assertRaises(SystemExit) as e:
                quiet_out(docs_tool.main, ["help", *argv])
            self.assertEqual(e.exception.code, 2)


if __name__ == "__main__":
    unittest.main(verbosity=1)
