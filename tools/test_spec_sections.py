#!/usr/bin/env python3
"""Self-tests of tools/spec_sections.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_spec_sections.py
"""
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import spec_blocks  # noqa: E402
import spec_sections  # noqa: E402
from selftest_support import split_spec  # noqa: E402


class SpecSections(unittest.TestCase):
    SPEC = "## 1. A\n### 1.1 B\n```onsa\n## 9.9 not a heading\n```\n#### 1.1.2 C\n### 1.2 D\n## 2. E\n"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        split_spec(self.SPEC, self.root)

    def tearDown(self):
        self.tmp.cleanup()

    def cases(self, *specs):
        return [{"path": f"tests/{i}.onsa", "spec": list(s)} for i, s in enumerate(specs)]

    def test_headings_skip_fences(self):
        self.assertEqual(spec_blocks.headings(self.SPEC), ["1", "1.1", "1.1.2", "1.2", "2"])

    def test_unknown_and_untested(self):
        heads = spec_blocks.headings(self.SPEC)
        cases = self.cases(["§1.1.2"], ["§9.9", "§2"])
        self.assertEqual(spec_sections.unknown(cases, heads), [("tests/1.onsa", "§9.9")])
        # a section is tested through a subsection
        self.assertEqual(spec_sections.untested(cases, heads), ["1.2"])
        # a case that does not run tests nothing, but its names are still checked
        cases = [{"path": "tests/n.onsa", "mode": "none", "spec": ["§1.2", "§9.9"]}]
        self.assertEqual(spec_sections.untested(cases, heads), heads)
        self.assertEqual(spec_sections.unknown(cases, heads), [("tests/n.onsa", "§9.9")])

    def test_sections_in_the_strings_of_the_compiler(self):
        heads = spec_blocks.headings(self.SPEC)
        src = 'let m = "a rule (§1.1, §9.9)";\n// §8.8 is a comment, not a message\nlet n = "§2";\n'
        self.assertEqual(spec_sections.unknown_refs([("a.rs", src)], heads), [("a.rs:1", "9.9")])
        (self.root / "crates" / "c" / "src").mkdir(parents=True)
        (self.root / "crates" / "c" / "src" / "lib.rs").write_text(
            'fn f() { g("§7.7") }\n#[cfg(test)]\nmod tests { const X: &str = "§6.6"; }\n', encoding="utf-8")
        (self.root / "crates" / "c" / "src" / "x_tests.rs").write_text('const Y: &str = "§5.5";\n', encoding="utf-8")
        found = spec_sections.unknown_refs(spec_sections.compiler_sources(self.root), heads)
        self.assertEqual(found, [("crates/c/src/lib.rs:1", "7.7")], "unit tests are not messages")
        # A `#[cfg(test)] mod x;` declaration early in the file cuts nothing; a
        # string that goes on over lines is read whole; a char `'"'` and a `}`
        # in a string of a test module do not throw the reading off.
        (self.root / "crates" / "c" / "src" / "lib.rs").write_text(
            "#[cfg(test)]\nmod x_tests;\n"
            "fn f() -> char { '\"' }\n"
            'fn g() { h("a long message \\\n    that names §4.4.4 here") }\n'
            '#[cfg(test)]\nmod tests {\n    const Z: &str = "} §3.3.3";\n}\n'
            'fn k() { h(r#"raw §2.2.2"#) }\n',
            encoding="utf-8",
        )
        found = spec_sections.unknown_refs(spec_sections.compiler_sources(self.root), heads)
        self.assertEqual(found, [("crates/c/src/lib.rs:5", "4.4.4"), ("crates/c/src/lib.rs:10", "2.2.2")])

    def run_main(self, flag, cases):
        script = f"import json; print(json.dumps({cases!r}))"
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = spec_sections.main([flag], root=self.root, cmd=(sys.executable, "-B", "-c", script))
        return code, out.getvalue()

    def test_check_fails_on_unknown_sections_only(self):
        code, out = self.run_main("--check", self.cases(["§1.2"]))
        self.assertEqual(code, 0, out)
        code, out = self.run_main("--check", self.cases(["§3"]))
        self.assertEqual(code, 1)
        self.assertIn("names §3", out)

    def test_list_never_fails_on_untested(self):
        code, out = self.run_main("--list", self.cases([]))
        self.assertEqual(code, 0)
        self.assertIn("0 of 5 sections have a case", out)

    def test_a_failing_lister_fails(self):
        out = io.StringIO()
        with mock.patch("sys.stdout", out):
            code = spec_sections.main(["--list"], root=self.root, cmd=(sys.executable, "-B", "-c", "raise SystemExit(1)"))
        self.assertEqual(code, 1)
        self.assertIn("cannot list the cases", out.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=1)
