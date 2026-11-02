#!/usr/bin/env python3
"""Self-tests of tools/narrowing.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_narrowing.py
"""
import argparse
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import narrowing  # noqa: E402
from selftest_support import quiet, git_in  # noqa: E402


class Narrowing(unittest.TestCase):
    """tools/narrowing.py (X-1): the seeds of a narrowed run, the shards, the base binaries."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve() / "main"  # git names /private/var
        self.root.mkdir()
        git_in(self.root, "init", "-q")
        for rel, text in {"tests/spec/a/x.onsa": "// E0013\n", "tests/spec/a/y.onsa": "y\n",
                          "crates/c.rs": "// E0001\nfn c() {}\n", "rules/d.md": "d\n"}.items():
            self.write(rel, text)
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "base")
        git_in(self.root, "branch", "dev")
        self.full = git_in(self.root, "rev-parse", "HEAD").strip()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def change(self):
        """A WIP commit and changes on top of dev: what a worktree holds."""
        self.write("crates/c2.rs", "// E0007\n")
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "WIP")
        self.write("crates/c.rs", "// E0002\nfn c() {}\n")  # E0001 removed, E0002 added
        self.write("rules/d.md", "E0003\n")  # the documents and tests/ name no code
        self.write("tests/spec/a/y.onsa", "y // E0004\n")
        self.write("tests/spec/b/é.onsa", "// E0006\n")  # untracked, a name outside ASCII
        self.write("crates/new.rs", "// E0005\n")  # untracked: its codes count
        self.write("tools/test_t.py", "E0008\n")  # tools/: the self-tests write codes as data (X-1 U2)
        (self.root / "crates/blob.bin").write_bytes(b"\xff\xfe")  # untracked, not text: no code

    def test_changed_paths_and_codes(self):
        self.change()
        self.assertEqual(narrowing.merge_base(self.root), self.full)
        self.assertEqual(narrowing.changed_paths(self.root, self.full),
                         {"crates/c2.rs", "crates/c.rs", "rules/d.md", "tests/spec/a/y.onsa", "tests/spec/b/é.onsa",
                          "crates/new.rs", "crates/blob.bin", "tools/test_t.py"})
        self.assertEqual(narrowing.diff_codes(self.root, self.full), {"E0001", "E0002", "E0005", "E0007"})
        git_in(self.root, "add", "-A")
        git_in(self.root, "commit", "-qm", "tracked")
        self.write("tools/test_t.py", "E0009\n")  # a tracked file of tools/: still no code
        self.assertEqual(narrowing.diff_codes(self.root, self.full), {"E0001", "E0002", "E0005", "E0007"})
        with self.assertRaises(narrowing.NarrowError):
            narrowing.changed_paths(self.root, "no-such-commit")

    def test_pick(self):
        self.change()
        self.write("crates/c.rs", "// E0002 E0005 E0007\n")
        seeds = ([("tests/spec/a/y.onsa", "E0002"), ("tests/spec/b/é.onsa", "")]
                 + [(f"tests/spec/c/{i}.onsa", "E0002" if i < 5 else "E0005" if i < 6 else "E0007 E0005")
                    for i in range(8)]
                 + [(f"tests/spec/fmt/{i}.onsa", "") for i in range(3)])
        # the codes with the fewest seeds first: E0007 (2), E0005 (3 with E0007's), then E0002 (5 more,
        # 8 in all) would pass the cap 6: the rest of the cap (3) comes from its seeds by a hash (X-1 U7;
        # y.onsa is in the diff)
        sel = narrowing.Selection(changed_since=self.full, code_cap=6)
        picked = narrowing.pick(seeds, sel, self.root, always=("tests/spec/fmt",))
        self.assertEqual(picked.counts, {"diff": 2, "codes": 6, "always": 3})
        self.assertEqual(picked.note, "codes cut to the cap 6 by hash: E0002 (3 of 5)")
        self.assertEqual(picked.describe(len(seeds)), "11 of 13 seeds (diff 2, codes 6, always 3; "
                                                       "codes cut to the cap 6 by hash: E0002 (3 of 5))")
        # the cap holds them all: no note
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=8), self.root)
        self.assertEqual((picked.counts, picked.note), ({"diff": 2, "codes": 8}, ""))
        # the cap holds none: the codes left out are named, none taken
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=0), self.root)
        self.assertEqual(picked.counts, {"diff": 2, "codes": 0})
        self.assertEqual(picked.note, "codes cut to the cap 0 by hash: E0002 (0 of 5), E0005 (0 of 3), E0007 (0 of 2)")
        # a sample is added after the rest
        picked = narrowing.pick(seeds, narrowing.Selection(changed_since=self.full, code_cap=0, sample=1.0,
                                                           salt="s"), self.root)
        self.assertEqual((picked.counts, len(picked.paths)), ({"diff": 2, "codes": 0, "sample": 11}, 13))

    def test_pick_fills_the_cap_by_a_hash_of_its_own(self):
        """The seeds of a code over the cap fill it (X-1 U7): the same salt takes the same, not the sample's."""
        self.change()
        seeds = [(f"tests/spec/c/{i}.onsa", "E0002") for i in range(100)]

        def cut(salt, order=seeds):
            sel = narrowing.Selection(changed_since=self.full, code_cap=20, salt=salt)
            return narrowing.pick(order, sel, self.root)

        picked = cut("W4-01")
        self.assertEqual((picked.counts, picked.note), ({"diff": 0, "codes": 20},
                                                        "codes cut to the cap 20 by hash: E0002 (20 of 100)"))
        self.assertEqual(picked.paths, cut("W4-01", list(reversed(seeds))).paths)  # the same salt: the same
        self.assertNotEqual(picked.paths, cut("W4-02").paths)
        self.assertEqual(len(cut(None).paths), 20)  # no salt (no --sample): still one choice
        self.assertEqual(cut(None).paths, cut(None).paths)
        # not the 20 the sample's hash puts first: they would overlap the sample
        paths = [p for p, _ in seeds]
        first = sorted(paths, key=lambda p: narrowing._hash(f"W4-01|{p}"))[:20]
        self.assertLess(len(picked.paths & set(first)), 10)
        self.assertNotEqual(picked.paths, narrowing.sampled(paths, 0.2, "W4-01"))

    def test_sample(self):
        paths = [f"tests/spec/{d}/{i}.onsa" for d in ("a", "b", "c") for i in range(200)] + ["tests/spec/d/x/1.onsa",
                                                                                            "tests/spec/d/y/2.onsa"]
        a = narrowing.sampled(paths, 0.1, "W4-01")
        self.assertEqual(a, narrowing.sampled(list(reversed(paths)), 0.1, "W4-01"))  # the same salt: the same
        self.assertNotEqual(a, narrowing.sampled(paths, 0.1, "W4-02"))
        self.assertTrue(40 < len(a) < 90, len(a))
        # at least one of each group (the first 3 parts of the directory): tests/spec/d/x and /y are one group
        self.assertEqual(narrowing.group("tests/spec/d/x/1.onsa"), "tests/spec/d")
        few = narrowing.sampled(paths, 1e-9, "W4-01")
        self.assertEqual(sorted(narrowing.group(p) for p in few), [f"tests/spec/{d}" for d in "abcd"])
        self.assertEqual(narrowing.sampled(paths, 1.0, "x"), set(paths))

    def test_shards_partition_the_whole(self):
        paths = [f"tests/spec/{i}.onsa" for i in range(300)]
        for k in (1, 2, 3):
            parts = [{p for p in paths if narrowing.in_shard(p, (i, k))} for i in range(k)]
            self.assertEqual(set().union(*parts), set(paths))
            self.assertEqual(sum(map(len, parts)), len(paths))
            self.assertTrue(all(parts), parts)
        picked = narrowing.pick([(p, "") for p in paths], narrowing.Selection(shard=(1, 3)), None,
                                always=("tests",))  # a shard has no directory always in
        self.assertEqual(picked.paths, {p for p in paths if narrowing.in_shard(p, (1, 3))})

    def make_base(self, commit=None, tools=("onsa", "onsa_cases")):
        d = self.root / "target" / "base" / self.full[:7]
        d.mkdir(parents=True, exist_ok=True)
        if commit is not None:
            (d / "COMMIT").write_text(commit + "\n")
        for t in tools:
            (d / t).write_text("#!/bin/sh\nexit 0\n")
            (d / t).chmod(0o755)
        return d

    def test_resolve_base(self):
        self.assertIsNone(narrowing.resolve_base(self.root, "none"))
        self.assertIn("same as HEAD", narrowing.resolve_base(self.root, "auto"))  # no code before it (X-1 U6)
        self.assertIn(f"no {self.root / 'target' / 'base' / self.full[:7] / 'COMMIT'}",  # HEAD's own (X-1 U6b)
                      narrowing.resolve_base(self.root, "auto", narrowed=True))
        self.write("crates/c.rs", "fn c() { 1 }\n")
        self.assertIn("COMMIT", narrowing.resolve_base(self.root, "auto"))
        d = self.make_base(self.full)
        self.change()
        base = narrowing.resolve_base(self.root, "auto")
        self.assertEqual(base, narrowing.Base(self.full[:7], (str(d / "onsa"),), (str(d / "onsa_cases"),)))
        # a short COMMIT of 7 characters or more is a prefix of the merge base
        self.make_base(self.full[:7])
        self.assertIsInstance(narrowing.resolve_base(self.root, "auto"), narrowing.Base)
        for wrong in (self.full[:6], "0" * 40):
            self.make_base(wrong)
            self.assertIn("not the merge base", narrowing.resolve_base(self.root, "auto"))
        self.make_base(self.full)
        (d / "onsa_cases").unlink()
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), f"no {d / 'onsa_cases'}")
        self.make_base(self.full)
        (d / "onsa").chmod(0o644)
        self.assertEqual(narrowing.resolve_base(self.root, "auto"), f"no {d / 'onsa'}")
        (d / "onsa").chmod(0o755)
        # a directory named: its two tools, named by COMMIT
        self.assertEqual(narrowing.resolve_base(self.root, str(d)).commit, self.full[:7])
        # from a worktree: the main tree's target/base
        wt = Path(self.tmp.name) / "wt"
        git_in(self.root, "worktree", "add", "-q", "-b", "work", str(wt))
        self.assertEqual(narrowing.resolve_base(wt, "auto"), base)
        # no dev: unknown; not a git work tree: unknown
        git_in(self.root, "branch", "-D", "dev")
        self.assertIn("no merge base of HEAD and dev", narrowing.resolve_base(self.root, "auto"))
        self.assertIn("no merge base", narrowing.resolve_base(Path(self.tmp.name), "auto"))

    def test_selection(self):
        def parse(*argv):
            ap = argparse.ArgumentParser()
            ap.add_argument("--root", type=Path, default=self.root)
            narrowing.add_arguments(ap)
            return quiet(narrowing.parse, ap, list(argv))[1]

        self.assertIsNone(parse())
        self.assertEqual(parse("--changed-since", "auto"), narrowing.Selection(changed_since=self.full))
        self.assertEqual(parse("--changed-since", "HEAD", "--code-cap", "5", "--sample", "0.5", "--salt", "s"),
                         narrowing.Selection(self.full, 5, 0.5, "s"))
        self.assertTrue(parse("--sample", "0.5", "--salt", "s").narrowed)
        self.assertFalse(parse("--shard", "0/2").narrowed)
        for bad in (["--changed-since", "nope"], ["--code-cap", "-1", "--changed-since", "auto"]):
            with self.subTest(bad=bad), self.assertRaises(SystemExit) as e:
                parse(*bad)
            self.assertEqual(e.exception.code, 2)


if __name__ == "__main__":
    unittest.main(verbosity=1)
