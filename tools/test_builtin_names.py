#!/usr/bin/env python3
"""Self-tests of tools/builtin_names.py (tools/selftest.py runs every self-test).

Alone: python3 -B tools/test_builtin_names.py
"""
import io
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import builtin_names  # noqa: E402
import repo  # noqa: E402
from selftest_support import json_cmd, split_spec  # noqa: E402


BUILTIN_BASELINES = dict(builtin_names.BASELINES)

NAMES_SPEC = """\
# Spec
## 2. 字句
### 2.2 キーワード（全て）

```
fn let match
use trait impl
```

`prev` `delay`（組込みの遅延の flow）と `sample_rate` は、flow の中で予約された組込み名（§11.4）。キーワードは `std.test` で使える。

## 4. 型
### 4.1 組込み型

| 分類 | 型 | 種 |
|---|---|---|
| 整数 | `I8 U32` | Copy |
| 標準 enum | `Option[T]`, `Result[T, E]` | 中身 |
| 関数 | `fn(A) -> R uses {E}` | Copy |

### 4.2 文字列
`Str` is not in the table.

## 6. 関数
### 6.3 trait
- 演算子 trait: `Add Neg`。
- 標準 trait: `PartialEq`, `Iter[T]`。

### 6.5 属性（全て）

`@repr(c)`、`@param(...)`（§11.7）。これ以外の属性は無い（`@deprecated` は必要になったら定義する）。

## 11. flow
### 11.3 レート

| クロック | 意味 |
|---|---|
| （定数） | `const` |
| `init` | 初期化時 |
| `sample` | サンプルごと |

- レートを型の形で書く（`x: Sig[F32]`、0.3 の草案の形）と E0020。`Sig` / `Ctl` は普通の名前で、`struct Sig[T]` を宣言してよい。

### 11.6 生成される API

`flow voice(...)` を宣言すると、コンパイラは名前空間 `voice` に次を生成する。

```onsa
voice.State        // 状態。voice.Hidden は書いていない
fn voice.init(cfg: voice.Config, sample_rate: F32) -> voice.State
```

- 引数の名前は `s`、`params` に固定する。利用者の `x` とは衝突しない。

## 12. メモリ
### 12.4 配置
- 容量の確認: ヘッダの `SIZE` / `BULK_SIZE` で分かる。`fast_budget` を書くと E0820。

## 8. 効果
### 8.1 宣言と使用
- 標準の効果（`Fs` `Random`）は std の `effect` 宣言で、`use` で取り込む。`Alloc` だけは prelude にある。

## 15. モジュール
### 15.1 モジュール
- 暗黙の prelude は、`Option Some None panic Alloc`、種の制約 `Copy` と `Dup`、組込み型だけである。
"""


class BuiltinNames(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        # NAMES_SPEC is a small spec: the baselines are for the real one (test_baselines)
        patcher = mock.patch.object(builtin_names, "BASELINES", {})
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_baselines(self):
        # N2: a place that stops giving a name of its baseline fails
        real = repo.spec_text(repo.ROOT)
        baselines = {
            "attributes (§6.5)": {"repr", "fp", "param", "mem"},
            "clocks (§11.3)": {"init", "block", "sample"},
            "generated API (§11.6, §12.4)": {"State", "process", "SIZE"},
        }
        self.assertTrue(builtin_names.builtin_names(real, [], baselines=baselines))
        for old, new, needle in (
            ("、`@mem(...)`（§12.4）、`@export`", "、`@export`", "attributes (§6.5) no longer gives mem"),
            ("| `sample` | サンプルごとの値 |", "| `samples` | サンプルごとの値 |", "clocks (§11.3) no longer gives sample"),
            ("rt fn voice.process(inout", "rt fn voice.run(inout", "no longer gives process"),
            ("ヘッダの `SIZE` / `ALIGN`", "ヘッダの `ALIGN`", "no longer gives SIZE"),
        ):
            with self.subTest(old=old):
                self.assertIn(old, real)
                with self.assertRaisesRegex(builtin_names.CheckError, re.escape(needle)):
                    builtin_names.builtin_names(real.replace(old, new, 1), [], baselines=baselines)

    def test_a_bar_in_a_code_span_does_not_divide_a_cell(self):
        # X-2 U7c: the columns of the tables of the spec are read by repo.table_cells
        row = "| 関数 | `fn(A) -> R uses {E}` | Copy |"
        self.assertIn(row, NAMES_SPEC)
        types = builtin_names.builtin_types(NAMES_SPEC.replace(row, "| `a | b` | `Pipe` | Copy |"))
        self.assertIn("Pipe", types)

    def test_real_baselines_hold(self):
        # the baselines of the module hold for the spec of the repository
        with mock.patch.object(builtin_names, "BASELINES", BUILTIN_BASELINES):
            builtin_names.builtin_names(repo.spec_text(repo.ROOT), [])

    def test_build_outputs_only_are_skipped(self):
        # N1: a `target` directory that is not a build output is scanned
        self.write("crates/x/Cargo.toml", "")
        self.write("crates/x/src/target/mod.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        self.write("crates/x/target/debug/build.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        found = builtin_names.scan(self.root, {"zeroed"})
        self.assertEqual(found, {"crates/x/src/target/mod.rs": {"zeroed": 1}})

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")

    def test_names_from_the_spec(self):
        names = builtin_names.builtin_names(NAMES_SPEC, ["sqrt", "std", "T"])
        expected = {
            "prev", "delay", "sample_rate",  # §2.2, first sentence only (not `std`, `test`)
            "I8", "U32", "Option", "Result",  # §4.1 type column (not `T`, `R`, `fn`)
            "Add", "Neg", "PartialEq", "Iter",  # §6.3
            "Fs", "Random",  # §8.1, inside the parentheses only (not `Alloc` of the next sentence)
            "Some", "None", "panic", "Alloc", "Copy", "Dup",  # §15.1
            "sqrt", "std",  # std
            "repr", "param",  # §6.5, the first sentence (not `deprecated`)
            "init", "sample",  # §11.3, the clocks of the table (not `const`)
            "Sig", "Ctl",  # §11.3, the old rate types (not `F32`, `x`)
            "State", "Config", "cfg", "sample_rate", "params",  # §11.6 (not the comment's `Hidden`, nor `s`, `x`)
            "SIZE", "BULK_SIZE",  # §12.4, the first sentence (not `fast_budget`)
        }  # fmt: skip
        self.assertEqual(names, expected)
        self.assertEqual(builtin_names.keywords(NAMES_SPEC), {"fn", "let", "match", "use", "trait", "impl"})

    def test_a_missing_place_fails(self):
        for old, needle in (
            ("- 暗黙の prelude は", "the prelude"),
            ("- 標準 trait:", "標準 trait"),
            ("標準の効果（", "standard effects"),
            ("予約された組込み名", "reserved builtin names"),
            ("### 4.1 組込み型", "§4.1"),
            ("0.3 の草案の形", "old rate types"),
            ("引数の名前は", "fixed argument names"),
            ("`flow voice(...)`", "example `flow"),
            ("- 容量の確認:", "sizes of the state"),
            ("`@repr(c)`、`@param(...)`", "no attribute"),
            ("| `init` | 初期化時 |\n| `sample` | サンプルごと |", "no clock"),
        ):
            with self.subTest(old=old):
                with self.assertRaisesRegex(builtin_names.CheckError, re.escape(needle)):
                    builtin_names.builtin_names(NAMES_SPEC.replace(old, "x"), [])

    def test_scan_rust(self):
        src = (
            'let a = "zeroed"; // "in a comment"\n'
            '/* "block /* nested */ comment" */ let b = r#"raw "x""#;\n'
            "let c = '\"'; let d = 'x'; fn f<'a>(x: &'a str) {}\n"
            'let e = "esc \\" quote"; let g = b"bytes";\n'
            'let h = "multi\nline"; let i = "after";\n'
        )
        literals, masked = builtin_names.scan_rust(src)
        self.assertEqual([(ln, t) for _, ln, t in literals], [
            (1, "zeroed"), (2, 'raw "x"'), (4, 'esc \\" quote'), (4, "bytes"), (5, "multi\nline"), (6, "after"),
        ])  # fmt: skip
        self.assertEqual(len(masked), len(src))
        self.assertEqual(masked.count("\n"), src.count("\n"))
        self.assertNotIn("comment", masked)

    def test_uses(self):
        names = {"zeroed", "narrow_u8", "trunc_u8_sat", "Option"}
        src = """\
fn f(n: &str) -> bool {
    if n == "zeroed" { return true }
    match n { "Option" | "other" => true, _ => false };
    n.starts_with("narrow_") || n.ends_with("_sat") || n == format!("narrow_{}", k).as_str()
        || n.starts_with("zz") || n == format!("{}f", 1) || n == "Option is a type"
}

#[cfg(test)]
mod tests {
    fn g() { let x = "zeroed"; let y = { "Option" }; }
}

fn after() { "Option"; }
"""
        found = builtin_names.uses_in(src, names)
        self.assertEqual(found, {"zeroed": 1, "Option": 2, "narrow_": 1, "_sat": 1, "narrow_{}": 1})

    def test_parts_of_names(self):
        # M2: the calls that take a part of a name, also inside an array
        names = {"narrow_u8", "trunc_u8_sat", "is_none"}
        src = """\
fn f(n: &str) -> bool {
    n.contains("none") || n.contains("narrow") || n.trim_start_matches("trunc_").is_empty()
        || n.trim_end_matches("_sat").is_empty() || n.starts_with(["narrow_", "zz"]) || n.ends_with(&["_u8_sat"])
        || n.contains("is_none") || n.contains("x") || n.contains("other") || f("narrow_")
}
"""
        found = builtin_names.uses_in(src, names)
        self.assertEqual(
            found,
            {"none": 1, "narrow": 1, "trunc_": 1, "_sat": 1, "narrow_": 1, "_u8_sat": 1, "is_none": 1},
        )

    def test_test_files(self):
        for rel, is_test in (
            ("crates/a/tests/x.rs", True),
            ("crates/a/src/tests.rs", True),
            ("crates/a/src/flow_tests.rs", True),
            ("crates/a/src/contests.rs", False),
            ("crates/a/src/lib.rs", False),
        ):
            self.assertEqual(builtin_names.is_test_file(rel), is_test, rel)

    def run_main(self, args=(), members=()):
        split_spec(NAMES_SPEC, self.root)
        out = io.StringIO()
        cmd = json_cmd({"--std-names": ["zeroed"], "--builtin-members": list(members)})
        with mock.patch("sys.stdout", out):
            code = builtin_names.main(["--root", str(self.root), *args], cmd=cmd)
        return code, out.getvalue()

    def test_members_of_sema_are_names(self):
        # the builtin methods of sema's table (`--builtin-members`) are builtin names
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "checked_add" || n.starts_with("narrow_") }\n')
        self.write(builtin_names.ALLOW, "")
        code, out = self.run_main(members=["checked_add", "narrow_u8"])
        self.assertEqual(code, 1)
        self.assertIn('"checked_add" is written 1 time(s), the list allows 0', out)
        self.assertIn('"narrow_" is written 1 time(s)', out)
        self.assertEqual(self.run_main()[0], 0)  # without them, nothing is found

    def test_same_spelling(self):
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "min" }\n')
        listed = '[allow."crates/a/src/lib.rs"]\n"zeroed" = 1\n\n[same_spelling."crates/a/src/lib.rs"]\n"min" = { count = 1, note = "@param のキー" }\n'
        self.write(builtin_names.ALLOW, listed)
        self.assertEqual(self.run_main(members=["min"])[0], 0)
        # --print keeps the same_spelling entries and their notes
        self.assertEqual(self.run_main(["--print"], members=["min"]), (0, listed))
        # both tables count: one more fails, asking for the place or a note
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "min" || n == "min" }\n')
        code, out = self.run_main(members=["min"])
        self.assertEqual(code, 1)
        self.assertIn('"min" is written 2 time(s), the list allows 1', out)
        self.assertIn("[same_spelling]", out)
        # one fewer asks to lower the count
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" }\n')
        code, out = self.run_main(members=["min"])
        self.assertEqual(code, 1)
        self.assertIn('"min" is written 0 time(s), the list allows 1; lower the count', out)
        # an entry needs a count and a note
        for bad in ('"min" = 1', '"min" = { count = 1 }', '"min" = { count = 1, note = " " }', '"min" = { count = 0, note = "x" }'):
            with self.subTest(bad=bad):
                self.write(builtin_names.ALLOW, f'[same_spelling."crates/a/src/lib.rs"]\n{bad}\n')
                code, out = self.run_main(members=["min"])
                self.assertEqual(code, 1)
                self.assertIn("cannot check", out)

    def test_main(self):
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" }\n')
        self.write("crates/a/tests/t.rs", 'fn t() { "zeroed"; }\n')
        self.write("crates/onsa_diag/src/codes.rs", 'fn t() { "zeroed"; }\n')  # the registry
        allow = '[allow."crates/a/src/lib.rs"]\n"Option" = 2\n"zeroed" = 1\n'
        self.write(builtin_names.ALLOW, allow)
        code, out = self.run_main()
        self.assertEqual(code, 0, out)
        # the list prints itself
        code, out = self.run_main(["--print"])
        self.assertEqual((code, out), (0, allow))
        # one more literal fails
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" || n == "None" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn('"None" is written 1 time(s), the list allows 0', out)
        # one fewer fails too, asking to lower the list
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn('"Option" is written 1 time(s), the list allows 2; lower the count', out)
        # a file of the list that is gone
        self.write(builtin_names.ALLOW, allow + '[allow."crates/gone.rs"]\n"zeroed" = 1\n')
        self.write("crates/a/src/lib.rs", 'fn f(n: &str) -> bool { n == "zeroed" || n == "Option" || n == "Option" }\n')
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("`crates/gone.rs` is not a file", out)
        # a malformed list
        for bad in ('[other]\nx = 1\n', '[allow."crates/a/src/lib.rs"]\n"zeroed" = 0\n', "[allow\n"):
            with self.subTest(bad=bad):
                self.write(builtin_names.ALLOW, bad)
                code, out = self.run_main()
                self.assertEqual(code, 1)
                self.assertIn("cannot check", out)

    def test_repository_list_is_sorted_and_positive(self):
        lists, notes = builtin_names.load_allow(builtin_names.ROOT / builtin_names.ALLOW)
        for table in builtin_names.TABLES:
            files = lists[table]
            self.assertEqual(list(files), sorted(files), table)
            for names in files.values():
                self.assertEqual(list(names), sorted(names), table)
        # every same_spelling entry says its meaning
        self.assertEqual(len(notes), sum(len(n) for n in lists["same_spelling"].values()))


if __name__ == "__main__":
    unittest.main(verbosity=1)
