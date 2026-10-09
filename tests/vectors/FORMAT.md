# テストベクトルの形式（形式の版 1）

整数・浮動小数・変換・検査付き演算の、演算・型・入力・期待する結果か panic の表（計画 D-16 の 2、Q-02 (a)、R-133、W2-01）。規範は**このデータと仕様（§3.3、§3.4、§6.6、§11.4、§13.4）**で、生成のプログラム `tools/vectors/` の言語や処理系ではない。インタプリタ・C・WASM・JS は、この表と照らして仕様と合うことを確かめる。

## ファイル

| ファイル | 内容 |
|---|---|
| `int-<型>.tsv`（`i8` `i16` `i32` `i64` `u8` `u16` `u32` `u64`） | 整数の演算（§3.4 の整数の表、検査付き、シフト、`min` `max` `abs`）|
| `float-<型>.tsv`（`f32` `f64`） | 浮動小数の演算（§3.4 の浮動小数の表と `std.math` の正確な関数）|
| `conv-<型>.tsv`（10 の数の型） | 変換（§3.3 の表。`from_bits` は `conv-f32` / `conv-f64`）|
| `expr-f32.tsv`、`expr-f64.tsv` | 縮約と再結合をしない式（§3.4）、`vdelay~` の補間と添字（§11.4、S-194）|
| `const.tsv` | 組込み型の関連定数（§6.6。`F32.PI` `F64.PI` を含む、S-211）|
| `OPS.tsv` | 演算の登録簿 |
| `MANIFEST` | ファイルごとの SHA-256 と行数、乱数の種 |
| `XCHECK` | 独立した実装との突き合わせの記録 |
| `fixture/<パッケージ>/` | 演算ごとの `pub fn` を持つ Onsa のパッケージ（下の「fixture」）|

`FORMAT.md` と `XCHECK` 以外は `tools/vectors/gen.py` が生成する。手で編集しない。

## 行

LF で区切る ASCII の行。読み手は次の 3 種類だけを区別する。

- `#` で始まる行: 注釈（無視する。ファイルの先頭に、型の core 集合の凡例がある）。
- `@ <演算> <段>`: 節の始まり。以後の行は、次の節までこの演算の行。
- 行: `<引数> TAB <期待> [TAB <注釈>]`。引数は空白で区切る。引数が無いとき（定数）は `()`。注釈は、行の由来の印で、読み手は無視する: 仕様の決定に由来する行は `S-189`、`S-106` など、`held-*` の行は空白の番号 `S-207` など（複数は `,` で区切る）。

演算は `<型>.<名前>`（型は小文字）。名前は、メソッド・関数の名前（§3.3、§3.4 の表）、演算子を脱糖した trait の名前（`add sub mul div rem neg not and or xor shl shr wadd wsub wmul sadd ssub smul eq ne lt le gt ge`）、式の名前（`expr_muladd` `expr_mulsub` `expr_add3_l` `expr_add3_r` `expr_interp` `vdelay_k` `vdelay_f`）、定数（`MIN` など）。変換は `<元の型>.<書き方>`: `as_<型>`（同じ型への `as_<元の型>` を含む。値を変えない。§3.3、S-210）、`narrow_<型>`、`trunc_<型>`、`trunc_<型>_sat`、`round_f32` / `round_f64`、`to_bits`、`from_bits`（型は浮動小数）。型の組と書き方の一対一は `OPS.tsv` と `tools/vectors/ops.py` の `conv_forms` が §3.3 の表から導く。

**段**: `edge`（境界値の全組合せ）、`rand`（決まった種の乱数）、`held-<S 番号>`（下。期待を書かない）。

## 値

| 型 | 書き方 |
|---|---|
| 整数（`i8`〜`u64`、シフトの量 `u32`） | 10 進。符号は `-` だけ。先頭の 0 と `-0` は書かない。`u64` は `i64::MAX` を超える値も 10 進 |
| `f32` / `f64` | `0x` と全幅（`f32` は 8 桁、`f64` は 16 桁）の小文字の 16 進で、IEEE 754 のビット |
| `bool` | `true` / `false` |

浮動小数の引数は NaN の符号とペイロード、`-0.0`、非正規化数を含めて、ビットで書く。`[[test.host]]`（計画 D-05、W1-11）の TOML は `i64::MAX` を超える整数と NaN のペイロードを書けず、行数も桁違いなので、この形式は別のデータとして持つ。

## 期待

| 期待 | 意味 |
|---|---|
| 値 | 上の書き方。浮動小数の結果が NaN のときは `nan`（符号とペイロードは未規定、§3.4。どの NaN でもよい）。それ以外の浮動小数は、ビットが一致する（`-0.0` と `0.0` は別の値）|
| `panic:<種類>` | その演算は panic する。種類は仕様の表の「panic する場合」の欄の分類で人が読む情報: `overflow`（結果が型に収まらない、`-a` の `MIN`、`abs(MIN)`）、`div-zero`、`shift`（量がビット幅以上）、`range`（`trunc_<型>` の範囲外と無限大）、`nan`（`trunc_<型>` の NaN）。読み手が比べるのは panic するかだけ（panic の文面は仕様に無く、C の境界は状態の値 1 しか返さない、§9.2、§14.2）|
| `some:<値>` / `none` | `Option` を返す演算（`narrow_<型>`、`checked_*`）|
| `?` | 仕様の空白の行（`held-*` の段）。期待が無い。読み手は実行して、内部エラーや落下でないことだけを見る |

`to_bits` の結果と `from_bits` の結果: NaN の `to_bits` は正の quiet NaN（`0x7FC00000` / `0x7FF8000000000000`）を整数で書く（S-106）。`from_bits` の結果が NaN なら `nan`。

## 仕様の空白（`held-*`）

期待を決められない行は、段を `held-<S 番号>` にして、期待を `?` にする（計画 §8.5）。決定の後は、`tools/vectors/model.py` の該当の保留（`Ctx.hold`）を外して生成し直す。行はそのまま `edge` / `rand` の行になる。

今は保留の節が無い。S-207（結果が 0 のときの符号）、S-208（`abs(-0.0)` は `+0.0`）、S-209（有限の数 `%` 無限大は `a`）は 2026-10-08 に決まり、仕様 §3.4 に規則が書かれたので、W2-12 で保留を外した（外した行は 1376。`held-S207` が 1268、`held-S208` が 4、`held-S209` が 104）。この三つの決定の行には、注釈に `S-207` `S-208` `S-209` を付けた事例が `edge` の節にある（`tools/vectors/named.py`。他の行と同じ節に混ざる）。

## 乱数と入力の選び方

乱数は splitmix64（`state` は 64 ビット。次の値は `state += 0x9E3779B97F4A7C15`、`z = state`、`z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9`、`z = (z ^ (z >> 27)) * 0x94D049BB133111EB`、`z ^ (z >> 31)`。全て 2^64 を法とする）。演算の鍵（`i32.add.a` など）ごとに、`state = 0x4F4E5341 xor FNV-1a-64(鍵の UTF-8)` で始める。演算を足しても他の演算の乱数は変わらない。入力の集合は型の関数として `tools/vectors/sets.py` が定める（手で並べた値は無い）: 整数の core（`0..3`、`MAX` と近傍、`isqrt(MAX)`、`2^(n/2)` の前後、符号付きは `MIN` と近傍、負）、浮動小数の core（`±0`、`±inf`、NaN の符号・quiet / signaling・ペイロード、最大の有限値、最小の正規化数、非正規化数、`1 ± eps`、`2^(p-1)` と `2^p`）、変換は目標の型の端と丸めの端（二重丸めの罠、引き分け）、式は縮約・再結合で結果が変わる入力を決まった探索で選ぶ。

## 登録簿 `OPS.tsv`

列: `op`、`fn`（fixture の関数の名前）、`file`、`pkg`（fixture のパッケージ）、`args`（Onsa の型）、`ret`、`spec`（仕様の節）、`tokens`（照合する仕様の記号）、`onsa`（Onsa の式。引数は `a` `b` `c`）。登録簿が演算の一覧の唯一の元で、生成のプログラム・fixture・読み手が同じものを読む。

## fixture

`fixture/<パッケージ>/` は、`OPS.tsv` から生成した Onsa のパッケージ（`onsa.toml` と `ops.onsa`）。演算ごとに `pub fn <fn>(a, b, c)` があり、`[export] fns` に全てを並べる。`Option` を返す演算は `<fn>_some`（`Bool`）と `<fn>_val`（値。`None` のときは読まない）の 2 つ。定数は引数の無い関数 `const_<型>_<名前>`。export の境界は panic で状態の値 1 を返す（§14.2）ので、読み手は `panic:*` を 1 として照らす。

パッケージ `scalar` は今の実装が `onsa check` で受理する演算の全て。それ以外のパッケージは、まだ受理されない演算を原因ごとに分けたもので、原因の作業が終わったら `tools/vectors/ops.py` の `PENDING_PACKAGES` の規則を消し、生成し直す（関数の名前は変わらない）。

| パッケージ | 演算 | 診断 | 待つ作業 |
|---|---|---|---|
| `checked` | `checked_rem` `checked_div_euclid` `checked_rem_euclid` `checked_shl` `checked_shr` `checked_neg` | E0413（メソッドが無い）| W5-02 |
| `zero_one` | `T.ZERO` `T.ONE`（定数）| E0302 | W5-05 |
| `predicates` | `is_nan` `is_finite` | E0302（`std.math` に無い）| W5-02 |

## 再生成と確認

```sh
python3 -B tools/vectors/gen.py --out tests/vectors   # データと fixture と MANIFEST を書く
python3 -B tools/vectors/xcheck.py                    # 独立した実装との突き合わせ。XCHECK を書く（生成のたびに回す）
python3 -B tools/vectors/gen.py --check               # gate の項目 `vectors`（再生成して 1 バイトも違わないこと、ほか）
python3 -B tools/vectors/gen.py --explain tests/vectors/int-i32.tsv:300   # 1 行を 10 進と式で読む
```

生成のプログラムは Python 3.11 以降の標準ライブラリだけ（整数と `Fraction`。Python の `float` と `random` は使わない）。作り直すと同じバイトになる。
