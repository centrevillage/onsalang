# 参照評価器の出力のデータの形式（形式の版 1）

`tests/spec/flow_semantics/` の事例（`mode = "test"`）の各 `test` で、参照評価器（`crates/onsa_tests/src/flow_ref/`）が `render`・`process` などの呼び出しに返した値の表（W7-19）。インタプリタとの比べ（U3）は、この表の呼び出しを Onsa の `test` に書き直して走らせ、出力を照らす。規範は**このデータと仕様（§11.6、§11.4、§13.4）**で、評価器ではない。評価器とデータが食い違えば、どちらが仕様に合うかを仕様の文で決める。

## ファイル

| ファイル | 内容 |
|---|---|
| `<事例>.tsv` | 元の事例（ファイルの語幹か、ディレクトリの名前）と一対一。元の事例を消せば、このファイルも消す |
| `MANIFEST` | ファイルごとの行数と頭の数、合計。ハッシュは持たない（データは毎回評価器の出力と突き合わせる） |

`FORMAT.md` 以外は `UPDATE_GOLDEN=1 cargo test -p onsa_tests --test flow_ref` が作る。手で編集しない。評価器と事例の assert が一つでも食い違うと、書き直さずに失敗する。

## 行

LF で区切る。先頭の `# flow_ref 1 source=<事例の経路> tests=… evaluated=… unavailable=… skipped=… waiting=…` が頭で、数は取り出しのたびに数え直す。`waiting` は事例が降下しない（検査が E0200 を出すか、Core に降りない）なら 1。そのような事例が実装待ちの一覧（`tests/pending.toml` の `test-case`）に無ければ、入口のテストが失敗する。
頭以降は test ごとの節で、順は事例に書いた順。

| 行 | 意味 |
|---|---|
| `@ <test の名前>` | 評価して事例の assert と印が成り立った test の始まり。以後の呼び出しの行が、次の節まで続く |
| `- <名前> TAB skipped <理由>` | 評価しない test。理由は `layout`（`In`・`Out`・チャンネルの配列・`Buf`・`process_inplace`・`Span` の値、W7-12）、`statement`（取り出しの形でない文）、`nocall`（生成された関数を、test からも test が呼ぶ補助関数からも呼ばない） |
| `? <名前> TAB unavailable <理由>` | 評価器がまだ評価しない形（理由は評価器の文） |
| `! <名前> TAB failed <文>` | 評価器と test の assert や印が食い違う test。入口のテストは、これが一つでもあるとデータを書かずに失敗するので、置かれたデータには無い |

test の名前の改行とタブは空白にする。

`process` の長さの違う `slice`（入力と出力の `Span` の長さが等しくない）は、評価器が `panic start`（§11.6）にする。`render` を test が呼ぶ補助関数（`fn is_prev(d: F32) -> Bool`）の中で呼んだときも、test が呼んだのと同じ呼び出しの行になる。

### 呼び出しの行

| 行 | 意味 |
|---|---|
| `init <n> <flow> sr=<値> [cfg <名前>=<値> …]` | `var st = F.init(..)`。`n` はその test が作った状態の順（0 から） |
| `process <n> [cfg …] [params …] frames=<数> [in <名前>=[<列>] …]` | `F.process(inout st, ..)`。`in` は `sample` の入力の名前ごとの列で、`frames` は全ての `Span` の長さ |
| `render <flow> sr=<値> [cfg …] [params …] [frames=<数>] [in …]` | `F.render(..)`。`frames` は `sample` の入力の無い flow だけ |
| `reset <n>` | `F.reset(inout st)` |
| `out<経路>=[<フレームごとの値>]` | 直前の `process`・`render` の出力の葉ごと。経路は、スカラが空、`[k]` がチャンネル、`.f` が struct の出力のフィールド、`.f[k]` がそのチャンネル。葉は出力の型から決める（フレームが 0 でも `out.l=[]`・`out.r=[]`、チャンネルの配列は `out[0]=[]`・`out[1]=[]`）。`process` の行も struct の出力のフィールドの名前で書く |
| `panic <段>` | test の最後の行。段は `init`、`start`（入力の長さの比べ）、`block`、`sample <n>`（その呼び出しでフレーム `n`）、`eval`（test の中の式の panic。範囲外の添字など。`xs.slice(from, to)` の `from > to` もここ、S-1148 の仮の扱い） |

印（`TESTFAIL`・`PANIC`）の付いた test を評価して合うのは、どれかの呼び出し（か test の式）が panic し、その前の assert が全て成り立つときである。assert が偽で落ちるだけの印付きの test は合わない。印の付いていない test が panic するときも合わない。

panic した呼び出しの行は残り、`out` の行は無い。panic の後の行は無い（test はそこで止まる）。

## 値

| 型 | 書き方 |
|---|---|
| 整数 | 10 進 |
| `F32` / `F64` | `0x` と全幅（8 桁、16 桁）の小文字の 16 進で、IEEE 754 のビット（`-0.0` は `0x80000000`、入力の NaN もビット） |
| 出力の NaN | `nan`（符号とペイロードは未規定、§3.4、§13.4。どの NaN でもよい。それ以外の出力はビットが一致する） |
| `Bool` | `true` / `false` |
| `Char` | `c<コードポイントの 10 進>` |
| 配列・struct・タプル・enum | `[…]`・`{…}`（フィールドの順）・`(…)`・`#<番号>(…)`（要素は空白で区切る） |
| `()` | `()` |

`out` の列とフレームの数は同じで、`process` の出力は書き戻した局所でなく、その呼び出しの出力。
