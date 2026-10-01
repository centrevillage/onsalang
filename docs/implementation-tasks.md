# Onsa 実装計画: 作業の詳細

- 対象: [`implementation-plan.md`](implementation-plan.md) の M0〜M9 を、着手できる作業の単位に分けたもの。方針（§0）、クレート構成（§1）、中核の設計判断（§2）はそちらに従い、ここでは繰り返さない
- 仕様: [`onsa-lang-spec-0.3.md`](../onsa-lang-spec-0.3.md)（節番号は 0.3 のもの）
- 日付: 2026-10-01
- ID の種類
  - `T<M>-<n>`: 作業。マイルストーン M の n 番目。規模は S（1〜2 日）/ M（3〜5 日）/ L（1〜2 週）の目安
  - `D-nn`: **実装の判断**。仕様が決めていない、実装の側の選択。提案と理由を書く
  - `S-nn`: **仕様の空白**。作業を切り出すときに見つかった小さな未定義。決定後に仕様 0.3 へ反映する

`D` は 2026-10-01 に全て決定した（案の通り）。`S` は提案で、決定したものから仕様・レビュー §7・変更点・この文書を揃えて更新する。

---

## 0. 見取り図

| M | 成果 | 利用者が確認できること | 規模 |
|---|---|---|---|
| M0 | 基盤 | `onsa check --json empty.onsa` が `[]`、CI が緑 | S |
| M1 | 字句・構文・fmt | 仕様の全ての例が解析でき、`fmt` が冪等 | M |
| M2 | 名前解決・核の型検査 | §17.6 `Poly` を含む核の例が `check` を通り、否定例が所定のコードで落ちる | L |
| M3 | flow の検査・降下、インタプリタ | `onsa test` で §17.3 `resonator decays` が通る。`interface` と `graph` | L |
| M4 | C バックエンドと export | §17.5 の C ホストがビルドでき、`voice` が interp とビット一致 | L |
| M5 | std と適合性テスト | `std.math` の精度、`--backends all`、`--flows` | M |
| M6 | WASM | ブラウザで `voice` が鳴る。3 者一致 | M |
| M7 | IDE の核 | VS Code で診断とホバー、`play`、`probe` | L |
| M8 | JS | 4 者一致 | M |
| M9 | 締め | `explain` 全コード、`audit` | S |

依存: M0 → M1 → M2 → M3 → M4 → M5 → M6 → M7。M8 は M6 の後、M9 は M7 の後。M4 の完了が第 1 期の最初の区切り（計画 §6）。

M3 で `resonator` を動かすには `exp` / `cos` が要るので、`std.math` の **宣言とインタプリタの対応付け** は M3 に入れ、M5 では精度の測定と差し替えだけを行う。

---

## 1. 実装の判断（D）

全て 2026-10-01 に案の通り決定。

### D-01 字句解析器と構文解析器は手書き（再帰下降）

- 案: パーサジェネレータを使わず、手書きの字句解析器と再帰下降の構文解析器にする。
- 理由: (1) 文の区切りが改行に依存し、文脈（ブロックの中か、括弧の中か）で改行の意味が変わる（§2.5）。ジェネレータでは字句解析器に文脈を戻す経路が要る。(2) 既存言語の書き方への修正候補（§18.1）は、エラー回復の中で「何を書こうとしたか」を推定する専用の規則で、手書きでしか書けない。(3) LSP で編集中のソースを扱うには、エラーから回復して AST を作り続ける必要がある。
- 代替: `lalrpop` / `pest`。文法の検証には使えるが、上記 3 点で結局手書きの層が要る。

### D-02 AST はアリーナ + ID。スパンはバイトオフセット

- 案: 各ノードは `Vec` に置き、`ExprId(u32)` などの ID で参照する。スパンは `Span { start: u32, end: u32 }`（ファイル内のバイトオフセット）。行・列は `LineIndex` で必要なときに計算する。トークンの前後の空白とコメント（trivia）はトークン列に残し、AST はトークン列への索引を持つ（`fmt` と `diff --ast` が使う）。
- 理由: `Box` のツリーは `wasm32` でも動くが、LSP で部分的に差し替えるのと、`fmt` でトークンの前後の空白を再現するのに、ID と索引の方が扱いやすい。rust-analyzer と同じ方向。
- 代替: `Box` のツリー。最初は速いが、`fmt` でコメントの位置を失う。

### D-03 Core IR は構造化ツリー。flow は `init` / `reset` / `ctl` / `tick` / `process` の 5 関数に落とす

- 案: Core は CFG / SSA ではなく、**構造化された文と式のツリー** にする（`if` / `while` / `for` の範囲、`match` は enum のタグの `switch`）。全てのバックエンドがソース（C / JS）か構造化バイトコード（WASM）なので、CFG に落とすと構造を復元する作業が各バックエンドに要る。
- flow は次の 5 つの Core 関数に落とす（計画 §2.2 の `process` を 2 つに分けたもの）。

| 関数 | 内容 | 呼ばれる場所 |
|---|---|---|
| `f.init(cfg, sr) -> State` | `Init` レートの `let` を評価して状態を構築 | 利用者、親の `init` |
| `f.reset(inout s)` | 遅延と `prev` を `init` 値へ、`w = 0`、サブインスタンスを `reset`、`poisoned = false` | 利用者、親の `reset` |
| `f.ctl(inout s, p: Params)` | `Ctl` レートの `let` を順に評価し、`Sig` から参照されるものを状態へ書く。サブインスタンスの `ctl` を呼ぶ | `f.process` の先頭、親の `ctl` |
| `f.tick(inout s, <Sig 入力の値>...) -> <出力の値>` | `Sig` レートの `let` を順に評価する 1 サンプル分。サブインスタンスの `tick` を呼ぶ | `f.process` のループ、親の `tick` |
| `f.process(inout s, p, <Span>...)` | `ctl` を 1 回呼び、`for i in 0..frames` で入力を全て読み、`tick`、出力を全て書く（§11.6 の不変条件） | 利用者、export の wrapper |

- `process_inplace` は `process` に同じ `Span` を渡すだけの関数。`render` は `Buf` を確保して `process` を 1 回呼ぶ（インタプリタと `Alloc` のあるターゲットだけ）。
- 理由: 親 flow が子を点ごとに呼ぶには、子のブロックレートの計算（`ctl`）とサンプルの計算（`tick`）が分かれていなければならない。FAUST の `compute` を `control` と `loop` に分けた形と同じ。`tick` が関数呼び出しになるのは C コンパイラがインライン化するので問題ない。
- 代替: 子の `process` をブロック単位で呼び、中間バッファを置く。状態の大きさにブロック長が入り、§12.4 の「コンパイル時に決まる」が崩れる。

### D-04 診断の登録簿はマクロで作る Rust の表。`explain` の本文は markdown ファイル

- 案: `onsa_diag/src/codes.rs` に `codes! { E0010 => { category: Syntax, message: "..." }, ... }` の形で全コードを書き、`explain` の本文は `onsa_diag/explain/E0010.md` を `include_str!` で埋め込む。テストで「仕様 §18.1 の範囲に収まる」「本文のファイルが全コード分ある（M9 の受け入れ）」を検査する。
- 理由: コードの追加漏れをコンパイルエラーにしたい。本文は長文なので Rust ソースから分ける。
- 代替: TOML の登録簿を実行時に読む。`wasm32` で `include_str!` にするなら差は無いが、型の検査が無い。

### D-05 `tests/spec` の形式はインラインのマーカ

- 案: 期待する診断を、同じ行の末尾に `//~ E0010` と書く（rustc の UI テストと同じ形。`//~ E0010 @13` で列も指定できる）。マーカの無いファイルは診断 0 件を期待する。ファイルの先頭行で検査の深さを指定する:

```
//! mode: none      // 収録のみで実行しない（`...` を含む断片、最上位の文、擬似コード）
//! mode: parse     // 構文解析だけ（第 1 期で未対応の fn 世界の例）
//! mode: check     // check --json の結果をマーカと比較（既定）
//! mode: test      // check の後、test ブロックをインタプリタで実行する
```

- 理由: 別ファイルの `.expect` より、否定例の意図が行の横に見える。仕様の例を含むファイルにマーカを足しても、§6 の同期検査（D-06）はマーカを無視して照合できる。
- 代替: 計画 §1 の `.expect`。JSON の全文を比較できるが、行番号のずれで壊れやすい。

### D-06 仕様の例と `tests/spec` の同期を機械的に検査する

- 案: `tools/check_spec_examples.py` が、仕様の全ての ```` ```onsa ```` ブロックについて「`tests/spec/` のどれかのファイルに、行末の `//~ ...` を除いて逐語的に含まれる」ことを検査し、CI で回す。擬似コードや `...` を含む断片は `mode: none` のファイルに収録する（S-15 は不要になった）。
- 理由: P9（仕様の例は全て検査を通る）を仕様の編集のたびに保証する。
- 代替: 仕様から自動で切り出す。断片（§3.1、§5.1、§7）は関数で包まないと検査できないので、手で用意した上で照合する方が確実。

### D-07 `std` は Onsa のソースで書き、プリミティブは `target fn` で宣言する。ソースはバイナリに埋め込む

- 案: `std/math.onsa` は次のように書く。

```onsa
pub target rt fn exp[T: Float](x: T) -> T
pub target rt fn sqrt[T: Float](x: T) -> T
```

  各バックエンド（インタプリタ、C、WASM、JS）が `std.math` の `target` 宣言の実装を持つ。`std` のソースは `include_str!` でコンパイラに埋め込み、`wasm32` でもファイル I/O なしで使える。利用者のパッケージの `target` 宣言は、第 1 期では `bind` が無いので E0200。

- 理由: §15.2 の `target` は「実装をビルドターゲットが与える宣言」で、プリミティブの意味そのもの。`extern "C"` にすると核が C 系以外へ出せなくなる（§13.2 の E1010）。
- 代替: コンパイラ組込みの名前。ソースが無いので `onsa primer --std` と `interface` に出すものを別に持つことになる。

### D-08 第 1 期の効果の扱い: `Alloc` だけを認識し、`test` ブロックの中でだけ使える

- 案: 効果行は構文解析と名前解決まで通す。第 1 期で意味を持つのは `Alloc` だけで、他の効果名は E0200。`Alloc` を要する操作（`Buf.zeroed`、`render`、`impulse`）は、`uses {Alloc}` を持つ関数と `test` の本体でだけ呼べる（§8.5 の「テストランナーが `Alloc` を提供する」の部分だけを実装する）。`Buf[T]` はインタプリタの内蔵型で、C / WASM / JS バックエンドは `Buf` を含む関数を出力しない（E0200）。
- 理由: M3 の受け入れ（`resonator decays`）が `impulse(48000) -> Buf[F32] uses {Alloc}` と `o.out: Buf[F32]` を使う。効果の仕組み全体（handler、証拠渡し）を入れずに、この経路だけを通す。
- 代替: `render` を `[F32; N]` を返す形にして `Buf` を避ける。`N` が実行時の値なので無理。

### D-09 依存クレートは最小にする

| 用途 | クレート | `wasm32` |
|---|---|---|
| CLI | `clap`（derive） | 不要 |
| JSON / TOML | `serde`, `serde_json`, `toml` | 可 |
| WASM の出力 | `wasm-encoder` | 可 |
| LSP | `lsp-server`, `lsp-types`（rust-analyzer と同じ） | 不要 |
| 音声出力（`play`） | `cpal` | 不要 |
| 動的ロード（`play`） | `libloading` | 不要 |
| wasm-bindgen | `wasm-bindgen` | `onsa_web` のみ |

字句・構文・型・Core・インタプリタ・C 出力には外部クレートを使わない。

### D-10 C の出力単位と名前

- 案: パッケージごとに 1 つの翻訳単位 `onsa_<package>.c` と、export する flow ごとのヘッダ `onsa_<flow>.h`、共通の `onsa.h`。内部の名前はモジュールパスを `__` でつないだ `static` 関数（`dsp__voice__tick`）。型は `dsp__voice__State`。export は `prefix` + 名前の最後の要素（§14.2）。固定長配列は `struct { T a[N]; }` で包み、値として扱えるようにする。集成体を返す関数は出力ポインタを第 1 引数に取る（§12.7）。
- 理由: 1 翻訳単位なら C コンパイラが `tick` をインライン化できる。配列を struct で包むのは、C の配列が値でないため。

### D-11 WASM の libm は musl を Onsa に移植したもの（= `std.math.exact` の先行実装）

- 案: `expf` / `logf` / `sinf` / `cosf` / `tanf` / `tanhf` / `powf` / `exp2f` / `log2f` と F64 版を、musl の実装から Onsa の `rt fn` に移植して `std/math/soft.onsa` に置く。WASM バックエンドは `std.math` の `target` 宣言をこれに束縛する。移植には `F32.to_bits()` / `F32.from_bits()` が要る（S-09）。
- 理由: WASM には libm が無い。C で書いた libm を wasm に別途コンパイルするとツールチェーンが増える。Onsa で書けば核のまま WASM / JS / C の全てで使え、§19 の `std.math.exact` と、libm の精度が足りない組込み向けの差し替え（§13.4）が同じもので済む。
- 代替: JS の `Math` を import する。AudioWorklet から import 関数を呼ぶ往復が重く、精度も環境依存。

### D-12 精度テストの参照値は mpmath で生成した表

- 案: `tools/gen_precision_tables.py`（mpmath）で、関数ごとに 4096 点（境界値、非正規化数、大きな値、乱数）の正しく丸めた値を生成し、`tests/precision/*.bin` に置く。テストは各環境の結果と比べて ULP 差を測る。
- 理由: MPFR を Rust から使う `rug` は C のビルドが要り、`wasm32` でも CI でも重い。表なら依存が無い。

### D-13 `play` は C → 共有ライブラリ → `libloading` + `cpal`。UI は端末

- 案: `onsa play voice` は M4 の経路で C を出力し、ホストの C コンパイラで共有ライブラリにして `libloading` で読み、`cpal` で鳴らす。パラメータは端末のキー操作（`@param` の一覧をスライダ風に表示）。GUI は IDE 側（M7 の `onsa_web` を使うブラウザ IDE）で作る。
- 理由: インタプリタはサンプル単位の `tick` には遅く、実時間の試聴に向かない。共有ライブラリなら M4 の生成物をそのまま使える。
- 代替: インタプリタで実時間。単純な flow なら動くが、保証できない。

### D-14 CI の構成

| ジョブ | 内容 |
|---|---|
| `check` | `cargo fmt --check`, `cargo clippy --all-targets -D warnings`, `cargo test` |
| `wasm` | `cargo build --target wasm32-unknown-unknown` を wasm 可のクレートに対して |
| `spec` | D-06 の同期検査、`tests/spec` のランナー |
| `conformance`（M4 以降） | Linux の clang と gcc、Windows の MSVC で C を生成・ビルドし、interp と比較 |
| `precision`（M5 以降） | 各 OS の libm の ULP を測定し、結果を artifact に残す |

---

## 2. 仕様の空白（S）

実装の作業を切り出すときに見つかった、仕様 0.3 が決めていない小さな項目。決めなくても着手できるが、該当する作業の前に決める。

| ID | 項目 | 提案 | 決める時期 |
|---|---|---|---|
| S-01 | 命名規則違反（§2.3）の診断コードが無い | E0320。種別ごとに修正候補（`fn Foo` → `fn foo`） | M1 |
| S-02 | 既存言語の書き方への修正候補（§18.1）のコードが無い | E0020 を 1 つにし、`found` と `fixes` で種類を区別する。一覧は T1-8 | M1 |
| S-03 | 「この版では未対応」のコードが無い | E0200。`message` に機能名（`effect handlers`、`Str`）を入れる | M2 |
| S-04 | flow の呼び出しで、引数のレートが入力の宣言のレートより高い（`Sig` を `Ctl` 入力へ、`Ctl` を `Init` 入力へ）ときのコードが無い | E0815。昇格の逆は無い（§11.3）ので、必ずエラー | M3 |
| S-05 | 状態の中で `let` に由来しないフィールドの位置 | 先頭から順に: bulk 領域のポインタ（`BULK_SIZE > 0` のとき）、`sample_rate: F32`（`Ctl` / `Sig` から参照されるとき）、`let` 由来のフィールド（宣言順）、`poisoned: Bool`、`jmp_buf`（`panic = "poison"` のとき）。`Sig` から参照される `Ctl` レートの `let` も状態に置く（FAUST と同じ。`ctl` と `tick` の間で受け渡す場所が要る） | M3 |
| S-06 | 名前の無いノードの名前 | 種類と番号: `prev_0`、`delay_0`、`vdelay_0`、`smooth_0`（§11.6 の `smooth_0` と同じ規則）。`delay` / `vdelay` の内部フィールドは `<名前>.buf`、`<名前>.w`（C では `d_buf`、`d_w`）。定数でない `init` の保存先は `<名前>.init` | M3 |
| S-07 | `fmt` の整列。§17.3 の例は連続する `let` の `=` と行末コメントを揃えている | gofmt と同じく、連続する 1 行の `let` の `=` と、連続する行の行末コメントを揃える。それ以外の整列は無い。行の自動折り返しはしない（書き手の改行を保つ） | M1 |
| S-08 | `if` / `while` / `match` / `for` の見出しの式に struct リテラルを書けるか。`if s == Shape.Circle {` が `Shape.Circle { ... }` と曖昧になる | Rust と同じく見出しの式では struct リテラルを書けない（括弧で囲めば書ける） | M1 |
| S-09 | `std.math` の関数の型。F32 と F64 の両方に使うが多重定義は無い（§6.1） | `Float` でジェネリック: `exp[T: Float](x: T) -> T`。`abs` / `min` / `max` は `Num`。`F32.to_bits() -> U32` / `F32.from_bits(U32)`（F64 は U64）を組込みメソッドに加える（D-11 と `std.math.exact` に要る） | M3 |
| S-10 | `std.dsp.sum` の演算順と `magnitude_at` の定義 | `sum[const N](xs: [F32; N]) -> F32` は `xs[0]` から順に左へ畳む（ビット一致のため順序を固定）。`magnitude_at` は F64 の Goertzel で、結果を F32 に丸める | M5 |
| S-11 | パッケージルートと単一ファイル | ルートは `onsa.toml` のあるディレクトリで、`.onsa` ファイルをその下から再帰的に集める（`tests/`、`target/` を除く）。マニフェスト無しの `onsa check foo.onsa` は、そのファイルを 1 モジュールのパッケージとして扱う（モジュール名はファイル名） | M2 |
| S-12 | 第 1 期で使える `Span` のメソッド | `len()`、`slice(from, to)`、`get(i) -> Option[T]`、`fill!(v)`、`add_from!(other)`、`copy_from!(other)`。`[T; N]` と `Buf[T]` にも同じものがある | M2 |
| S-13 | `@derive` の第 1 期の範囲 | `PartialEq Eq PartialOrd Ord Default` は実装、`Hash Show` は E0200（`Str` が要る）。`Option` / `Result` / タプル / `[T; N]` の `PartialEq` は組込み（§17.6 の `self.notes[i] == Some(note)`） | M2 |
| S-14 | `--backends all` で、どの出力を許容誤差で比べるか | flow 単位。Core の到達解析で超越関数のプリミティブに到達する flow は全ての出力を許容誤差（2 ULP）で、到達しない flow はビット一致で比べる | M5 |
| S-15 | §11.6 の生成 API のブロックは擬似コードで、解析できない | 取り下げ。`tests/spec/flow/generated_api.onsa` に `mode: none` で収録した（M0 で解決） | — |
| S-16 | `test` の名前の重複と、`assert` の失敗の報告の形 | 同じモジュールで同名の `test` は E0306。失敗は `test "name" failed at file:line: assert <式のソース>` の形で、`--json` では診断と同じ形に `"kind": "test"` を足す | M3 |
| S-17 | §17.3 と §17.4 は同じモジュールだが、`use std.math.{exp, cos}` と `use std.math.{floor, exp}` で `exp` を二度取り込む | 同じ名前の二度目の `use` は E0304（束縛の重複）とし、§17.4 の行を `use std.math.{floor}` に直す。`use` はモジュールのどの位置にも書ける（Rust と同じ） | M2 |
| S-18 | 字句・構文の一般のエラー（不正な文字、予期しないトークン）のコードが無い | E0001（不正な文字・リテラル）、E0002（予期しないトークン。`message` に期待したものを書く） | M1 |
| S-19 | 文字列・文字リテラルのエスケープが未定義（§8.3 の例は `"a\nb\n"` を使う） | Rust と同じ `\n \t \r \0 \\ \" \' \u{XXXX}` の閉じた一覧 | M1 |
| S-20 | `test` はキーワードだが、標準ライブラリのモジュール名に `std.test`、`std.dsp.test` を使っている（§11.8、§17.3） | パスの `.` の直後ではキーワードを名前として許す（構文解析器はそうした）。または `std.testing` に改名する | M2 |

---

## 3. 共通の設計

計画 §2 を実装の型に落としたもの。クレートの境界で共有する。

### 3.1 スパンと診断（`onsa_diag`）

```rust
pub struct FileId(u32);
pub struct Span { pub file: FileId, pub start: u32, pub end: u32 }   // バイトオフセット、半開
pub struct Diagnostic {
    pub code: Code,                 // D-04 の登録簿
    pub message: String,            // 英語。登録簿のテンプレートに名前を埋めたもの
    pub span: Span,
    pub found: Option<String>,      // 問題の箇所のソース
    pub fixes: Vec<Fix>,            // Fix { replace: String } または Fix { insert_before/after }
    pub notes: Vec<(Span, String)>, // 関連位置（「ここで束縛された」など）
}
```

JSON は §18.1 の形そのもの（`span` は `file` / `line` / `col` / `end_col` に展開）。複数行にまたがる場合は `end_line` を足す。

### 3.2 AST（`onsa_syntax`）

- `Token { kind, span }` の列。コメントと空白は `Trivia` としてトークンに付属させる（`fmt` が使う）。
- `Item`（`Fn` / `Flow` / `Struct` / `Enum` / `TypeAlias` / `Trait` / `Impl` / `Effect` / `Handler` / `Const` / `Use` / `Extern` / `Target` / `Test`）、`Type`、`Pattern`、`Expr`、`Stmt`、`Attr`。全てのノードが `Span` を持つ。
- 式の二項演算は構文解析では **平らな列** `Binary { operands: Vec<ExprId>, ops: Vec<(BinOp, Span)> }` として保持し、群の検査（E0010）は構文解析の直後の独立した段で行う。これにより E0010 の修正候補（括弧の挿入位置）を列全体から作れる。
- `Call { callee, kind: Plain | Flow (~) | Bang (!) , args: Vec<Arg> }`、`Arg { mode: Borrow | Inout | Move, expr }`。
- `Attr::Param { keys: Vec<(key, const expr)> }` は flow の入力にだけ付く。

### 3.3 型と種（`onsa_sema`）

- `Ty` はインターン（`TyId(u32)`）: `Int(IntKind)`, `Float(F32|F64)`, `Bool`, `Char`, `Unit`, `Array(TyId, u32)`, `Tuple(Vec<TyId>)`, `Named(DefId, Vec<GenericArg>)`, `Span(TyId)`, `Fn(FnSig)`, `Ptr(TyId)`, `Buf(TyId)`（第 1 期はインタプリタ限定）, `Rate(Rate, TyId)`（flow の中だけ）, `Var(TyVarId)`（推論中）。
- 種は `Kind::{Copy, Shared, Affine}` を型の構造から計算して `TyId` ごとにキャッシュする。
- 大きさと配置は `layout(TyId) -> Layout { size, align, fields: Vec<(name, offset)> }`。§12.4 の規則。`onsa interface`、`SIZE`、`_Static_assert`、プローブ、ホットリロードが全て同じ関数を使う。
- 推論の状態は `Infer { vars: Vec<Option<TyId>>, lits: Vec<LitConstraint> }`。文の順に進め、関数の終わりで未解決の `IntLit` / `FloatLit` を E0405 にする。

### 3.4 Core IR（`onsa_core`）

```rust
pub struct Module { types: Vec<TypeDef>, consts: Vec<ConstDef>, fns: Vec<FnDef>, flows: Vec<FlowMeta> }
pub struct FnDef {
    name: QualName,                       // dsp.voice.tick の形。C では __ 区切り
    params: Vec<Param>,                   // Param { local, mode: Borrow|Inout|Move, ty }
    ret: Ty, sret: bool,                  // 集成体を返すなら sret = true（§12.7）
    rt: bool, locals: Vec<Local>, body: Block,
}
pub enum Stmt { Let(LocalId, Expr), Assign(Place, Expr), Expr(Expr),
                If(Expr, Block, Block), While(Expr, Block), ForRange(LocalId, Expr, Expr, Block),
                Break, Continue, Return(Option<Expr>) }
pub enum Expr { Lit(Lit, Ty), Local(LocalId), Const(ConstId),
                Unary(UnOp, Ty, Box<Expr>), Binary(BinOp, NumTy, Overflow, Box<Expr>, Box<Expr>),  // Overflow: Checked|Wrap|Sat
                Cmp(CmpOp, Ty, ..), Cast(Ty, Ty, ..), Call(FnId, Vec<Arg>), Prim(PrimId, Vec<Expr>),
                Field(Box<Expr>, u32), Index(Box<Expr>, Box<Expr>),  // Index は常に境界検査付き
                Struct(Ty, Vec<Expr>), Array(Vec<Expr>), Repeat(Box<Expr>, u32), Tuple(Vec<Expr>),
                IfExpr(..), Switch(Box<Expr>, Vec<(Tag, Block)>),  // enum のタグで分岐。束縛は Field で取り出す
                Panic(MsgId) }
pub enum Place { Local(LocalId), Field(Box<Place>, u32), Index(Box<Place>, Expr) }
```

- 全ての式に型が付く。ジェネリクスは無い（単相化済み）。レートは無い（flow は降下済み）。
- `Prim` は `std.math` の `target` 宣言と組込みメソッド（`trunc_i32_sat`、`to_bits`、`Span.len` など）。`PrimId` の一覧を `onsa_core::prim` に置き、各バックエンドはこの一覧に対して対応表を持つ（表の欠けはテストで検出）。
- `verify(Module)` は、型の一致、`inout` 引数が `Place` であること、ローカルの定義前の使用、rt 関数が rt 関数だけを呼ぶこと、`Switch` の網羅性を検査する。デバッグビルドでは降下・単相化の各段の後に走らせる。
- テキスト形式 `onsa dump --core`（隠しコマンド）を持ち、golden テストにも使う。

### 3.5 flow の降下の形

D-03 の 5 関数。§17.3 の `resonator` なら次の形になる（擬似 Onsa）。

```
struct resonator.State {
  sample_rate: F32          // S-05: Ctl から参照される
  r: F32, b1: F32, b2: F32  // Ctl レートの let のうち Sig から参照されるもの（S-05）。w は Ctl からしか参照されないので省く
  y1: F32                   // prev(y, 0.0) の保存値
  y2: F32                   // prev(y1, 0.0) の保存値
  poisoned: Bool
}
fn resonator.init(cfg: resonator.Config, sr: F32) -> State { State { sample_rate: sr, r: 0.0, ..., y1: 0.0, y2: 0.0, poisoned: false } }
rt fn resonator.reset(inout s) { s.y1 = 0.0; s.y2 = 0.0; s.poisoned = false }
rt fn resonator.ctl(inout s, p: Params) {
  s.r = exp(-(F32.PI * p.bw) / s.sample_rate)
  let w = (2.0 * F32.PI * p.fc) / s.sample_rate   // 状態に置かないローカル
  s.b1 = 2.0 * s.r * cos(w)
  s.b2 = s.r * s.r
}
rt fn resonator.tick(inout s, x: F32) -> F32 {
  let y1 = s.y1                       // prev の出力は保存値
  let y2 = s.y2
  let y = ((1.0 - s.r) * x) + (s.b1 * y1) - (s.b2 * y2)
  s.y2 = y1                           // prev(y1): y1 を保存
  s.y1 = y                            // prev(y):  y を保存
  y
}
rt fn resonator.process(inout s, p, x: Span[F32], inout out: Span[F32]) {
  // 長さの検査（違えば panic）
  resonator.ctl(inout s, p)
  for i in 0..x.len() { let xi = x[i]; let yi = resonator.tick(inout s, xi); out[i] = yi }
}
```

- `prev` の保存は、その `let` の評価の **後**、`tick` の末尾でまとめて行う（§11.4「出力は保存値で、その後に `e` を保存する」）。複数の `prev` が同じ信号を参照しても、保存は各ノードが独立に持つ。
- `delay` / `vdelay` は §11.4 の演算順をそのまま `tick` の中に展開する（関数にしない。順序を固定したいため）。
- 親の `tick` は子の `tick` を `Call` で呼ぶ。子の `Ctl` 入力に渡す親の値は、親の `ctl` で子の `Params` を組み立てて子の `ctl` を呼ぶ。
- `par` は `[sub.State; N]` と `ForRange` に落とし、`i` はループ変数（`Init` レートの値）。

---

## 4. 作業

### M0 基盤（S）

| ID | 作業 | 場所 | 規模 |
|---|---|---|---|
| T0-1 | Cargo ワークスペースと全クレートの空の骨格、`rust-toolchain.toml`（stable）、`.gitignore` に `target/` を追加、`Cargo.lock` をコミット | ルート、`crates/*` | S |
| T0-2 | `onsa_diag`: §3.1 の型、D-04 の登録簿（この文書 §5 の全コードを登録。`explain` 本文は空でよい）、JSON と人間向けの出力、`LineIndex` | `onsa_diag` | S |
| T0-3 | `onsa_cli` の骨格: `onsa check [--json] <path...>`、`onsa explain <code>`。終了コード 0（診断なし）/ 1（診断あり）/ 2（使い方・I/O の誤り） | `onsa_cli` | S |
| T0-4 | `tests/spec` のランナー（D-05）: ファイルを集め、`//! mode:` とマーカを読み、`check` の結果と `(code, line)` の集合を比較する。`cargo test -p onsa_tests` で走る | `crates/onsa_tests` | S |
| T0-5 | D-06 の同期検査スクリプトと、仕様の 39 ブロックの収録（T1-11 の前倒し） | `tools/`, `tests/spec` | S |
| T0-6 | D-14 の `check` / `wasm` / `spec` ジョブ | `.github/workflows/ci.yml` | S |

受け入れ: `onsa check --json tests/spec/empty.onsa` が `[]` を出し、CI が緑。

### M1 字句・構文解析と fmt（M）

✅ は完了（2026-10-01）。構文解析の実装上の注記: 式の中の `a.b` は `Path` 1 要素 + `Field` の連鎖で表し、複数要素の `Path` は型・`use`・パターン・属性・struct リテラルにだけ現れる（名前解決が `Field(Path(voice), init)` をモジュールのパスに読み替える）。パターンの `-1` は `PatKind::Neg`。E0320 は構文解析の後の独立した段（`naming.rs`）。

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T1-1 ✅ | 字句解析器 | §2 の全トークン。キーワード（§2.2）。識別子の種別（`snake_case` / `UpperCamel` / `UPPER_SNAKE` / `_`）を字句の段で分類。整数（10 進・`0x`・`0b`・`_`）、浮動小数（小数点の両側に数字。`1.` / `.5` は E0020 の修正候補）、`'c'`、文字列（`{名前.フィールド}` の補間と `{{` `}}` を字句の段で分解）。`//` と `///`。`名前~(` と `名前!(`（識別子の直後、空白なし、直後が `(`）。`.` 直後の数字列はタプルの添字。改行は `Newline` トークンとして出す | M |
| T1-2 ✅ | AST | §3.2。全ノードにスパン、trivia の保持 | S |
| T1-3 ✅ | 宣言の構文解析 | 下の文法の `Item` 全部。属性（`@derive` `@repr` `@relaxed` `@deprecated` `@param`）、ドキュメントコメントの付属 | M |
| T1-4 ✅ | 文とブロック | 文の区切り（§2.5）: ブロックの中では `Newline` で文を終える。行末が二項演算子・`=`・`->`、または次の行が `.` で始まれば継続。括弧・角括弧・struct リテラル・`match` の腕の並びの中では `Newline` を読み飛ばす（文脈のスタック）。`else` の位置 E0003。ブロックの値（最後の式）。`let` のパターン、`var`、代入、`for ... in [move]`、`while`、`break` / `continue` / `return`、`assert` | M |
| T1-5 ✅ | 式 | 後置 > 前置 > `as` > 二項の結合。二項は平らな列として保持し、独立した段で群の検査 E0010（修正候補: 括弧の挿入）、E0011、E0012。struct リテラル（S-08 の制限）、配列 `[a, b]` / `[e; N]`、タプル、`if` / `else if`、`match` と腕、無名 `fn`、`handle { } with ...`、`unsafe { }`、`par i in a..b { }`、引数のモード（`inout x`、`move x`、`inout [a, b]`）、`?`、`_` | M |
| T1-6 ✅ | パターン | §7 の一覧。`\|` は パターンの文脈でだけ選択 | S |
| T1-7 ✅ | エラー回復 | 項目単位: エラーの後は次の行頭の項目キーワードまで読み飛ばす。関数の中では次の文まで。関数ごとに最初のエラーだけを報告（P-01） | S |
| T1-8 ✅ | 既存言語の書き方（E0020、S-02） | 検出する形と修正候補: `&mut x` / `&x` → `inout x` / `x`、`<T>` → `[T]`、`::` → `.`、行末の `;` → 削除、`i32 i64 u8 u32 u64 f32 f64 bool usize isize` → `I32 ...`（`usize` → `U32`）、`let mut` → `var`、`loop {` → `while true {`、`proc` → `flow`、`fn f<T>` / `impl<T>` → `[T]`、`mut self` → `inout self`、`#[derive(...)]` → `@derive(...)`、`..=` → 無い（`a..b + 1`）、`+ ~ _`（FAUST）→ `prev` の説明、`1.` / `.5` → `1.0` / `0.5`、`x = e` を flow の本体で → `let x = e` | M |
| T1-9 | `onsa fmt` | 正規化の規則: 2 空白の字下げ、二項演算子の両側に 1 空白、`,` の後に 1 空白、括弧の内側に空白なし、複数行の並びには末尾の `,`、`else` は `}` と同じ行、末尾の `return` を除去、項目の間は 1 空白行、ファイル末尾は改行 1 つ、S-07 の整列、書き手の改行は保つ（自動折り返しなし）。コメントはトークンの trivia から再現。`--check` | M |
| T1-10 | `onsa diff --ast` | 2 つのファイルの AST を trivia を無視して比較し、変わった項目の一覧（追加・削除・変更）と、変更された項目の中の最初の差の位置を出す | S |
| T1-11 ✅ | 仕様の例の収録 | §6 の表の全ブロックを `tests/spec/` に置く（第 1 期で未対応のものは `mode: parse`）。否定例（E0003 / E0010 / E0011 / E0012 / E0020 / E0320）を各 3 つ以上 | S |

文法（EBNF。`NL` は改行トークン、`{}` は繰り返し、`[]` は省略可）:

```
File       = { Item }
Item       = { DocComment } { Attr } [ Vis ] ( Fn | Flow | Struct | Enum | TypeAlias | Trait | Impl
           | Effect | Handler | Const | Use | Extern | Target | Test )
Vis        = "pub" [ "(" "pkg" ")" ]
Use        = "use" Path [ "." "{" Ident { "," Ident } [ "," ] "}" ]
Fn         = [ "rt" ] "fn" Ident [ Generics ] "(" Params ")" [ "->" Type ] [ "uses" EffectRow ] Block
FnSig      = [ "rt" ] "fn" Ident [ Generics ] "(" Params ")" [ "->" Type ] [ "uses" EffectRow ]
Generics   = "[" GenParam { "," GenParam } "]"
GenParam   = TypeName [ ":" Bound { "+" Bound } ] | "const" Ident ":" Type | Ident      // Ident は効果行変数
Bound      = [ "?" ] Path
Params     = [ Param { "," Param } [ "," ] ]
Param      = { Attr } [ "inout" | "move" ] ( "self" | Ident | "_" ) [ ":" Type ]        // self に型なし。型の省略は無名 fn だけ
Flow       = "flow" Ident "(" Params ")" "->" Type Block
Struct     = "struct" TypeName [ Generics ] ( "{" Fields "}" | "(" Type ")" )
Fields     = [ Field { "," Field } [ "," ] ]        Field = [ Vis ] Ident ":" Type
Enum       = "enum" TypeName [ Generics ] "{" Variant { "," Variant } [ "," ] "}"
Variant    = TypeName [ "(" Type { "," Type } ")" ]
TypeAlias  = "type" TypeName "=" Type
Trait      = "trait" TypeName [ Generics ] "{" { FnSig | Fn | Const } "}"
Impl       = "impl" [ Generics ] Type [ "for" Type ] "{" { [ Vis ] ( Fn | Const ) } "}"
Effect     = [ "blocking" ] "effect" TypeName "{" { FnSig } "}"
Handler    = "handler" Ident [ "(" Params ")" ] ":" Path "{" { Fn } "}"
Const      = "const" ConstName ":" Type "=" Expr
Extern     = "extern" Str "lib" Str "{" { "type" TypeName | FnSig } "}"
Target     = "target" ( "type" TypeName | FnSig )
Test       = "test" Str Block
EffectRow  = "{" [ Path { "," Path } ] "}"
Attr       = "@" Ident [ "(" AttrArg { "," AttrArg } ")" ]      AttrArg = Ident ":" Expr | Path | Str
Type       = Path [ "[" Type { "," Type } "]" ]                 // F32, Sig[F32], Array[T], voice.State
           | "[" Type ";" Expr "]" | "(" ")" | "(" Type "," Type { "," Type } ")"
           | [ "rt" ] "fn" "(" [ ParamType { "," ParamType } ] ")" [ "->" Type ] [ "uses" EffectRow ]
ParamType  = [ "inout" | "move" ] Type

Block      = "{" { Stmt NL } [ Expr ] "}"
Stmt       = "let" Pattern [ ":" Type ] "=" Expr | "var" Ident [ ":" Type ] "=" Expr | Expr "=" Expr
           | "for" Pattern "in" [ "move" ] Expr Block | "while" Expr Block
           | "break" | "continue" | "return" [ Expr ] | "assert" Expr | Expr
Expr       = Cast { BinOp Cast }                     // 群の検査は後段
Cast       = Prefix [ "as" Type ]
Prefix     = ( "-" | "!" ) Postfix | Postfix
Postfix    = Primary { "(" Args ")" | "~(" Args ")" | "!(" Args ")" | "." Ident | "." Int | "[" Expr "]" | "?" }
Primary    = Literal | Path | "_" | "(" Expr ")" | "(" Expr "," Expr { "," Expr } ")"
           | "[" Args "]" | "[" Expr ";" Expr "]" | Path "{" FieldInits "}"    // S-08: 見出しの式では不可
           | Block | "if" Expr Block { "else" "if" Expr Block } [ "else" Block ]
           | "match" Expr "{" { Pattern [ "if" Expr ] "=>" Expr "," } "}"
           | "fn" "(" Params ")" [ "->" Type ] [ "uses" EffectRow ] Block
           | "handle" Block "with" ( Path [ "(" Args ")" ] | Path "{" { Fn } "}" )
           | "unsafe" Block | "par" Ident "in" Expr ".." Expr Block
Args       = [ Arg { "," Arg } [ "," ] ]            Arg = [ "inout" | "move" ] Expr
Pattern    = PatAlt { "|" PatAlt }
PatAlt     = "_" | Ident | Literal | Path [ "(" Pattern { "," Pattern } ")" ]
           | "(" Pattern "," Pattern { "," Pattern } ")" | Path "{" Ident ":" Pattern { "," Ident ":" Pattern } "}"
```

`prev` / `delay` / `vdelay` / `sample_rate` は普通の呼び出しとして解析し、意味は M3 で与える。`a..b` は `for` と `par` の見出しの中でだけ `Expr ".." Expr` として読む。

受け入れ: 計画 §3 M1 の通り。加えて、否定例が全て所定のコードで落ち、`fmt` が §17 の例を変えない。

### M2 名前解決と核の型検査（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T2-1 | パッケージとモジュール | S-11。`onsa.toml` の `[package]` と `[dependencies]`（第 1 期は `std` だけ、D-07 で埋め込み）。ファイルからモジュール木、`use`（グロブなし、`pub use`）、循環 E0310、可視性（`pub` / `pub(pkg)` / 無指定）、prelude | M |
| T2-2 | 項目の収集とシグネチャ | 全モジュールの項目を集め、型とシグネチャを解決する。組込み型の表、ジェネリックの引数（型、`const N: U32`、効果行変数）、引数モード、`rt`、効果行（D-08: `Alloc` 以外は E0200）、struct / enum / 別名、`const`、`impl`（固有メソッド、関連関数、関連定数）、flow の **シグネチャ**（入出力のレート型、`@param`）と名前空間の項目（§11.6 の型・定数・関数。本体の検査は M3）、`test`。trait の定義と `impl Tr for Ty` は E0200（組込みの trait 名は境界としてだけ使える）。`effect` / `handler` / `extern` / 利用者の `target` は E0200 | L |
| T2-3 | 名前の規則 | E0320（S-01）、E0305（flow と同名の宣言）、E0306（S-16）、名前の種別の表（§2.3）に基づく解決（`Fs.read` は型の関連関数、`fs.read` はモジュール） | S |
| T2-4 | 種と配置 | `Kind` の計算、`layout`（§3.3）。`[T; N]`、タプル、struct、enum（タグ + 最大の列挙子、タグは `U8` / `U16` / `U32` のうち最小）、`Option` / `Result` | S |
| T2-5 | 本体の型検査 | §4.7 の推論。リテラルの制約付き型変数、期待型の下向き伝播、E0405 / E0406 / E0408 / E0420。演算子（群ごとに許す型。`+%` 系は整数だけ、`&& \|\|` は `Bool`、ビット演算は整数）、比較、`as` の許す対の表（§3.3）、変換メソッド（`narrow_*`、`round_f32` / `round_f64`、`trunc_*`、`trunc_*_sat`、`to_bits` / `from_bits`）、`checked_*` / `div_euclid` / `rem_euclid`、フィールド・添字・タプルの添字、struct / 配列 / タプルのリテラルと `[e; N]`、`if` / `match`（網羅性 E0501。enum、`Option`、`Bool`、タプル、リテラルは `_` が要る）、`for`（範囲、配列、`Span` の借用の反復。`move` の反復は E0200）、`while`、`return` / `break` / `continue`、`?`（`Option` / `Result`）、関連定数 `F32.PI` / `T.ZERO`、`assert`、型付きホール `_` | L |
| T2-6 | ジェネリクス | 呼び出しの引数と期待型からの具体化、組込みの境界（`Num` `Float` `PartialEq` `PartialOrd` `Eq` `Ord` `Copy` `Dup` `?Dup`）の検査、`const N` の等値、E0406。具体化の要求を記録して M3 の単相化に渡す | M |
| T2-7 | 第二級の値とクロージャ | `Span` を引数の型にだけ許す（E0710）。無名 `fn` は期待型のある引数の位置にだけ書け、捕捉は Copy の値だけ（`inout` 引数と Affine の捕捉はエラー）。`std.array.from_fn` と S-12 の `Span` メソッドを組込みとして解決 | M |
| T2-8 | 引数モードと排他性 | 場所（place）の解析。`inout` には `var` / `inout` 引数とそのフィールド・要素だけ（借用束縛は不可）。E0702（同じ呼び出しで重なる `inout`。フィールドが異なれば重ならず、配列の添字どうしは重なる）、E0711、E0713 / E0714、§5.4 の借用束縛（`let y = x.f` が借用引数から派生していれば借用）、Affine の移動後の使用（分岐を考慮した定義済み解析。第 1 期の Affine は flow の状態と `Buf` だけ） | L |
| T2-9 | rt | E0901（rt から非 rt の呼び出し）、E0902（効果行の `Alloc`）、E0903（モジュール内の呼び出しグラフの閉路） | S |
| T2-10 | スコープ | E0304（見えている束縛と同じ名前）、兄弟スコープの許可 | S |
| T2-11 | `const` | 初期化式がリテラルと集成体のリテラルだけのものを評価（関数呼び出しは M3 の T3-9）。参照は `ConstId` | S |
| T2-12 | `onsa check --json` | 関数ごとに最初のエラー、全関数分を一度に。`found` と `fixes` を全コードで埋める | S |

受け入れ: 計画 §3 M2 の通り。§17.6 `Poly` は flow の本体を除いて検査が通る（`voice.State` などは T2-2 の名前空間の項目で解決できる）。

### M3 flow の検査と降下、インタプリタ（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T3-1 | flow の検査 | 本体の制限 E0806、名前の順序と因果性 E0801（`prev` 系の第 1 引数だけが前方参照）、レートの推論（`定数 < Init < Ctl < Sig` の最大値。`let` の注釈による昇格）、E0810（値型は Copy。境界の入れ子の配列）、E0813 / E0814、`delay` の E0807（`N = 1`）/ E0808（長さが定数でない）と `N >= 2` / `MAX >= 1`、呼び出しの形 E0811 / E0812 と E0805（効果を持つ fn）と非 rt fn の `Init` 制限、S-04 の E0815、`par`（`N` は定数、`i` は `Init` の `U32`）、`sample_rate()`、`match` の点ごとの意味 | L |
| T3-2 | Core IR | §3.4 の定義、`verify`、テキスト出力 `onsa dump --core` | M |
| T3-3 | fn の降下 | AST → Core。演算子を型付きの命令に（`+` は `Checked`、`+%` は `Wrap`、`+\|` は `Sat`）、添字を検査付きに、`?` を `Switch` に、`for` の範囲を `ForRange` に、配列と `Span` の反復を添字のループに、無名 `fn` の引数（`array.from_fn`）は呼び出し先の組込みに展開（インライン）、集成体を返す関数は `sret` | M |
| T3-4 | 単相化 | T2-6 の要求から、到達する具体化だけを生成。名前は `clamp[F32]` → `clamp__F32` | S |
| T3-5 | flow の降下 | §3.5 と D-03。状態の struct（S-05 の順序、S-06 の名前）、`Config` / `Params` / `Out`、`init` / `reset` / `ctl` / `tick` / `process` / `process_inplace` / `render` / `params_default`、`prev` の保存順、`delay` / `vdelay` の §11.4 の演算順の展開、サブインスタンス、`par` | L |
| T3-6 | 配置と大きさ | `layout` で `SIZE` / `BULK_SIZE` / `ALIGN`。`bulk_threshold`（マニフェストのターゲットから。無指定なら全て fast）で bulk へ分ける。bulk のポインタを fast の先頭に置く | S |
| T3-7 | インタプリタ | Core を直接実行する木歩き。値は `enum Value`（スカラ、集成体は `Vec<Value>`、`Span` は（バッファの参照、範囲）、`Buf` はヒープ）。検査付きの演算と添字は Rust の `checked_*` で、panic は `Err(Panic { msg, span })`。`Prim` は Rust の `f32` / `f64` のメソッドに対応付ける（`exp` `ln` `sin` ... は Rust が libm を呼ぶ。`fmod` は `%`）。F32 の演算は `f32` のまま（縮約されない） | M |
| T3-8 | `onsa test` | `test` 項目を実行。`assert` の失敗と panic はそのテストの失敗（S-16 の形）。`render` / `impulse` / `energy` / `assert_near`（D-08、std の宣言は T3-10）。`--json` | S |
| T3-9 | `const` の評価 | 関数呼び出しを含む初期化式をインタプリタで評価。E0407（第 1 期は Copy だけ） | S |
| T3-10 | `std` の最初の版 | `std/math.onsa`（D-07、S-09。宣言だけ）、`std/dsp.onsa`（`sum`、`db_to_amp`）、`std/dsp/test.onsa`（`impulse` `energy` `assert_near` `magnitude_at`）、`std/array.onsa`（`from_fn`）。Onsa で書けるものは Onsa で書く | S |
| T3-11 | `onsa interface <mod>` | 公開シグネチャ、種、大きさ、効果、`rt`、`@param`、flow の生成 API（§11.6 の形で表示）。`--json` | S |
| T3-12 | `onsa graph <flow>` | DOT。ノードは `let` とインスタンス（名前は S-06）、辺は参照、`prev` 系の辺は破線、レートで色分け。`--svg` は `dot` があれば呼ぶ | S |

受け入れ: 計画 §3 M3 の通り。加えて `onsa dump --core` の出力が golden テストにある。

### M4 C バックエンドと export（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T4-1 | `runtime/c/onsa.h` | `onsa_param_info`（`name` `id` `min` `max` `default_` `step` `unit` `scale` `label`）、panic の設定マクロ（`ONSA_PANIC_POISON` / `TRAP` / `RESET` / `HALT`）と差し替え可能な `onsa_panic(const char* msg, const char* file, uint32_t line)`、検査付きの整数演算（`__builtin_*_overflow`、MSVC は手書きの比較）、`onsa_span_f32 { float* ptr; uint32_t len; }`、`#pragma STDC FP_CONTRACT OFF`、`_Static_assert(FLT_EVAL_METHOD == 0, ...)` | S |
| T4-2 | Core → C | 型（struct、enum は `struct { tag; union }`、配列は struct で包む、タプルは struct）、名前（D-10）、関数（`sret`、借用の集成体は `const T*`、`inout` は `T*`、スカラは値）、文、式（F32 の各演算を `(float)` で囲む）、`Checked` / `Wrap` / `Sat`、添字の検査、`Switch`、`Panic`、`Prim` の対応表（libm の `expf` など）、`const` は `static const` | L |
| T4-3 | flow の API | 内部の 5 関数と、export の wrapper（§14.2 の形）: `_init(s, bulk, cfg の各フィールド, sample_rate)`、`_reset`、`_params_default`、`_process(s, p, 入力..., 出力..., frames)` の戻り値（`poisoned` → 1、部分的な重なりと出力どうしの一致 → 2）、`@param` の範囲への飽和、`param_info` の表、`_new` / `_free`（`provides` に `Alloc` があるとき）、ヘッダ（`SIZE` / `BULK_SIZE` / `ALIGN` と `_Static_assert(sizeof(...) == ...)`） | M |
| T4-4 | panic の実現 | `poison`: wrapper で `setjmp`、`onsa_panic` が `longjmp`、出力をゼロで埋めて `poisoned = true`。`jmp_buf` は状態の末尾（S-05）。`trap` / `reset` / `halt`: `__builtin_trap()` / ターゲットのフック / `for(;;)`。`reset` で `poisoned` を解く | S |
| T4-5 | `onsa build --target <name>` | マニフェストの `[targets.*]`（`kind` = `staticlib` / `source`（`lang = "c"`）、`platform`、`numeric`、`provides`、`panic`、`panic_messages`、`memory.bulk_threshold`）、`[export]`（`prefix`、`flows`、`fns`。E0809 と E0610 はここで検査）。`target/<name>/` に `.c` / `.h` を出し、`platform` がホストなら `cc` を呼ぶ（フラグ: `-std=c11 -O2 -ffp-contract=off -fno-fast-math`、x86-32 は `-msse2 -mfpmath=sse`、MSVC は `/fp:strict`）、`ar` で `.a`。クロスは C の出力だけ | M |
| T4-6 | golden | `tests/golden/<name>.c` と生成物の差分。`UPDATE_GOLDEN=1` で更新 | S |
| T4-7 | 適合性の基盤 | `tests/conformance/<name>.onsa`（`render` を呼ぶ `test` だけを持つ）。ハーネスは interp で `Out` を得て、同じ入力で C（生成した小さなドライバ）を走らせ、サンプル列をバイト比較する。超越関数を通る flow は S-14 の判定で許容誤差（M5 で確定。M4 では同じ libm なので一致を期待する） | M |
| T4-8 | §17.5 の例 | `examples/voice_host/`: `daisy` 相当のターゲット定義（ホスト向けに `platform` を変えたもの）で staticlib を作り、C のホストが WAV に書く | S |
| T4-9 | NRVO と移動 | `sret` の構築先の決定（§12.7 の条件）。閾値以上のコピーの箇所を記録（`audit --memory` は M9） | S |

受け入れ: 計画 §3 M4 の通り。

### M5 `std` と適合性テスト（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T5-1 | 精度の測定 | D-12 の表と ULP の測定。interp（Rust）、C（ホストの libm）の結果を記録。2 ULP を超える関数の一覧を作り、超える環境では D-11 の Onsa 実装に束縛を切り替える | M |
| T5-2 | `std.math.soft` | D-11。musl からの移植と、精度表に対する検査 | M |
| T5-3 | `std.dsp` の完成 | S-10。`magnitude_at`、`sum` の順序の固定を確認する conformance | S |
| T5-4 | `std.test` | `check` と `gen`（D-08 と同じく `test` の本体でだけ使える組込み。`Random` はテスト名から決めた種。`--seed`）。`Gen[T]` の型はインタプリタの内蔵 | M |
| T5-5 | `onsa test --flows` | export される各 flow について、`@param` の角と無作為の内点（既定 8 点）× 入力（無音・インパルス・一様雑音）を interp で走らせ、出力が有限で panic しないことを検査。`--backends` と組み合わせ可 | S |
| T5-6 | `onsa test --backends all` | T4-7 のハーネスを `tests/conformance` 全体と `--flows` の掃引に適用。S-14 の判定 | S |
| T5-7 | `onsa primer --std` | 言語の要約（仕様 §2〜§11 の圧縮版を `docs/primer.md` に手で書き、埋め込む）と `std` の `interface` | S |
| T5-8 | 生成テスト | `tests/fuzz`: 小さな flow（`prev` / `delay` / 四則）を乱数で生成し、interp と C を比較。CI では短時間だけ | S |
| T5-9 | CI | D-14 の `conformance` と `precision` ジョブ | S |

### M6 WASM バックエンド（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T6-1 | Core → WASM | `wasm-encoder`。線形メモリに状態（export する flow ごとに固定のオフセット。`SIZE + BULK_SIZE` に加え、`process` 用の入出力バッファ領域）、`init` / `reset` / `process` / `params_default` を export、`f32` 命令は IEEE のまま、検査付き演算はトラップ（`unreachable`）、`@param` の表は JSON の custom section `onsa.params`、D-11 の libm | L |
| T6-2 | `wasm-worklet` | `kind = "wasm-worklet"`: `.wasm` と glue（`AudioWorkletProcessor` の JS。パラメータの書き込み、トラップを捕まえて `poisoned`、`reset` の呼び出し）、最小の HTML | M |
| T6-3 | 適合性 | T4-7 のハーネスに Node（`WebAssembly.instantiate`）を追加 | S |

### M7 IDE の核（L）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T7-1 | `onsa_lsp` | `lsp-server`。開いているファイルの診断（保存ではなく変更時）、ホバー（型・レート・種・大きさ・効果・`rt`）、定義へジャンプ、`fmt`（`textDocument/formatting`）、flow の状態の一覧（独自の要求 `onsa/interface`） | L |
| T7-2 | `onsa_web` | `wasm-bindgen` で `check(json) -> json`、`build_wasm(package) -> bytes`、`interface`、`graph`、`fmt` を公開。ブラウザの IDE はこれと T6-2 の glue で動く | M |
| T7-3 | `onsa play <flow>` | D-13 | M |
| T7-4 | `onsa probe <flow>.<name>` | 降下の段で `let` 名を追加の出力に昇格させる（`process` に `inout probe_<name>: Span[T]` を足す）。CLI は WAV / CSV に書く。`play --probe` で端末に波形の概形 | M |
| T7-5 | ホットリロード | `play` の中で、再コンパイル後に `layout` を比べ、名前と型が一致するフィールドを旧状態からコピーし、それ以外は `init` の値。§19 の「型の変わったフィールド」は `init` で初期化 | S |
| T7-6 | VS Code 拡張 | 構文の色分け（TextMate）と LSP クライアントの最小構成 | S |

### M8 JavaScript への変換（M）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T8-1 | Core → JS | flow ごとに 1 クラス。状態は `Float32Array` / `Int32Array` などの型付き配列を `layout` のオフセットで共有する 1 つの `ArrayBuffer`。F32 の各演算の後に `Math.fround`。`I64` / `U64` は E0200。`@param` の表は定数のオブジェクト。`kind = "source"`, `lang = "js"` | M |
| T8-2 | 適合性 | Node で実行し、4 者で比較 | S |

### M9 第 1 期の締め（S）

| ID | 作業 | 内容 | 規模 |
|---|---|---|---|
| T9-1 | `explain` | 全コードの本文（原因、例、直し方）。D-04 の検査を有効にする | M |
| T9-2 | `onsa audit` | `--memory`（状態の内訳、T4-9 の移動の一覧）、`--stack`（rt の呼び出しグラフの最大深さ × フレームの推定）、`--panics`（export の rt の経路にある検査付きの演算・添字・`unwrap`・非飽和の変換） | M |
| T9-3 | 仕様への反映 | `D` と `S` の決定、`primer`、`README` | S |

---

## 5. 診断コードの実装表

| コード | 内容 | 検出する段 | M |
|---|---|---|---|
| E0001 / E0002 | 不正な文字・リテラル / 予期しないトークン（S-18） | 字句・構文 | M1 |
| E0003 | `else` の位置 | 構文 | M1 |
| E0010 | 群の混在 | 構文（後段） | M1 |
| E0011 | `as` を二項の中に | 構文（後段） | M1 |
| E0012 | 前置の重ね | 構文（後段） | M1 |
| E0020 | 既存言語の書き方（S-02） | 字句・構文 | M1 |
| E0200 | この版では未対応（S-03） | 名前解決・型 | M2 |
| E0304 | シャドーイング | 名前解決 | M2 |
| E0305 | flow と同名の宣言 | 項目の収集 | M2 |
| E0306 | 同名の `test`（S-16） | 項目の収集 | M2 |
| E0310 | モジュールの循環 | モジュール | M2 |
| E0320 | 命名規則（S-01） | 構文 | M1 |
| E0405 | リテラルの型が決まらない | 型 | M2 |
| E0406 | 型パラメータが決まらない | 型 | M2 |
| E0407 | `const` の結果の種 | `const` の評価 | M3 |
| E0408 | リテラルが範囲外 | 型 | M2 |
| E0420 | 対象の型が未解決 | 型 | M2 |
| E0501 | 網羅性 | 型 | M2 |
| E0610 | export の効果が `provides` に無い | `build` | M4 |
| E0611〜E0615, E0620, E0630, E0640〜E0642, E0650 | 効果・handler・ポリシー・並行 | — | 第 2 期 |
| E0702 | `inout` の重なり | モード | M2 |
| E0710 | 第二級の値の位置 | 型 | M2 |
| E0711 | 借用の Affine を `move` | モード | M2 |
| E0713 / E0714 | `!` の有無 | 型 | M2 |
| E0801 | 前方参照 | flow | M3 |
| E0805 | 効果を持つ fn の呼び出し | flow | M3 |
| E0806 | 本体の制限 | flow | M3 |
| E0807 / E0808 | `delay` の長さ | flow | M3 |
| E0809 | export の `Ctl` に `@param` が無い | `build` | M4 |
| E0810 | 値型が Copy でない、境界の入れ子 | flow | M3 |
| E0811 / E0812 | `~` の有無 | 名前解決 | M2 |
| E0813 / E0814 | `prev` 系の引数のレート | flow | M3 |
| E0815 | 引数のレートが入力より高い（S-04） | flow | M3 |
| E0901 | rt から非 rt | rt | M2 |
| E0902 | rt の効果行に `Alloc` | rt | M2 |
| E0903 | rt の再帰 | rt | M2 |
| E0904 / E0905 | rt と blocking / rt 効果 | — | 第 2 期 |
| E1010 | 核から `extern` に到達 | — | 第 2 期 |

第 1 期で実装するのは 40 コード。

---

## 6. 仕様の例の対応表

仕様の ```` ```onsa ```` ブロック（開始行）と、`tests/spec/` の置き場所、検査の深さ（D-05）、通るマイルストーン。断片は関数か `test` で包み、包んだ部分はブロックの外に置く（D-06 の照合は逐語の部分一致）。

| 行 | 節 | 内容 | ファイル | mode | M |
|---|---|---|---|---|---|
| 79 | §2.1 | コメント | `lex/comments.onsa` | check | M2 |
| 161 | §3.1 | 群（E0010 の否定例を含む） | `ops/groups.onsa` | check | M2 |
| 178 | §3.3 | 変換 | `ops/convert.onsa` | check | M2 |
| 260 | §4.4 | ユーザ定義型 | `types/user.onsa` | check | M2 |
| 283 | §4.5 | ジェネリクス | `types/generics.onsa` | check | M2 |
| 328 | §5.1 | 束縛 | `values/bind.onsa` | check | M2 |
| 380 | §5.4 | `total_len`（`Array[Str]`） | `values/borrow_for.onsa` | parse | 第 2 期 |
| 394 | §6.1 | `mean`（`Array`） | `fn/mean.onsa` | parse | 第 2 期 |
| 411 | §6.2 | `Point` のメソッド | `fn/methods.onsa` | check | M2 |
| 428 | §6.3 | `Show` | `fn/trait_show.onsa` | parse | 第 2 期 |
| 448 | §6.4 | `@derive`（`Hash` `Show` は E0200 のマーカ） | `fn/derive.onsa` | check | M2 |
| 463 | §6.6 | `const`（`make_sine_table` を補う） | `fn/const.onsa` | check | M3 |
| 476 | §7 | 制御（断片。`...` を含む） | `control/forms.onsa` | none | — |
| 509 | §8.1 | 効果 | `effects/decl.onsa` | parse | 第 2 期 |
| 528 | §8.1 | `map`（`...`） | `effects/map.onsa` | none | — |
| 557, 577, 602 | §8.3〜8.5 | handler（最上位の `let`）、arena、main（`...`） | `effects/{handler,arena,main}.onsa` | none | — |
| 618 | §9.1 | `line_count`（`...`） | `effects/result.onsa` | none | — |
| 663 | §10 | `soft_clip` | `rt/soft_clip.onsa` | check | M2 |
| 709 | §11.2 | `one_pole` | `flow/one_pole.onsa` | check | M3 |
| 791 | §11.5 | `unison`（`saw` を補う） | `flow/unison.onsa` | check | M3 |
| 815 | §11.6 | 生成 API（擬似） | `flow/generated_api.onsa` | none | — |
| 856 | §11.7 | `gain` | `flow/gain.onsa` | check | M3 |
| 887 | §11.8 | `check` | `test/check.onsa` | parse → test | M5 |
| 1073, 1090 | §14.1 | `extern` と `Conv` | `ffi/extern.onsa` | parse | 第 2 期 |
| 1118 | §14.2 | `onsa_version` | `ffi/export_fn.onsa` | check | M2 |
| 1175 | §15.2 | `target` | `module/target.onsa` | parse | 第 2 期 |
| 1281 | §16 | `std.task` のシグネチャ（本体なし） | `concurrency/task_sigs.onsa` | none | — |
| 1294 | §16 | `run` | `concurrency/run.onsa` | parse | 第 2 期 |
| 1320 | §16 | `on_audio`（最上位の文） | `concurrency/on_audio.onsa` | none | — |
| 1340 | §17.1 | `gcd` | `examples/gcd.onsa` | test | M3 |
| 1360 | §17.2 | `line_count` のテスト | `examples/line_count.onsa` | parse | 第 2 期 |
| 1393, 1425, 1467 | §17.3〜17.4 | `resonator`、`saw` / `smooth` / `voice`、`echo`（同じモジュール） | `examples/voice.onsa` | test | M3 |
| 1487 | §17.4 | `render_vowel` | `examples/render_vowel.onsa` | parse | 第 2 期 |
| 1530 | §17.6 | `Poly`（`voice.onsa` と同じファイル） | `examples/voice.onsa` | check | M3 |

M1 では `none` 以外の全てのファイルが `parse` として通ることを確認する（`mode` の指定は M2 以降の検査の深さ）。断片を包むためのコード（`fn groups(...) {`、`Point` の定義、`make_sine_table`、`saw`）はブロックの外に置いてある。M0 でこの収録を済ませた（T1-11 の前倒し）。否定例のマーカは、その診断を実装するマイルストーンで足す。

---

## 7. 着手の順

最初の 10 作業。T0-5 と S-15 以外は仕様の決定を待たない。

1. T0-1 ワークスペース
2. T0-2 `onsa_diag`（§5 の全コードを登録）
3. T0-3 `onsa_cli` の骨格
4. T0-4 `tests/spec` のランナー（D-05 を仮採用）
5. T0-6 CI
6. T1-1 字句解析器
7. T1-2 AST
8. T1-3 宣言の構文解析
9. T1-4 文とブロック（文の区切り）
10. T1-5 式（群の検査）

S-01 / S-02 / S-07 / S-08 / S-15 は M1 の中で要るので、6 の前に決める。D-01 / D-02 / D-05 / D-06 はこの 10 作業の形を決めるので、最初に決める。
