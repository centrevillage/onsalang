# Onsa 実装計画

- 対象: [`onsa-lang-spec-0.3.md`](../onsa-lang-spec-0.3.md) §20 の第 1 期（移植可能な核）を中心に、第 2 期・第 3 期の輪郭まで（計画の節番号は 0.2 と 0.3 で同じ）
- 日付: 2026-10-01
- 前提のレビュー: [`review-draft-0.2.md`](review-draft-0.2.md)。`C-` / `G-` / `I-` / `P-` はそのレビューの ID
- 作業の詳細: [`implementation-tasks.md`](implementation-tasks.md)。各マイルストーンを作業（`T`）に分け、実装の判断（`D`）と仕様の空白（`S`）を一覧にしたもの

---

## 0. 方針

1. **構文は最初から言語全体を解析する。** 第 1 期の意味検査は核だけだが、fn 世界の構文（効果、handler、`Str` など）も構文解析と名前解決は通し、核の外の機能は「この版では未対応」の診断（E02xx）で落とす。LLM が書いたコードに構文エラーでなく正しい位置の診断を返せる。
2. **flow はコンパイラの前段で fn 世界に降下する。** flow から `State` 構造体・`init` / `reset` / `process` 関数を Onsa Core の普通の宣言として生成し、バックエンドは flow を知らない。バックエンドを増やすときに flow の意味を再実装しない。
3. **インタプリタが意味の基準。** `onsa test` と `--backends all` の比較元はインタプリタ。Rust の `f32` 演算は IEEE で縮約されないので、`strict` の基準にできる。
4. **仕様の例を最初の回帰テストにする。** §17 の例と、各節の肯定・否定の例を `tests/spec/` に切り出し、期待する診断コードを付ける（P9 の検証）。
5. **決めていないことは実装しない。** レビュー §6 の「実装の前に決めること」を各マイルストーンの着手条件にする。

---

## 1. リポジトリ構成

Rust のワークスペース。クレートは責務ごとに分け、`wasm32-unknown-unknown` でもビルドできるものと、できないもの（ファイル I/O、音声出力、LSP）を分ける。

```
onsalang/
├── Cargo.toml                 ワークスペース
├── crates/
│   ├── onsa_syntax/           字句・構文解析、AST、スパン、fmt（wasm 可）
│   ├── onsa_diag/             診断コードの登録簿、JSON 出力、explain の本文（wasm 可）
│   ├── onsa_sema/             名前解決、型、効果、rt、排他性、flow の検査（wasm 可）
│   ├── onsa_core/             Onsa Core IR の定義と検証、flow の降下、単相化（wasm 可）
│   ├── onsa_interp/           Core のインタプリタ（wasm 可）
│   ├── onsa_backend_c/        C11 の出力（wasm 可。文字列を返すだけ）
│   ├── onsa_backend_wasm/     WASM の出力（wasm 可）
│   ├── onsa_backend_js/       JavaScript の出力（第 1 期の末）
│   ├── onsa_driver/           マニフェスト、ターゲット、パッケージの読み込み、パイプラインの束ね
│   ├── onsa_cli/              `onsa` コマンド
│   ├── onsa_lsp/              LSP サーバ
│   └── onsa_web/              wasm-bindgen で IDE へ公開する API（check / build / render）
├── std/                       標準ライブラリ（Onsa で書く）
│   ├── math/                  exp, cos, sin, ... （Onsa）
│   ├── dsp/                   sum, db_to_amp, test.{impulse, energy, ...}
│   └── ...
├── runtime/
│   └── c/onsa.h               生成コードが include する共通定義（param_info, panic フック）
├── tests/
│   ├── spec/                  仕様の例。期待する診断は行末の `//~ E0010`（詳細 D-05）
│   ├── golden/                生成 C / WASM の golden
│   └── conformance/           render の出力のビット一致（interp vs C vs WASM）
├── examples/                  voice, echo, poly（仕様 §17）
└── docs/
```

`.gitignore` に `target/` を足す（現在は C++ 向けの内容だけ）。

---

## 2. 中核の設計判断

実装の最初に固定するもの。後から変えると全段に波及する。

### 2.1 AST と Onsa Core の二層

| 層 | 役割 | 持つもの |
|---|---|---|
| AST（`onsa_syntax`） | ソースの忠実な表現。fmt、diff、LSP が使う | 全てのトークンのスパン、コメント、属性、flow |
| Onsa Core（`onsa_core`） | 検査済み・型付き・単相の正準 IR。全バックエンドの入力 | 型が全て決まった式、明示の `drop`（第 2 期）、構造化された制御（`if` / `while` / `for` の範囲）、flow 無し |

Core の性質:

- 関数は全て単相（ジェネリクスは単相化して落とす）。
- 式に暗黙のものが無い。レートの昇格、点ごとの適用、演算子の trait 脱糖は Core の前で解決する。
- `panic` は Core の命令（`check_add`、`check_index`、`panic(msg_id)`）。バックエンドが各ターゲットの方法で出す。
- 検証器（`onsa_core::verify`）を持ち、型と所有権の不変条件を各段の後で検査する。デバッグビルドでは常に走らせる。

### 2.2 flow の降下

`flow f(入力) -> 出力 { let ...; e }` を次へ落とす。

```
struct f.State {
  // Init レートの let のうち、Ctl / Sig から参照されるもの
  // prev: T、delay(N): [T; N] + U32、vdelay(MAX): [T; MAX + 1] + U32
  // サブインスタンス: g.State（名前は let の名前。無名は g_0, g_1, ...）
  // par: [g.State; N]
  poisoned: Bool            // export の境界で使う
}
struct f.Config { Init 入力 }
struct f.Params { Ctl 入力 }
fn    f.init(cfg: f.Config, sample_rate: F32) -> f.State
rt fn f.reset(inout s: f.State)                       // 遅延と prev を init 値に戻し、サブインスタンスも reset。Init の値は保つ
rt fn f.ctl(inout s: f.State, p: f.Params)            // Ctl レートの let を順に評価（ブロックに 1 回）。Sig から参照されるものは状態へ
rt fn f.tick(inout s: f.State, Sig 入力の値...) -> 出力の値   // Sig レートの let を順に評価する 1 サンプル分。遅延を進める
rt fn f.process(inout s: f.State, p: f.Params, Sig 入力: Span[T]..., inout 出力: Span[T]...) {
  // ctl を 1 回、for i in 0..frames { 入力を全て読む、tick、出力を全て書く }（詳細 D-03）
}
rt fn f.process_inplace(inout s: f.State, p: f.Params, inout 入出力: Span[T]...)  // 入出力の形が一致するときだけ
fn    f.render(...) uses {Alloc}                      // process を 1 回呼ぶ。Sig 入力があれば frames 無し
```

- **レート解析**: 各 `let` のレートは式のレートの最大値。`prev` / `delay` / `vdelay` の結果と flow の呼び出しの結果は常に `Sig`。`par` の `i` は `Init`。
- **因果性**: 名前の順序の検査（§11.2）。`prev` 系の第 1 引数だけが前方参照を許す。
- **状態の配置**: フィールドは宣言順（`let` の順）、自然アラインメント、並べ替えなし（G-07）。`bulk_threshold` 以上の配列は bulk 領域へ。bulk 領域のアドレスは fast 領域の先頭にポインタとして持つ（C API の `init` が受け取る）。`SIZE` / `BULK_SIZE` / `ALIGN` をここで計算し、生成コードに `_Static_assert` を出す。
- **`par`**: 配列 + ループに落とす（仕様 §11.5。`i` は `Init` レートの値）。
- **遅延の実装**: 仕様 §11.4 のリングバッファと演算順をそのまま実装する。全バックエンドで同じ演算順にする。
- **panic**: Core の `check_*` 命令。`process` の中では、バックエンドが「中断して poisoned」を実現する（I-01）。

### 2.3 型検査

- 関数単位。シグネチャは完全注釈（P1）なので、呼び出し先はシグネチャだけを見る。
- 本体は仕様 §4.7 の形: 文の順の一方向推論、単一化変数、期待型の下向き伝播。リテラルは `IntLit` / `FloatLit` の制約付きの型変数で、関数の終わりに未解決なら E0405。
- `.` `[]` `as` `match` `?` 関数値の呼び出しの対象は、その時点で解決済みを要求（E0420、§4.7）。
- 演算子は第 1 期では組込み数値型に直接型付けする（trait の脱糖は第 2 期で trait を入れたときに同じ結果になるよう、`Add.add` の形で Core に出しておく）。
- 第 1 期のジェネリクス: `const N: U32` と、組込みの `Num` / `Float` / `Ord` / `Eq` 境界だけ（`std.dsp.sum[const N]` などに要る）。ユーザ定義 trait は第 2 期。

### 2.4 数値

- F32 / F64 の演算は Core で型ごとに別の命令にし、バックエンドは混ぜない。
- `sqrt`、`floor` / `ceil` / `trunc` / `round`、`abs`、`min` / `max`、`fmod` はビット一致するプリミティブ。超越関数（`exp` / `cos` / `sin` / `log` / `exp2` / `pow` / `tanh`）も各環境のプリミティブ（C の libm、JS の `Math`、WASM は同梱の libm）に対応付け、精度目標 2 ULP を検査する（仕様 §13.4）。満たさない環境の関数だけ Onsa 実装に差し替える。
- C: `#pragma STDC FP_CONTRACT OFF`、`_Static_assert(FLT_EVAL_METHOD == 0)`、F32 の各演算を `(float)` で囲む。ターゲット定義にコンパイラフラグ（`-ffp-contract=off -fno-fast-math`、MSVC は `/fp:strict`）を含める（仕様 §13.4）。
- WASM: 命令がそのまま IEEE。追加の処置なし。
- JS: F32 の各演算の後に `Math.fround`。F64 はそのまま。`I64` / `U64` は第 1 期では JS の対象外（E02xx）。

### 2.5 診断

- `onsa_diag` に全コードを登録する（コード、英語の message テンプレート、explain の本文、修正候補の形）。仕様の表（§18.1）の範囲を守る。
- 全ての診断は JSON（§18.1 の形）と人間向けの両方を出す。
- 関数ごとに独立に検査し、関数ごとに最初のエラーを報告する（P-01。仕様の決定に従う）。
- 既存言語の書き方（`&mut`、`<T>`、`::`、`;`、`i32`、`proc`、`+ ~ _`）の修正候補は、字句・構文の段で検出する専用の規則にする。

---

## 3. マイルストーン

各マイルストーンに「成果物」「受け入れ条件」「先に決める仕様」「規模」を付ける。規模は相対（S: 数日、M: 1〜2 週、L: 3 週以上）の目安で、一人で実装する場合。

### M0 基盤（S）

- 成果物: ワークスペース、`onsa_diag` の登録簿と JSON 出力、CI（fmt / clippy / test / wasm32 ビルド）、`tests/spec` の実行基盤（`.onsa` + `.expect` を比較するテストランナー）。
- 受け入れ: 空のソースに `onsa check --json` が `[]` を返す。CI が緑。
- 決める仕様: なし。

### M1 字句・構文解析と fmt（M）

- 成果物: 言語全体の字句解析器と構文解析器（§2〜§7、§8、§11、§14、§15.2 の宣言）、AST、`onsa fmt`、`onsa diff --ast`。文の区切り（§2.5）、演算子の群（E0010 / E0011）、`~`（字句として `IDENT ~ (`）、`else` の位置（E0003）、既存言語の書き方への修正候補。
- 受け入れ: 仕様の全てのコード例（`...` を含むものを除く）が解析できる。`fmt` が冪等（`fmt(fmt(x)) == fmt(x)`）で、仕様の例を変えない。E0010 / E0011 / E0003 の否定例が落ちる。
- 決める仕様: なし。P-02（レシーバの `!`）、G-03（タプル・配列リテラル・パターン・関連定数・前置/後置の結合・`_`）、C-04、C-05、C-08 は 0.3 で決定済み。

### M2 名前解決と核の型検査（L）

- 成果物: モジュールと `use`（§15.1、循環 E0310）、名前の種別（§2.3）、核の型検査（§2.3 の方針）、シャドーイング E0304、`as` の規則（§3.3）、`const`（§6.6。初期化式はインタプリタで評価するので M3 と同時）、引数モードと排他性（§5.2、E0702）、第二級の値（§5.3、E0710）、借用束縛（§5.4、E0711）、`rt` の規則 3〜4（§10。効果は第 1 期では常に空）、型付きホール、`onsa check --json`。核の外の機能（`Str`、`Array`、効果、handler、trait の定義）は E02xx「未対応」。
- 受け入れ: §17.1、§17.3〜§17.6 の例が `check` を通る（§17.2 は効果を使うので除く）。各節の否定例が所定のコードで落ちる。E0405 / E0420 / E0702 / E0710 / E0304 / E0903 のテストがある。
- 決める仕様: なし（G-05 は 0.3 で決定済み、E0406）。

### M3 flow の検査と降下、インタプリタ（L）

- 成果物: flow の検査（順序と因果性 E0801、レート E0810、`delay` の規則 E0807 / E0808、呼び出しの形 E0811 / E0812 / E0805、本体の制限 E0806、`@param` E0809）、§2.2 の降下、状態の配置と `SIZE` / `BULK_SIZE` / `ALIGN` の計算、`onsa interface`（型の種と大きさ、flow の生成 API）、`onsa graph`（DOT）、Core のインタプリタ、`test` ブロックの実行（`onsa test`）、`render`。
- 受け入れ: §17.3 の `resonator decays` と、§17.4 / §17.6 を使ったテストがインタプリタで通る。`echo` の `BULK_SIZE` が `bulk_threshold = 4096` で 384004 前後（`[F32; 96001]` の配置に従う値）になる。`graph` が §17.4 の `voice` に対して `saw` / `resonator` × 2 / `smooth` のノードを出す。
- 決める仕様: なし。G-04（遅延の状態と演算順は仕様 §11.4、`process_inplace` と入出力の読み書きの順序は §11.6）と G-07（配置規則、§12.4）は 0.3 で決定済み。
- 注意: 超越関数はインタプリタでは Rust の `f32` / `f64` のメソッド（libm 相当）で計算する。C との比較は、超越関数を通る出力については許容誤差付きになる（仕様 §13.4）。

### M4 C バックエンドと export（L）

- 成果物: Core → C11。関数、Copy の struct / enum / 配列、`const`、flow の生成物、`onsa.h`、生成ヘッダ（§14.2。`frames` は `uint32_t`、C-06）、`@param` のメタデータ表、`[export]` と `prefix`、`_Static_assert` による `SIZE` / `ALIGN` の検証、panic の実現（I-01。ホストは `setjmp`、組込みは `trap` / `reset` / `halt`）、`onsa build`（ターゲット `staticlib` / `exe` の C 出力と、ホストでのコンパイル）、整数の検査（`__builtin_*_overflow`）、§17.5 の C ホストの例のビルド。
- 受け入れ: §17.5 がビルドでき、`voice` の 48000 サンプルがインタプリタとビット一致する（conformance の最初のテスト）。panic が `poisoned` を返し、`reset` で復帰する。golden テスト（生成 C の差分）がある。
- 決める仕様: なし。I-01（panic。仕様 §9.2 の `panic` 設定）、I-02（コンパイル条件。§13.4）、I-04（返り値の構築。§12.7）は 0.3 で決定済み。
- 注意: 集成体を返す関数は常に出力ポインタで構築する（仕様 §12.7）。`init` の生成はこの規則で書く。NRVO の条件と、`audit --memory` の移動の列挙もここで実装する。

### M5 `std/math` と `std/dsp`、適合性テストの基盤（M）

- 成果物: `std/math`（各環境のプリミティブへの対応付け。`exp` `exp2` `log` `log2` `sin` `cos` `tan` `tanh` `pow` と、ビット一致する `sqrt` `floor` `ceil` `trunc` `round` `abs` `min` `max` `fmod`。WASM 用の同梱 libm）、精度のテスト（参照は正しく丸めた値、2 ULP 以内で判定。環境ごとの結果を記録し、超える関数は Onsa 実装に差し替える）、`std/dsp`（`sum`、`db_to_amp`、`test.{impulse, magnitude_at, energy, assert_near}`）、`std/test`（`check`、`gen`。テストランナーの決定的な `Random`）、`onsa test --flows`（`@param` の範囲での自動検査）、`onsa test --backends all` の仕組み（`render` の出力を interp と C で比較）、`onsa primer --std`。
- 受け入れ: §17 の全てのテストが interp と C でビット一致。`std/math` の各関数が精度目標を満たす。
- 決める仕様: なし（I-03 は 0.3 で決定済み。精度目標 2 ULP は仮決めで、M5 の測定で見直す）。

### M6 WASM バックエンド（M）

- 成果物: Core → WASM（核のみ。線形メモリに状態を置き、`init` / `reset` / `process` / `params_default` を export。`@param` の表は JSON の custom section）、`wasm-worklet` ターゲットの出力（AudioWorklet の glue JS を同梱）、トラップを glue で捕まえて poisoned にする。
- 受け入れ: conformance が interp / C / WASM の 3 者でビット一致。ブラウザで `voice` が鳴る最小のページがある。
- 理由: P-03。ブラウザの IDE に C のツールチェーンは無く、WASM は `strict` と相性が最も良い。

### M7 IDE の核（L）

- 成果物: `onsa_lsp`（診断、ホバーでの型・レート・種・大きさ、定義へジャンプ、`fmt`）、`onsa_web`（wasm-bindgen で `check` / `build_wasm` / `interface` / `graph` を公開）、`onsa play`（デスクトップは C でビルドして `cpal` 等で出力、`@param` から UI）、`onsa probe`（降下の段で指定した `let` を出力に追加する「プローブ出力」を生成し、IDE はそれを描画する）、ホットリロード（名前と型が一致するフィールドの引き継ぎ。`interface` の情報を使う）。
- 受け入れ: VS Code で仕様の例を開くと診断とホバーが出る。`play voice` でパラメータを動かしながら鳴る。`probe voice.f1` が波形を表示する。
- 決める仕様: §19 の「ホットリロードで型の変わったフィールド」は未決定のまま「`init` で初期化」で進める。

### M8 JavaScript への変換（M）

- 成果物: Core → JS（核のみ。`Float32Array` と `Math.fround`。クラス 1 つ = flow 1 つ）、`source` ターゲットの `lang = "js"`、conformance に JS を追加（Node で実行）。
- 受け入れ: 4 者でビット一致（I64 / U64 を使うものは JS を除外）。
- 位置付け: WASM が使えない環境と、生成コードを人間が読む用途。優先順位は M6 より低い。

### M9 第 1 期の締め（S）

- 成果物: `onsa explain` の本文を全コード分そろえる、`onsa audit --memory`（flow の状態の内訳）、`onsa audit --stack`（核は再帰が無いので呼び出しグラフの最大深さ × フレームの大きさ。C バックエンドのフレームの大きさは推定になるので「上限の推定」と表示）、仕様の 0.3 への反映（この計画で決めたこと）。

第 1 期の成果物で、仕様 §0.1 の「IDE での試聴、各言語へのトランスパイル（C / JS）、プラグインや組込み機器への組み込み（C の staticlib）」がそろう。CLAP / VST3 の `kind` は、C の staticlib を既存のプラグインの枠組みに入れる作業なので、第 1 期の中で M4 の後に追加できる（規模 M、独立）。

---

## 4. テスト戦略

| 種類 | 置き場所 | 内容 |
|---|---|---|
| 仕様の例 | `tests/spec/` | 各節の肯定例と否定例。期待する診断は行末の `//~ E0010`、先頭行の `//! mode:` で検査の深さ（詳細 D-05、D-06）。P9 の検証 |
| 単体 | 各クレート | 字句、文の区切り、演算子の群、レート解析、配置の計算、`fmt` の冪等性 |
| golden | `tests/golden/` | 生成 C / WASM / JS のテキスト差分。意図した変更だけが差分になる |
| conformance | `tests/conformance/` | `render` の出力を interp / C / WASM / JS で比較。`strict` ではバイト一致、`relaxed` は対象外 |
| 精度 | `std/math` | ULP 目標の検証 |
| 生成テスト | `tests/fuzz/` | 小さな flow を乱数で生成し、interp と C を比較（M5 以降）。演算の順序と丸めの差を機械的に見つける |
| 例 | `examples/` | §17 の `voice` / `echo` / `poly` を実際にビルドして鳴らす |

---

## 5. 第 2 期・第 3 期の輪郭

第 2 期（fn 世界）は仕様 §20 の 7〜9。順序の提案:

1. 効果と handler（末尾再開、証拠渡し）。`Alloc` 無しで動く `Log` / `Clock` / `Random` から。標準の効果は std の `effect` 宣言（S-74、下の持ち越しの一覧）。C-01、C-02、G-01 は 0.3 で決定済み。並行性は 2026-10-02 に削除し、実行文脈の登録（仕様 §16）に置き換えた。`std.sync` の同期型は Copy 要素の固定サイズの値で、ヒープを使わない。
2. `Alloc`、Shared 型（`Str` `Array` `Map` `Set`）、`Buf`、Perceus の参照カウント、`Drop`。ヘッダの形は仕様 §12.8（G-06 で決定済み）。
3. ユーザ定義 trait と演算子の脱糖、`derive`、`Iter` と `for` の脱糖。標準 trait を std の宣言へ移す（S-72、下の持ち越しの一覧）。
4. 標準ライブラリ（`std.fs` `std.audio.wav` など）と `main`、ターゲットの `provides`、`std.audio.device` の文脈の登録（§16.1）。`onsa.policy` は延期。
5. LLVM バックエンド（ネイティブの `exe` / プラグイン）。C バックエンド経由で先に動かし、LLVM は性能が要るときに。
6. `interface` / `audit` / `primer` の完成。

**第 1 期から持ち越す作業。** 第 1 期の暫定の作りを、第 2 期の該当する作業の中で置き換える。第 2 期の各作業に着手するときと、第 2 期を締めるときに、この一覧を確かめる。レビューで暫定と決めたものは、ここに必ず載せる。

| 項目 | 第 1 期の暫定 | 第 2 期で行うこと | 作業 | 出典 |
|---|---|---|---|---|
| 標準 trait | コンパイラの列挙 `Bound`（S-84 の数の trait と演算子 trait を含む）、含意の表 `implies`、§6.3 の組込み型の実装の Rust の表 | 標準 trait を std の `trait` 宣言（上位の trait を含む）に、組込み型の実装を std の `impl` に移す。コンパイラは lang item（演算子の脱糖、補間の `Show`、`T.default()`、`Drop`、derive、`for` の `Iter`）だけを知る。`Bound`・`implies`・Rust の表を取り除く 演算子 trait のシグネチャ（返り値の型）は、std に宣言する前に R-131 の残りとして決める。利用者の型が `Int` を実装できるようにする前に、総称の整数の変換（`api-candidates.md` の A-09）を `Int` に置くかを決める | 3 | R-127、S-72、S-84、R-131 |
| 参照カウント | 移動・コピー・破棄の文と型ごとの破棄の種類は第 1 期から Core にある（R-81）。破棄の種類「参照カウント」は全てのバックエンドで E0200 | Shared 型のコピーを参照カウントの増加に変え、破棄の種類「参照カウント」を実装する（Perceus） | 2 | R-81 |
| `Drop` | `impl Drop` は E0200（trait の実装は第 2 期）。取り出しで全体を消費する規則（S-85）は第 1 期に入れる | `Drop` を実装する型の分解とフィールドの取り出しを E0711 にする。`drop(move self)` の本体の終わりで、`self` を `drop` を呼び直さずにフィールドごとに破棄する（本体の中では分解できる） | 2 | R-95、S-85 |
| std 以外の依存 | 依存として読み込むのは埋め込みの std だけ。パッケージのモデル（ID と依存の表）は std 以外も受けられる形にある（R-88）。パッケージルート直下の `tests/` の `.onsa` は E0200（S-96） | 取得元（パス、レジストリ、git など）、版の解決（菱形の依存で違う版を同居させるか）、`onsa.lock` の形を決め、依存を読み込む。パッケージの `tests/` の役割（R-122。問いは R-122 の本文に集めた）も一緒に決め、`tests/` の E0200 を決めた役割に置き換える | 4 | R-88、S-83、R-122、S-96 |
| 無名関数の捕捉 | 無名関数が Shared 型の値を捕捉したとき、複製（参照カウントの増加）か借用かが決まっていない。§5.4 の表の行は「第 2 期に決める」で、実装は E0200 | 捕捉の意味を決めて §5.4 の表に書き、束縛の状態の判定に足す | 2 | R-85、S-80 |
| 標準の効果 | std に宣言だけを置き、`Alloc` 以外を効果行に書くと E0200。効果の宣言は std の中だけで受け付ける | 操作と handler を実装し、利用者の `effect` 宣言を受け付ける。`Random` などのモジュールの名前を確定する | 1 | R-129、S-74 |

第 3 期（変換先の拡大）は §20 の 10〜11 のまま。C++ と Rust への核の変換は、C バックエンドの構造を流用できるので各 M。

---

## 6. リスクと対策

| リスク | 影響 | 対策 |
|---|---|---|
| ビット一致が C コンパイラの条件で崩れる（I-02） | `strict` の約束が守れない | M4 で `_Static_assert` とフラグを生成物に含め、M5 の conformance を CI で複数コンパイラ（clang / gcc / MSVC）に対して回す |
| 環境の libm の精度のばらつき | 組込みの軽量 libm で 2 ULP を超え、試聴と機器の音がずれる | M5 で環境ごとに測定し、超える関数だけ Onsa 実装に差し替える。ビット一致が要る用途向けの `std.math.exact` は §19 |
| panic の実現（I-01）が組込みで重い | `jmp_buf` の大きさ、`longjmp` の無い環境 | ターゲットの `panic` 設定で選べるようにし、`trap` を既定にする |
| 型推論の規則（仕様 §4.7）が実装でずれる | 診断の位置が LLM に分かりにくい | §4.7 の各規則に対応する否定例をテストに入れる |
| flow の名前空間の名前解決 | モジュールと名前空間の扱いが実装で分かれる | 名前空間をモジュールと同じ項目の種類として実装する（仕様 §11.2、§11.6。E0305） |
| 第 1 期の範囲が膨らむ（LSP、play、probe） | C の出力が遅れる | M7 は M4〜M6 の後に置き、M4 の完了を第 1 期の最初の区切りにする |
