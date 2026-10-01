# Kumi 言語仕様 Draft 0.2

> Kumi（組み / 組紐）: 小さな部品を、検査可能な継ぎ目で組み上げる言語。

Draft 0.1 からの変更点と、その理由は [`docs/kumi-0.2-changes.md`](docs/kumi-0.2-changes.md) にまとめた。主な変更は次の 3 つ。

1. **表面構文の原則を「既存コーパスに寄せる」から「同形同義・異義異形」に変えた。** `proc` → `flow`、`sink` → `move`、`virtual` → `target`、レート `Const` → `Init`、flow の呼び出しは後置の `~`（`saw~(f0)`）、flow 本体は `let` で書く。
2. **目的を「FAUST に代わる DSP 開発環境の基盤言語」と明記した。** パラメータのメタデータ、全言語へ変換できる「移植可能な核」、バックエンド間のビット一致、IDE 向けのツールを加えた。
3. **メモリ管理を組込み前提で作り直した。** ヒープ確保を明示の効果 `Alloc` にした。flow の状態はコンパイル時に大きさが決まる。スタックの上限は監査できる。

---

## 0. 目的と設計原則

### 0.1 目的

- **DSP 開発環境の基盤となる言語。** FAUST と同じく、一つのソースから IDE での試聴、各言語へのトランスパイル、プラグインや組込み機器への組み込みまでを行う。FAUST と違い、point-free の難解な記法を使わず、DSP 以外のコード（ボイス割り当て、MIDI 処理、ファイル入出力）も同じ言語で書ける。
- **LLM が本体を書き、人間が監査し、コンパイラが誤りを局所・高速・決定的に否定する。**
- **同じソースが、デスクトップのプラグインと、ヒープの無いマイコンの両方で動く。**
- **最終的には、言語全体を各言語へ変換できる。** 第一段階では DSP の核（flow と、そこから呼ばれる関数）だけを全ての変換先へ移し、言語全体へ段階的に広げる（§13）。

### 0.2 原則

| # | 原則 | 帰結 |
|---|---|---|
| P1 | **局所性** — 意味・型・エラーは関数の中で閉じる | 全関数のシグネチャは完全注釈。推論は関数本体の中だけ。 |
| P2 | **一意性** — 一つの意図に書き方は一つ | 糖衣を増やさない。`kumi fmt` が唯一の表記に正規化する。 |
| P3 | **同形同義・異義異形** — 同じものは同じ見た目、違うものは違う見た目 | 既存言語の見た目は、**意味が一致するときだけ** 借りる。詳細は §0.3。 |
| P4 | **世界への接触はシグネチャに出る** | 効果（`uses {...}`）で表す。**ヒープ確保も効果**（`Alloc`）。 |
| P5 | **リアルタイム性は型で検査する** | `rt` 修飾。関数単位。 |
| P6 | **メモリの上限は静的に分かる** | flow の状態の大きさはコンパイル時に決まる。ヒープを使う箇所はシグネチャに出る。スタックの上限は監査できる。 |
| P7 | **移植可能性は言語の性質** | どの変換先でも同じ意味を持ち、`strict` ではビット一致する。第一段階は DSP の核、最終目標は言語全体（§13）。**新しい言語機能は、主要な変換先への変換方法を示せる場合にだけ入れる。** |
| P8 | **修復ループは言語機能** | 安定診断コード、JSON 診断、型付きホール、インタフェース抽出、監査コマンド。 |
| P9 | **仕様の例は全て検査を通る** | 仕様内のコード例はプライマーとして LLM に渡される前提で書く。 |

### 0.3 見た目を決める規則（P3 の詳細）

人間も LLM も、見た目から意味を予測する。見た目と意味の対応が一対一であるほど、認知の負荷は低い。

1. **同じ概念は同じ見た目にする。** 言語の中で同じ概念を表す二つの構文を作らない（P2）。
2. **違う概念は違う見た目にする。** 言語の中で、異なる概念に同じ構文や同じ語を使わない（例: 0.1 では flow の方程式 `y = e` と、fn の代入 `y = e` が同じ見た目だった）。
3. **既存言語から借りるのは、意味が一致するときだけ。** 借りる先は概念ごとに選ぶ。汎用の部分は汎用言語（Rust, Swift, C++）から、信号処理の部分は信号処理の言語（FAUST, SuperCollider, Cmajor, Lustre）から借りる。
4. **偽の友人を作らない。** 主要な既存言語の読み方で読んだとき、**検査を通るのに意味が違う** 構文や名前は採らない。検査で落ちる違い（`i32` と書いて `I32` を求められる、など）は、診断の修正候補で吸収できるので許容する。
5. **意味の広すぎる語を、特定の概念の名前にしない。** `proc`、`object`、`data`、`manager` のような語は、他の言語で別の具体的な意味（無名関数、手続き一般など）を持っていることが多い。

### 0.4 非目標

- Rust の借用検査器を再現すること（参照は第二級に限定し、ライフタイムを持たない）
- 遅延評価、高階型、型レベル計算
- マクロによる構文拡張

---

## 1. 全体構成

```
.kumi ── parse ── resolve ── check (types / effects / rt / exclusivity / flow / rates)
                                   │
                              Kumi Core（正準 IR）
                                   │
            ┌──────────────────────┴───────────────────────┐
     ネイティブのバックエンド                        ソースへの変換（§13）
     C / LLVM / WASM                        C / C++ / Rust / JS / ...
     言語全体を最初から扱う                   段階 1: 移植可能な核（flow とその依存）
     （プラグイン、CLI、組込み）              段階 2: 言語全体（最終目標）
```

言語は二つの世界を持つが、式の構文は共通。

- **fn 世界**: 関数、型、trait、効果。通常のプログラム。
- **flow 世界**: 同期データフロー（Lustre 系）の信号処理。一つの flow は、状態を表す型と、それを操作する関数に降下する（§11）。

---

## 2. 字句

### 2.1 コメント

```kumi
// 行コメント
/// ドキュメントコメント（直後の宣言に付く。`kumi doc` と `kumi interface` に出る）
```

ブロックコメントは無い。

### 2.2 キーワード（全て）

```
fn rt flow par struct enum trait impl effect blocking handler handle with uses
let var if else match for in while break continue return
pub use extern export unsafe target test prop assert
const type as inout move self Self true false
```

`prev` `delay` `vdelay` `sample_rate` は flow の中で予約された組込み名（§11.4）。

### 2.3 命名規則（エラー、lint ではない）

| 種類 | 規則 | 例 |
|---|---|---|
| 値・関数・flow・モジュール | `snake_case` | `wrap01`, `line_count`, `resonator` |
| 型・trait・効果・列挙子 | `UpperCamel` | `Buf`, `Ord`, `Fs`, `Some` |
| 型パラメータ | `UpperCamel` 1 語 | `T`, `Item` |
| 効果行変数 | `snake_case` 1 語 | `e` |
| 定数 | `UPPER_SNAKE` | `MAX_VOICES` |

名前の種別が字面で決まる。

- `Fs.read(p)` は効果操作か型の関連関数、`fs.read(p)` はモジュール関数。
- flow の本体の中で、`saw~(f0)` は **状態を持つインスタンス**、`wrap01(x)` は **状態を持たない関数** の呼び出し。違いは名前ではなく呼び出しの形（後置の `~`、§2.6）で表す。

### 2.4 リテラル

- 整数: `42`, `0xFF`, `0b1010`, `1_000_000`
- 浮動小数: `1.0`, `2.5e-3`（小数点の両側に数字が必須。`1.` や `.5` は不可）
- 文字: `'a'`（Unicode スカラ値）
- 文字列: `"..."`（UTF-8）。補間は `{名前}` または `{名前.フィールド...}` のみ。補間される値は `Show` を実装していなければならない。`{{` と `}}` はエスケープ。補間を含む文字列は新しい `Str` を作るので `Alloc` を要する（§12）。補間を含まない文字列リテラルは静的領域に置かれ、`Alloc` を要しない。
- **既定の型は無い。** リテラルの型は、期待型と関数本体の中の推論で決まる。決まらなければエラー（E0405）。`var acc = 0.0` は、`acc` の型が本体の中で決まらない限り書けない。

  浮動小数のリテラルが既定で `F64` になると、倍精度 FPU の無いマイコン（Cortex-M4F など）で気付かずにソフトウェア浮動小数を使うことになる。それを避けるための規則である。

### 2.5 文の区切り

- ブロック `{ }` の中では、改行で文が終わる。ただし行末のトークンが二項演算子、`=`、`->` の場合、または次の行が `.` で始まる場合は継続する。判定は隣接する 2 行で決まり、インデントは意味を持たない。
- 丸括弧・角括弧・構造体リテラル・`match` の腕の並びの中では、改行は空白として扱う（要素は `,` で区切る）。
- `else` は直前の `}` と同じ行に書く（E0003）。
- `;` は使わない。

### 2.6 `~`（flow の呼び出し）

`名前~(引数, ...)` は flow のインスタンスを作る呼び出しである（§11.5）。

- `~` は名前の直後に空白を空けずに書き、直後に `(` が続く。モジュールで修飾した名前にも付けられる（`filters.resonator~(x, fc, q)`）。
- `~` は flow の呼び出しにだけ使う。flow を `~` 無しで呼ぶと E0811、flow でないものに `~` を付けると E0812。どちらも修正候補を示す。
- `~` は演算子ではなく、他の意味を持たない。ビット反転は `!` と書く（Rust と同じ）。
- FAUST の `~` はフィードバック、つまり状態を作る演算子である。Kumi の `~` も「状態を持つものを作る」印で、意味の方向は同じである。FAUST の二項演算子としての書き方（`+ ~ _`）は Kumi では構文エラーになる。

---

## 3. 演算子

### 3.1 優先順位を持たない規則

二項演算子は **群** に分かれる。異なる群の演算子を括弧なしで混在させるとエラー（E0010）。

| 群 | 演算子 | 同じ群内の連鎖 |
|---|---|---|
| 加法 | `+` `-` | 左結合で可 |
| 乗法 | `*` `/` `%` | 左結合で可 |
| 比較 | `==` `!=` `<` `<=` `>` `>=` | 不可（`a < b < c` はエラー） |
| 論理積 | `&&` | 可 |
| 論理和 | `\|\|` | 可 |
| ビット | `&` `\|` `^` `<<` `>>` | 不可 |

```kumi
let a = x + y - z             // OK: 加法群の連鎖
let b = x + (y * z)           // OK
let c = x + y * z             // E0010: 加法と乗法の混在
let d = (lo <= x) && (x < hi) // OK
```

前置の `-` と `!`、後置の呼び出し `f(x)`・flow の呼び出し `f~(x)`・フィールド `.f`・添字 `[i]`・`?` は、どの二項演算子よりも強く結合する。

### 3.2 演算子は trait に脱糖する

`+` は `Add.add`、`<` は `Ord.lt` など（§6.3）。オーバーロードはこの経路だけで、型ごとに実装は高々一つ。

### 3.3 変換

`as` は **情報を失わない拡大変換** だけに使える（`I32 as I64`、`F32 as F64`、`I32 as F64`、`U8 as F32` など）。それ以外は、変換元の型のメソッドを使う。

```kumi
let n = i as I64                 // OK
let k = n.narrow_i32()           // I64 -> Option[I32]
let s = x.round_f32()            // F64 -> F32、最近接偶数丸め
let c = xs.len().round_f32()     // U32 -> F32、最近接偶数丸め
let j = y.trunc_i32()            // F32 -> I32、範囲外は panic
```

Rust の `as` は情報を失う変換も許す。Kumi の `as` で書けるのはその部分集合で、検査を通るものは Rust と同じ意味を持つ（§0.3 の 4）。

`as` 式を二項演算子のオペランドにするときは括弧が必要（E0011）: `acc + (x as F64)`。

暗黙の数値変換は無い。唯一の暗黙変換は flow のレート昇格（§11.3）で、これは値を変えない。

---

## 4. 型

### 4.1 組込み型

| 分類 | 型 | 種（§4.6） | 記憶域（§12.1） |
|---|---|---|---|
| 整数 | `I8 I16 I32 I64 U8 U16 U32 U64` | Copy | 値 |
| 浮動小数 | `F32 F64`（IEEE 754 binary32 / binary64） | Copy | 値 |
| その他スカラ | `Bool Char ()` | Copy | 値 |
| 固定長配列 | `[T; N]`（`N` はコンパイル時定数） | `T` に従う | 値 |
| 文字列・バイト列 | `Str`（UTF-8, 不変）, `Bytes`（不変） | Shared | ヒープ（リテラルは静的） |
| 列 | `Array[T]`（不変・永続、参照カウント） | Shared | ヒープ |
| 集合 | `Map[K, V]`, `Set[T]` | Shared | ヒープ |
| バッファ | `Buf[T]`（可変、長さは生成時に固定） | Affine | ヒープ |
| ビュー | `Span[T]`（引数専用、§5.3） | — | 借用元 |
| 標準 enum | `Option[T]`, `Result[T, E]` | 中身に従う | 値 |
| 関数 | `fn(A, B) -> R uses {E}`, `rt fn(A) -> R` | Copy（捕捉なし） | 値 |
| FFI | `Ptr[T]`（§14） | Copy | 値 |

`Option` と `Result` の列挙子だけは修飾なしで書ける。他の enum の列挙子は常に `Type.Variant` と書く。

**添字・長さ・大きさの型は `U32` に固定する。** プラットフォームによって幅が変わる整数型（Rust の `usize` に当たるもの）は無い。

- 理由: 幅がターゲットで変わると、オーバーフローで panic する点がターゲットごとに変わり、ソースの意味とバックエンド間のビット一致が崩れる。JavaScript にも対応する型が無い。
- `len()`、添字、`const N`、`SIZE` などは全て `U32`。Java の配列添字（`int`）や JavaScript の配列長と同じ幅である。
- 一つの配列・バッファ・文字列は 2³² − 1 要素（バイト）までに制限される。それを超えるデータは分割して扱う（ファイルのオフセットなど、大きさが要る値には `U64` を使う）。
- C の `size_t` は FFI の宣言の中でだけ `CSize` として書ける（§14.1）。`U32` との変換は境界で検査する。

### 4.2 文字列

`Str` は **常に正しい UTF-8 のバイト列** である。長さと位置はバイト単位で数える（Rust、Go と同じ）。

| 操作 | 意味 |
|---|---|
| `s.len() -> U32` | バイト数 |
| `s.substr(from, to) -> Str` | バイト範囲 `[from, to)` の部分文字列（`Alloc`）。範囲外、または文字の途中で切れる場合は panic |
| `s.get_substr(from, to) -> Option[Str]` | 同上。panic の代わりに `None` を返す |
| `s.find(pat: Str) -> Option[U32]` | 最初に現れるバイト位置 |
| `s.is_char_boundary(i) -> Bool` | `i` が文字の境界か |
| `s.chars()` / `s.bytes()` | Unicode スカラ値（`Char`）/ バイト（`U8`）の反復 |
| `Str.from_utf8(b: Bytes) -> Result[Str, Utf8Error]` | 検証付きの変換。生のバイト列は `Bytes` で扱う |

- `s[i]` の添字は無い（何を返すかが一意でないため）。1 バイトは `s.bytes()` か `s.as_bytes()` から得る。
- 等値と順序はバイト列の辞書順。UTF-8 のバイト順はコードポイントの順と一致する。正規化はしない。
- 変換先の文字列の表現が UTF-8 でない場合（JavaScript など）も、この意味を保つ（§13.5）。

### 4.3 `Map` と `Set` の反復順序

`Map` と `Set` は **挿入した順** に反復する（JavaScript の `Map`、Python の `dict` と同じ）。要素を削除しても、残りの順序は変わらない。ハッシュ関数や実装によって反復の順序が変わらないので、全てのターゲット・変換先で結果が決定的になる。

### 4.4 ユーザ定義型

```kumi
pub struct Point {
  x: F32,
  y: F32,
}

pub enum Shape {
  Circle(F32),
  Rect(F32, F32),
}

pub struct Hz(F32)          // 単一フィールドのタプル構造体 = newtype（別名ではなく別の型）

type Samples = Buf[F32]     // 型別名（新しい型を作らない。`kumi interface` は展開して表示する）
```

- `struct` は名前的。匿名レコード型は無い。
- フィールドアクセス `p.x` は、`p` の型が注釈またはその場の推論で既知であることを要求する（E0420）。

### 4.5 ジェネリクス

```kumi
pub fn clamp[T: Ord](x: T, lo: T, hi: T) -> T {
  if x < lo { lo } else if x > hi { hi } else { x }
}

pub struct Ring[T, const N: U32] {
  data: [T; N],
  head: U32,
}
```

- 宣言位置で `[...]`。呼び出し位置で型引数は書かない（期待型の注釈で決める）。このため、式の中の `[...]` は常に添字か配列リテラルであり、構文が曖昧にならない。
- const ジェネリクスは等値比較のみ（`N + 1` のような型レベル算術は無い）。
- 型パラメータには、暗黙に `Dup`（複製できる = Copy か Shared）の制約が付く。Affine 型も受け付けるには `[T: ?Dup]` と書いて、この制約を外す（Rust の `?Sized` と同じ形）。その場合、`T` の値は借用・`inout`・`move` でしか扱えない。
- `Buf[T]` と `Span[T]` の要素型は `T: Copy` に限る。

### 4.6 種（kind）: Copy / Shared / Affine

全ての型は構造から次のどれかに分類される。注釈は不要で、`kumi interface` に表示される。

| 種 | 該当 | 複製 | 破棄 |
|---|---|---|---|
| Copy | スカラ、Copy 要素の固定長配列・タプル・構造体・enum、捕捉の無い関数値 | ビットコピー | 何もしない |
| Shared | `Str` `Bytes` `Array` `Map` `Set`、それらを含む型 | 参照カウントで共有、書き込み時コピー | 参照カウントを減らし、0 なら解放（`Alloc`） |
| Affine | `Buf`、`Drop` 実装型、flow の状態（`f.State`）、それらを含む型 | 不可（ムーブのみ） | 中身の破棄、`Drop` |

---

## 5. 値・変数・引数モード（可変値意味論）

### 5.1 束縛

```kumi
let x: I32 = 1     // 不変
var acc: F64 = 0.0 // 可変（ローカルのみ）
acc = acc + (x as F64)
```

- 代入は **値** の代入。`var b = a` の後で `b` を変えても `a` は変わらない（Shared 型は書き込み時コピー、一意なら in-place。Perceus 方式の参照カウント）。
- 参照は値として存在しない。したがってライフタイムも無い。
- **シャドーイングは無い。** 同じ関数の中で、同じ名前を二度束縛できない（E0304）。`let x = x + 1` はエラー。flow の自己参照（§11.2）と意味が衝突しないための規則でもある。

### 5.2 引数モード

| モード | 宣言 | 呼び出し位置 | 意味 |
|---|---|---|---|
| 借用（既定） | `x: T` | `f(x)` | 読み取り専用。呼び出し中は変更されない。 |
| `inout` | `inout x: T` | `f(inout x)` | 排他的な可変借用。呼び出し側は `var` か `inout` 引数であること。 |
| `move` | `move x: T` | `f(move x)` | 所有権を受け取る。Affine 値はこの後使えない。 |

- `inout` と `move` は **呼び出し位置にも書く**。読み手は呼び出し 1 行で、何が変わるかを知る。`inout` は Swift、`move` は C++ / Rust と同じ意味。
- 同じ変数を一つの呼び出しで二度 `inout` に渡すとエラー（E0702）。同じ値の **異なるフィールド**（`self.voices[i]` と `self.params[i]` など）は重ならないものとして扱う。同じ配列の添字どうしは、添字が等しいかを静的に判定しないので、重なるものとして扱う。
- メソッドのレシーバは `self` / `inout self` / `move self` と宣言する。レシーバの `inout` は呼び出し位置に書かない（宣言から分かる）が、レシーバは可変な場所（`var`、`inout` 引数、それらのフィールドや要素）でなければならない。

### 5.3 第二級の値: 借用・`Span`・捕捉するクロージャ

次のものは **引数の位置にだけ** 現れる。返り値、構造体のフィールド、`let` の右辺にはできない（E0710）。そのため、どれもヒープを使わず、ライフタイムも要らない。

| もの | 書き方 | 意味 |
|---|---|---|
| 借用 | `f(x)`, `f(inout x)` | §5.2 |
| `Span[T]` | 引数の型として `xs: Span[T]` / `inout xs: Span[T]` | 連続した要素の非所有ビュー（C++20 の `std::span` と同じ意味）。`[T; N]`、`Buf[T]`、`Span[T]` を渡せる |
| 部分ビュー | `f(xs.slice(from, to))`, `f(inout xs.slice(from, to))` | 半開区間 `[from, to)` の `Span`。範囲外は panic |
| 捕捉するクロージャ | `xs.map(fn(x) { x * k })` | 外側の値をコピーで捕捉する無名関数。`inout` 引数と Affine 値は捕捉できない |

捕捉の無い関数値（名前付きの関数、捕捉しない無名関数）は Copy の第一級の値で、保存も返却もできる。

---

## 6. 関数と trait

### 6.1 関数

```kumi
pub fn mean(xs: Array[F64]) -> Option[F64] {
  if xs.is_empty() {
    return None
  }
  Some(xs.sum() / (xs.len() as F64))
}
```

- 引数・返り値・効果は全て注釈する。返り値が `()` の場合だけ `->` を省略する（省略が唯一の書き方）。
- ブロックの値は最後の式。`return` は途中脱出にだけ使う（末尾の `return` は `kumi fmt` が除去する）。
- 多重定義、既定引数、可変長引数、名前付き引数は無い。
- 無名関数は `fn(x: F32) -> F32 { x * 2.0 }`。期待型が分かる位置では注釈を省略できる: `xs.map(fn(x) { x * 2.0 })`。
- `mean` は `xs` を借用して読むだけなので、`Alloc` を要しない（§12.2）。

### 6.2 メソッド

```kumi
impl Point {
  pub fn new(x: F32, y: F32) -> Point { Point { x: x, y: y } }   // 関連関数: Point.new(...)
  pub rt fn norm(self) -> F32 { sqrt((self.x * self.x) + (self.y * self.y)) }
  pub rt fn scale(inout self, k: F32) {
    self.x = self.x * k
    self.y = self.y * k
  }
}
```

`impl` 内の関数はドット記法でのみ呼ぶ（`p.norm()`, `Point.new(1.0, 2.0)`）。自由関数は前置でのみ呼ぶ。同じ関数に二つの呼び方は無い。

### 6.3 trait

```kumi
pub trait Show {
  fn show(self) -> Str uses {Alloc}
}

impl Show for Point {
  fn show(self) -> Str uses {Alloc} { "({self.x}, {self.y})" }
}
```

- **一貫性**: `impl Tr for Ty` は `Tr` か `Ty` を定義したモジュールにしか書けない（孤児規則）。重複実装、特殊化は無い。
- ジェネリック trait（`Iter[T]` など）は、一つの型について高々一つしか実装できない。
- 既定メソッドは可。トレイトオブジェクト（動的ディスパッチ）は無い（§19）。
- 演算子 trait: `Add Sub Mul Div Rem Neg Eq Ord BitAnd BitOr BitXor Shl Shr`。
- 標準 trait: `Eq`, `Ord`（演算子用。浮動小数は IEEE 比較）、`TotalOrd`（ソート用。浮動小数は実装しない）、`Hash`, `Show`, `Default`, `Iter[T]`, `IntoIter[T]`, `Drop`, `Num`, `Float`, `Dup`（自動。§4.5）。
- `Drop` の `drop(move self)` は、`rt` を付けること、`uses {Alloc}` を持つことだけが許される。値が破棄される位置は、その型の破棄が必要とするもの（`Alloc`、非 rt）を要求する（E0611 / E0901）。

### 6.4 derive

```kumi
@derive(Eq, Hash, Show)
pub struct Key {
  id: U32,
}
```

`@derive` で書けるのは `Eq Ord TotalOrd Hash Show Default` の閉じた一覧だけ。

### 6.5 属性（全て）

`@derive(...)`, `@repr(c)`, `@relaxed`, `@deprecated("...")`, `@param(...)`（§11.7）。これ以外の属性は無い。

### 6.6 コンパイル時定数

```kumi
const TABLE_SIZE: U32 = 1024
const SINE: [F32; 1024] = make_sine_table()
```

- 初期化式から呼べるのは、効果行が空か `{Alloc}` だけの関数。`Alloc` はコンパイラが提供する。
- 結果は Copy でなければならない。結果は読み取り専用の静的領域（組込みではフラッシュ）に置かれる。

---

## 7. 制御

```kumi
if c { a } else { b }
match v {
  Some(x) => x,
  None => 0,
}
for i in 0..n { ... }       // `..` は半開区間。`for` は IntoIter に脱糖する
while cond { ... }
break / continue / return
```

- `match` は網羅的（E0501）。ガードは `Some(x) if x > 0 => ...`。
- 反駁可能な `let` は無い。分解は反駁不能なパターン（タプル・構造体）だけ: `let (a, b) = pair`。
- `loop {}` は無い（`while true` と書く）。
- 範囲 `a..b` は `for` と `par`（§11.5）の見出しにしか書けない。
- 末尾呼び出しの最適化は保証しない。反復は `for` / `while` で書く。

---

## 8. 効果

### 8.1 宣言と使用

```kumi
pub blocking effect Fs {
  fn read(path: Path) -> Result[Str, IoError]
  fn write(path: Path, data: Str) -> Result[(), IoError]
}

pub fn load(path: Path) -> Result[Str, IoError] uses {Fs} {
  Fs.read(path)
}
```

- 効果行は **効果単位**（`Fs`）で書く。標準ライブラリは `FsRead` と `FsWrite` を分けている。本仕様の例では簡単のため `Fs` を使う。
- 効果行が空なら `uses` を書かない。それが純粋関数。
- `blocking` はブロックしうる効果の印である（§8.2）。
- `load` は受け取った `Str` をそのまま返すので、破棄が起きず、`Alloc` を要しない。
- 効果の多相:

```kumi
pub fn map[T, U, e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {Alloc, e} { ... }
```

### 8.2 `Alloc` と、ブロックする効果

- **`Alloc`** はヒープの確保と解放を表す **明示の効果** である。Shared 値と `Buf` の生成・解放、補間文字列の生成は `Alloc` を要する（§12.2）。
- **ブロックするかどうかは、効果の宣言で決まる。** ブロックしうる操作（ロック、システムコール、待機）を持つ効果は `blocking effect` と宣言する。**関数がブロックしうるのは、効果行に `blocking` の効果を含むときだけ** である。使う側は `uses {Fs}` と書くだけでよく、ブロックの印を二度書く必要は無い。
- `blocking` でない効果の handler は、その操作の中で `blocking` の効果を使えない（E0612）。この検査は handler の定義の中で閉じる。例えば `Log` はブロックしない効果なので、リングバッファに書く handler は書けるが、標準出力に同期的に書く handler は書けない。
- 組込みの `Block` は操作を持たない `blocking` の効果で、extern 関数がブロックすることを主張するのに使う（§14.1）。`Block` は handler で処理できない。
- `rt fn` は、効果行に `Alloc` も `blocking` の効果も含まない関数である（§10）。

標準ライブラリの主な効果:

| 効果 | `blocking` | 内容 |
|---|---|---|
| `Fs`, `Net`, `Stdout`, `Stdin` | ○ | 入出力 |
| `Sleep` | ○ | 待機 |
| `Sync` | ○ | `Chan`、`Mutex` などのブロックする同期操作（§16） |
| `Spawn` | ○ | タスクの生成と合流（§16） |
| `Clock` | × | 現在時刻の取得 |
| `Random` | × | 乱数 |
| `Log` | × | ログ（handler はブロックしない書き方に限られる） |
| `Alloc` | × | ヒープ（§12） |

`Alloc` を明示にしたのは、組込みではヒープが無いことがあり、またヒープの代わりに arena を使い分ける価値があるからである。ブロックを効果の宣言で表すのは、ブロックできない環境（ブラウザのメインスレッド、AudioWorklet、プラグインの GUI スレッド）へ、どの関数を持ち込めるかをシグネチャだけで判断するためである（§13.5）。

### 8.3 handler

```kumi
handler memory_fs: Fs {
  fn read(_: Path) -> Result[Str, IoError] { Ok("a\nb\n") }
  fn write(_: Path, _: Str) -> Result[(), IoError] { Ok(()) }
}

let r = handle { load(Path.new("x.txt")) } with memory_fs
```

- handler は **末尾再開のみ**。各操作は値を返して呼び出し元に戻る。継続の捕捉、早期脱出、多重再開は無い。
  - 実装は証拠渡し（evidence passing）で、静的に解決できればゼロコスト。
  - Affine 値が複製される経路が無いので、一意性と健全に共存する。
  - handler の操作が `rt` なら、handle 式も `rt` で使える。
  - `blocking` でない効果の handler は、ブロックする効果を使えない（§8.2）。
- handler 自身が使う効果は、`handle` 式の効果行に加わる。
- handler は引数を取れる。引数は第二級（§5.3）で、`handle` 式の間だけ有効: `handler arena(inout mem: Span[U8]): Alloc { ... }`、`handle { ... } with arena(inout scratch)`。
- インライン形式 `handle { ... } with Fs { fn read(...) ... }` も同じ意味。

### 8.4 `Alloc` の handler と、持ち出しの禁止

```kumi
use std.mem.{arena}

const N: U32 = 1024

/// 一時的な Array を使って倍音テーブルを作る（ヒープを使う）
fn harmonics() -> [F32; N] uses {Alloc} { ... }

/// 呼び出し側が渡した作業領域の上で harmonics を実行する。ヒープの無いターゲットでも呼べる
pub fn harmonics_in(inout scratch: Span[U8]) -> [F32; N] {
  handle { harmonics() } with arena(inout scratch)
}
```

- `Alloc` を処理する `handle` 式の結果の型は Copy でなければならない（E0640）。ヒープ上の値を、その確保領域の外へ持ち出せない。
- 確保した領域が尽きた場合は panic する。
- 解放は、その値を確保した allocator に戻る（オブジェクトのヘッダに確保元を記録する）。そのため、外側で確保された値が arena の中で破棄されても正しく扱われる。
- std は `arena`（作業領域の上の bump allocator）を提供する。システムのヒープはターゲットが提供する（§15.3）。`Alloc` の handler を自分で書くには `unsafe` が要る。

### 8.5 main と実行環境

```kumi
pub fn main() -> Result[(), AppError] uses {Fs, Stdout, Alloc} { ... }
```

`main` の効果行の各効果について、ビルドターゲットが handler を提供しなければならない（E0610、§15）。ヒープの無いターゲットは `Alloc` を提供しないので、その `main` は `Alloc` を効果行に持てない。

時刻と乱数も効果（`Clock`, `Random`）。待機は `Sleep` で、`Clock` とは分けてある（`Clock` はブロックしない）。テストでは handler を差し替えるだけで決定的になる。`test` と `prop` の本体では、テストランナーが `Alloc` を提供する。

---

## 9. エラーと panic

### 9.1 回復可能なエラー

`Result[T, E]` と後置 `?`。

```kumi
pub fn line_count(path: Path) -> Result[U64, ConfigError] uses {Fs, Alloc} {
  let text = Fs.read(path).map_err(ConfigError.Io)?
  ...
}
```

`?` は、関数の返り値の `E` と **同じ型** のエラーにしか使えない。暗黙の変換（`From` 相当）は無い。変換は `map_err` で明示する。

### 9.2 panic（バグ）

次の場合は panic する。

- 整数のオーバーフロー（`+ - *`。ラップアラウンドは `wrapping_add`、飽和は `saturating_add` などで明示する）
- 整数のゼロ除算
- 範囲外の添字アクセス `xs[i]` と `xs.slice(from, to)`（範囲外を許す取得は `xs.get(i)` で、`Option` を返す）
- `Alloc` の handler の領域が尽きたとき
- `unwrap`、`assert` の失敗、`panic(msg)`

panic は効果行に現れない。

| 文脈 | panic の挙動 |
|---|---|
| 通常の実行 | メッセージと位置を出力してプロセスを終了する（巻き戻しは無い） |
| テスト | そのテストを失敗にする |
| `rt` 関数（flow の `process` を含む） | その呼び出しを中断し、出力をゼロで埋め、インスタンスを **poisoned** にする。以後の `process` は無音を出力し、`reset` まで復帰しない。export された C API は戻り値で通知する。 |
| export された関数 | panic は FFI 境界を越えない。エラーコードに変換する。 |
| OS の無いターゲット | ターゲットの `panic` 設定（`trap` / `reset` / `halt`）に従う。`panic_messages = false` でメッセージ文字列をバイナリから除く（§15.3）。rt での poisoned の規則は同じ。 |

---

## 10. リアルタイム（`rt`）

```kumi
pub rt fn soft_clip(x: F32) -> F32 {
  x / (1.0 + abs(x))
}
```

`rt fn` の検査規則は次の通り（違反は E09xx）。

1. 効果行に `Alloc` を含まない（E0902）。したがって Shared 値と `Buf` の生成も、所有する Shared 値・`Buf` の破棄もできない（§12.2）。
2. 効果行に `blocking` の効果を含まない（E0904）。したがってブロックしない。
3. `rt` でない関数を呼ばない（E0901）。暗黙の破棄で呼ばれる `Drop` も含む。
4. 再帰しない（直接・相互とも、E0903）。モジュール間の import は循環しない（§15.1）ので、この検査はモジュールの中で閉じる。これによりスタックの上限が計算できる（§12.5）。
5. ループの上限は検査しない（停止性は対象外）。

- `rt` は関数型の一部（`rt fn(F32) -> F32`）で、高階関数でも保持される。
- 1 と 2 は効果行だけで決まる。`rt` を付けた関数では、これらとともに 3 と 4 が検査される。
- `extern` 宣言の `rt` は検証されない主張として扱い、`kumi audit` に列挙する（§14）。

参考: Clang の `[[clang::nonblocking]]` / `[[clang::nonallocating]]` と同種の検査を、言語の型に組み込んだもの。

---

## 11. flow: 信号処理

### 11.1 考え方

flow は **同期データフロー** の信号処理ノード（Lustre / SCADE 系）。FAUST と同じく、

- 状態は遅延にしか現れない
- 結線の誤りはコンパイル時に落ちる
- タイトなループに降下する
- 状態の大きさがコンパイル時に決まる

という性質を持つ。ただし point-free ではなく、**全ての信号に名前がある**。

flow の本体は、**1 サンプルごとに評価される関数の本体** と同じ形で書く。fn の本体と違うのは次の 3 点だけである。

1. `prev` / `delay` / `vdelay` で、信号の **過去の値** を参照できる。
2. 値が **レート** を持つ（§11.3）。
3. flow の呼び出し `f~(...)` は、**状態を持つインスタンス** を作る（§11.5）。

### 11.2 宣言

```kumi
pub flow one_pole(x: Sig[F32], p: Ctl[F32]) -> Sig[F32] {
  let y = ((1.0 - p) * x) + (p * prev(y, 0.0))
  y
}
```

- 入力は `(名前: レート型, ...)`、出力は `-> レート型`。複数の出力は struct を値型にして表す（`-> Sig[Stereo]`）。
- 本体は `let` 文の並びと、最後の式（出力）。`var`、代入、`for`、`while`、`return` は書けない（E0806）。
- **名前は上から順に定義する。** 定義より前で（自分自身の定義の中も含む）名前を参照できるのは、`prev` / `delay` / `vdelay` の第 1 引数だけである。過去の値は既に存在するので、前方参照ではない。それ以外の前方参照は E0801。
- この規則により、遅延を通らない閉路（瞬時のループ）は書けない。因果性の検査は名前の順序の検査になる。
- シャドーイングは無い（§5.1）ので、`prev(y, 0.0)` の `y` は常に、その本体の `let y` を指す。

### 11.3 レート

| レート型 | 意味 | 評価のタイミング |
|---|---|---|
| `Init[T]` | 初期化時に決まる値 | `init` で 1 回 |
| `Ctl[T]` | ブロックレート | `process` の呼び出しごとに 1 回 |
| `Sig[T]` | サンプルレート | サンプルごと |

- レートは `Init < Ctl < Sig` の順に並ぶ。式のレートはオペランドのレートの最大値。コンパイル時定数（`const`、リテラル）は `Init` 以下のどのレートにもなる。
- 低いレートから高いレートへの昇格は暗黙に行う（値は変わらない。言語で唯一の暗黙変換）。高いレートから低いレートへの変換は無い。間引きが要る場合は明示的な flow（`sample_and_hold` など）を使う。
- コンパイラは各 `let` を、そのレートに応じたループの外側へ巻き上げる。係数計算がサンプルループの外に出ることが、型から保証される。
- レートは最も外側に付く。値型 `T` は Copy でなければならない（E0810）。例: ステレオ信号は `Sig[[F32; 2]]`、名前付きの複数出力は `Sig[Stereo]`。
- `Init` は「初期化時」、`const` は「コンパイル時」で、別の概念なので別の語を使う。

### 11.4 組込み

| 名前 | 型（概略） | 意味 |
|---|---|---|
| `prev(e, init)` | `Sig[T] -> Sig[T]` | 1 サンプル遅延。最初のサンプルは `init` |
| `delay(e, N, init)` | `N: const U32`、`N >= 2` | N サンプル遅延。1 サンプルは `prev` と書く（E0807） |
| `vdelay(e, d, MAX, init)` | `d: Sig[F32]` 以下のレート、`MAX: const U32` | 可変遅延（線形補間）。`d` は `[1, MAX]` に飽和する |
| `sample_rate()` | `Init[F32]` | サンプルレート |

- 遅延線の長さ（`N`、`MAX`）は **コンパイル時定数** でなければならない（E0808）。サンプルレートに依存する長さは、想定する最大のサンプルレートで上限を決める（例: `const MAX_ECHO: U32 = 96000`）。これにより状態の大きさがコンパイル時に決まる（§12.4）。
- `vdelay` の `d` の下限が 1 なのは、`d = 0` が遅延を通らない閉路になるからである。

### 11.5 呼び出しと複製

flow 本体の中での呼び出しは、呼び出す相手によって意味が決まり、相手の種類は呼び出しの形で分かる（§2.6）。

| 呼び出す相手 | 形 | 意味 |
|---|---|---|
| flow | `saw~(f0)` | 呼び出し位置ごとに独立した状態を持つインスタンスを作る |
| 効果行が空の `rt fn` | `wrap01(x)` | 点ごとに適用する。結果のレートは引数のレートの最大値 |
| 効果行が空の非 `rt` fn | `make_window(n)` | `Init` 以下のレートの引数でのみ呼べる。`init` で評価される |
| 効果を持つ fn（`Alloc` を含む） | | 呼べない（E0805） |

- `if c { a } else { b }` は点ごとの選択。**両方の分岐の flow インスタンスは常に進む**（クロックによる停止は §19）。
- flow 本体の中に再帰やループは無い。
- `Alloc` を持つ関数を呼べないので、flow とその初期化はヒープを使わない。

**複製** `par i in 0..N { e }` は、`e` を `N` 個並べる（FAUST の `par(i, N, e)` と同じ意味）。`N` はコンパイル時定数、`i` は各複製の中で `Init` レートの定数、結果の値型は `[T; N]`。`e` の中の flow 呼び出しは、複製ごとに別のインスタンスになる。

```kumi
use std.dsp.{sum}

const UNISON: U32 = 4

pub flow unison(f0: Ctl[F32], detune: Ctl[F32]) -> Sig[F32] {
  let saws = par i in 0..UNISON {
    saw~(f0 * (1.0 + (detune * spread(i, UNISON))))
  }
  sum(saws) * 0.25
}

/// 0..n を [-0.5, 0.5] に等間隔に並べる
pub rt fn spread(i: U32, n: U32) -> F32 {
  (i.round_f32() / (n - 1).round_f32()) - 0.5
}
```

`par` は `for` と違う見た目にしてある。`for` は順に実行される反復で、`par` は同時に存在する N 個の構造の宣言だからである。

### 11.6 生成される API

`flow voice(...)` を宣言すると、コンパイラは名前空間 `voice` に次を生成する。flow 自体は型ではない。状態を表す型は `voice.State` である。

```kumi
// 型
voice.State        // 状態。Affine、固定サイズ、ヒープを使わない。遅延線も含む
voice.Config       // Init 入力をフィールドに持つ struct（Copy）
voice.Params       // Ctl 入力をフィールドに持つ struct（Copy）
voice.Out          // render の結果。出力チャンネルごとの Buf

// 定数
const voice.SIZE: U32        // 状態のうち fast 領域のバイト数（§12.4）
const voice.BULK_SIZE: U32   // 状態のうち bulk 領域のバイト数

// 関数
fn voice.init(cfg: voice.Config, sample_rate: F32) -> voice.State
rt fn voice.reset(inout s: voice.State)
rt fn voice.process(inout s: voice.State, params: voice.Params, <Sig 入力>, <出力>)
fn voice.render(cfg: voice.Config, params: voice.Params, <Sig 入力>,
                frames: U32, sample_rate: F32) -> voice.Out uses {Alloc}
fn voice.params_default() -> voice.Params   // 全ての Ctl 入力に @param の default がある場合
```

- 名前空間はモジュールと同じ扱いで、関数は `voice.process(inout st, ...)` のように前置で呼ぶ（`fs.read(p)` と同じ形）。
- `process` の引数: `Sig` 入力ごとに `name: Span[T]`、出力ごとに `inout name: Span[T]`。出力が単一の値なら名前は `out`、struct ならフィールド名、`[T; N]` なら `[Span[T]; N]`。全ての `Span` の長さは等しくなければならず、違えば panic（poisoned）する。
- `Sig` 入出力の値型は、スカラ、`[スカラ; N]`、または（出力のみ）それらをフィールドに持つ struct。
- `init` は効果を持たず、ヒープを使わない。大きな値の返り値は、呼び出し側の領域に直接構築される（コピーしないことを保証する）。
- `render` はテストと一括処理用。
- 状態の所有者は呼び出し側。サンプルレートを変えるときは、`init` を呼び直す。
- 状態のフィールドは `let` の名前を保つ（`kumi interface`、トランスパイル結果、デバッガ、プローブで同じ名前が見える）。名前の無いインスタンス（`smooth~(gain, 0.01)` を式の中に直接書いたもの）は `smooth_0` のように番号で呼ぶ。
- flow は第一級の値ではない。flow の外からは、この名前空間の型と関数を通じてだけ扱う。
- v0.2 では、flow の出力は `Sig` だけ（`Ctl` 出力は §19）。

### 11.7 パラメータのメタデータ `@param`

```kumi
use std.dsp.{db_to_amp}

pub flow gain(
  x: Sig[F32],
  @param(min: -60.0, max: 12.0, default: 0.0, unit: "dB")
  level: Ctl[F32],
) -> Sig[F32] {
  x * db_to_amp(level)
}
```

- `@param` は `Ctl` 入力にだけ付けられる。キーは `min max default step unit scale label id` の閉じた一覧で、値はコンパイル時定数。`scale` は `"linear"`（既定）か `"log"`。
- 用途: IDE の自動 UI、プラグイン（CLAP / VST3 / AU）のパラメータ情報、`params_default()`、C API のメタデータ表。
- export する flow（§15.3）の `Ctl` 入力には `@param` が必須（E0809）。
- `id` を省略すると、名前から安定した ID を作る。`kumi.policy` で凍結したインタフェースでは、ID の変更もエラーになる（§15.4）。
- export された API は、パラメータを `[min, max]` に飽和させてから `process` に渡す。Kumi の中からの呼び出しでは飽和させない（メタデータは宣言であり、意味を変えない）。

UI の宣言を DSP の式の中に書く FAUST（`hslider(...)`）と違い、パラメータはシグネチャに出る。パラメータの一覧を知るのに本体を読む必要が無い（P1）。

### 11.8 テスト用の補助

一括処理は生成された `render` で行う。`std.dsp.test` には次を置く。

- `impulse(n: U32) -> Buf[F32] uses {Alloc}`
- `magnitude_at(xs: Span[F32], freq: F32, sample_rate: F32) -> F32`
- `energy(xs: Span[F32], from: U32, to: U32) -> F64`（半開区間 `[from, to)` の二乗和）
- `assert_near(a: F64, b: F64, tol: F64)`

---

## 12. メモリ

### 12.1 記憶域

| 記憶域 | 置かれるもの | 確保の時期 | 大きさ |
|---|---|---|---|
| 静的（読み取り専用） | `const`、補間の無い文字列リテラル | コンパイル時 | コンパイル時に決まる |
| 値 | Copy 値、固定長配列、struct、flow の状態 | 所有者の場所（スタック、他の値の中、静的領域） | コンパイル時に決まる |
| ヒープ | Shared 値、`Buf` | `Alloc` を通じて実行時 | 実行時に決まる |

`kumi interface` は、各型について種と大きさ（値の場合）を表示する。

### 12.2 `Alloc` が要る操作

| 操作 | `Alloc` |
|---|---|
| Shared 値・`Buf` の生成、補間文字列 | 要る |
| 所有する Shared 値・`Buf` の破棄（参照カウントが 0 になりうる） | 要る |
| Shared 値・`Buf` の借用、読み取り | 要らない |
| 受け取った Shared 値を、そのまま返す・`move` で渡す | 要らない |
| Copy 値・flow の状態の生成と破棄 | 要らない |

`Alloc` の有無はシグネチャに出るので、関数がヒープを使うかどうかはシグネチャだけで分かる。Zig の「隠れた確保をしない」と同じ目的を、allocator の引数ではなく効果で達成する。

### 12.3 ヒープの無いターゲット

- `provides` に `Alloc` を持たないターゲット（§15.3）では、`main` と export される関数の効果行に `Alloc` を書けない（E0610）。この検査はシグネチャだけで閉じる。
- flow は元々ヒープを使わないので、そのまま使える。
- 初期化時に一時的なヒープが欲しい計算は、静的な作業領域の上で `arena` を使う（§8.4）か、`const` にしてコンパイル時に計算する（§6.6）。

### 12.4 flow の状態の大きさと配置

- flow の状態の大きさは、コンパイル時に決まる（遅延線の長さはコンパイル時定数、値型は Copy、ヒープを使わない）。
- 状態は二つの領域に分かれる。
  - **fast**: スカラと小さな配列。キャッシュや内部 SRAM に置く。
  - **bulk**: ターゲットの `bulk_threshold`（バイト）以上の配列。遅延線や大きなテーブル。外部 SDRAM などに置く。
- 閾値を設定しなければ、全てが fast に入り、`BULK_SIZE` は 0 になる。
- C API は二つの領域を別々のポインタで受け取る（§14.2）。Kumi の中から見ると、状態は一つの値である。

### 12.5 スタック

- `rt` 関数は再帰しない（§10）。flow の `process` は関数値を経由しない。したがって、export された flow の `process` のスタック使用量の上限は計算できる。
- `kumi audit --stack` は、各エントリ（export された関数・flow、`main`）の最悪スタック使用量を報告する。関数値を経由する呼び出しや、rt でない再帰を含むエントリは「不明」と報告する。
- `main` は再入しないので、コンパイラは `main` のローカル変数を静的領域に置いてよい（ターゲットの `main_frame = "static"`）。大きな flow の状態を `main` のローカルに置いても、スタックを消費しない。ソースの意味は変わらない。

### 12.6 参照カウント

- Perceus 方式。所有権の解析により、不要な増減を省き、一意な値はその場で更新する。
- 値が不変なので循環は生じず、循環の回収器は要らない。
- 参照カウントは既定では原子的でない。スレッドに送られた値だけを原子的な参照カウントに切り替える（Koka と同じ方式）。スレッドの無いターゲットでは原子命令を使わない。

---

## 13. 移植性とトランスパイル

### 13.1 段階

| 段階 | 変換する範囲 | 変換先 |
|---|---|---|
| ネイティブ | 言語全体 | C / LLVM / WASM（最初から） |
| 段階 1 | 移植可能な核（§13.2） | 全ての変換先（§13.3） |
| 段階 2（最終目標） | 言語全体 | 全ての変換先（§13.5） |

段階 1 を先に置くのは、DSP の核がどの言語にも素直に移せる（効果もヒープも無い）からである。段階 2 は、言語の設計の段階から制約として扱う（P7、§13.5）。

### 13.2 移植可能な核

次のものを **移植可能な核** と呼ぶ。

- flow
- flow から呼ばれる関数（効果行が空の `rt fn`、`Init` レートで呼ばれる効果行が空の fn）
- それらが使う `const`、型（Copy の struct、enum、固定長配列）

核に入るものは、既存の規則から自動的に次を満たす。新しい検査は要らない。

- 効果が無い（I/O が無く、ヒープも使わない）
- 状態の大きさがコンパイル時に決まる
- 再帰が無く、flow の中に関数値が無い

例外として、核の中から `extern` 関数に到達する場合、その flow は C 系以外の変換先には出力できない。`kumi transpile` は到達経路を示すエラーを出す（E1010）。

### 13.3 変換先

| 変換先 | 段階 1 の生成物 | v0.2 での位置付け |
|---|---|---|
| C（C11） | 状態の struct と関数（§14.2 の API）。ヒープを使わない | 必須。全ての基準 |
| C++ | ヘッダのみのクラス | 計画 |
| Rust | `#![no_std]` の struct と impl | 計画 |
| JavaScript / TypeScript | AudioWorklet で使えるクラス（`Float32Array`、`Math.fround`） | 計画 |
| WASM | C 経由または LLVM 経由 | 計画 |

- 生成されるコードは、ソースの名前を保つ（状態のフィールド名は `let` の名前、パラメータ名は入力の名前）。生成されたコードを人間が監査できることを目的とする。
- `@param` のメタデータは、各言語の定数表として出力する。
- 段階 1 では、言語全体（fn 世界の効果、handler、Shared 型）は C / LLVM / WASM のバックエンドだけが扱う。他の変換先へは段階 2 で広げる。

### 13.4 バックエンド間のビット一致

数値プロファイル `strict`（§15.5）では、全ての変換先が同じ入力に対してビット単位で同じ出力を出す。

- `std.math` は Kumi で書かれており、核と一緒に変換される。変換先の libm の差が入らない。
- FMA への縮約と再結合を禁止する。JavaScript では各演算の後に `Math.fround` を挟む。
- 整数のオーバーフローと範囲外アクセスの検査も、全ての変換先で同じに行う。

`kumi test --backends all` は、全ての変換先で `render` の出力がビット一致することを検査する（適合性テスト）。

### 13.5 言語全体の変換（最終目標）

言語全体を変換できるようにするため、言語機能は次の制約の下で設計する。

- **変換方法の無い機能は入れない**（P7）。機能を追加するときは、C、C++、Rust、JavaScript への変換方法を示す。
- **意味は変換先によって変わらない。** 変わるのは性能だけにする。変わる場合は、下の「既知の差」に挙げて解消の方針を決める。

現在の機能の変換方法:

| 機能 | 変換方法 | 0.2 の設計がそれを可能にしている点 |
|---|---|---|
| ジェネリクス、trait | 単相化して、普通の関数にする | 動的ディスパッチ（トレイトオブジェクト）が無い |
| 効果と handler | handler を構造体（関数の表）にし、隠れた引数として渡す（証拠渡し） | handler は末尾再開のみ。継続の捕捉が要らないので、関数ポインタかクロージャがあればどの言語でも書ける |
| 捕捉するクロージャ | 各言語の無名関数、または関数 + 環境の構造体 | 第二級なので、環境の寿命が呼び出しの中に収まる |
| Shared 型（`Str`、`Array` など） | C / C++ / Rust: 参照カウント。GC のある言語: 変換先の GC に任せる | 値が不変なので、参照カウントでも GC でも観測できる意味は同じ。一意な値のその場での更新（Perceus）は最適化にすぎない |
| Affine 型と `Drop` | 破棄の位置で明示的に `drop` を呼ぶコードを出す。GC のある言語でもファイナライザに頼らない | 破棄の位置がコンパイル時に全て決まる |
| `inout` / `move` | `inout` はポインタ・参照・変換先の可変引数、または値を返して書き戻す。`move` は所有権の移動か、ただの受け渡し | 参照が第二級で、ライフタイムが無い |
| `rt`、`Alloc` の検査 | 変換前に Kumi のコンパイラが検査済み。変換先では何もしない | 検査はシグネチャで閉じる |
| ブロックする効果 | ブロックできない変換先（JavaScript）では、効果行に `blocking` の効果を含む関数を `async` 関数にし、呼び出しを `await` にする | ブロックするかどうかが効果行だけで決まる（§8.2） |
| `Str` | UTF-8 の変換先ではそのまま。JavaScript では UTF-8 のバイト列（`Uint8Array`）で持ち、JS の API との境界で変換する。リテラルは変換時に符号化しておく | 長さと位置をバイト単位で定義した（§4.2） |
| `Map` / `Set` | 挿入順を保つ表（JS の `Map`、C / Rust では挿入順の索引付き表） | 反復の順序を挿入順と定義した（§4.3） |
| panic | C: ターゲットの panic 設定。C++ / Rust / JS: 回復しない例外や abort に対応させる | panic は回復可能なエラーと分かれている（`Result`） |
| `target` 宣言 | 変換先ごとの実装モジュールを `bind` で割り当てる | ソースに `cfg` が無い |

既知の差（未解決、§19）:

- **言語ごとの FFI**: `extern "C"` は C 系の変換先でしか使えない。`extern "js"` のように変換先ごとの extern を設けるかどうか。
- **64 ビット整数**: JavaScript の `Number` では `I64` / `U64` を表せない。`BigInt` か 2 語での模倣が要り、遅い。
- **JavaScript での文字列の性能**: `Str` を UTF-8 のバイト列で持つので、JS の API との受け渡しのたびに変換のコストがかかる（意味は揃う）。
- **arena の枯渇**: 確保量は変換先のメモリ表現で変わるので、arena の枯渇（panic）が起こる点が変換先によってずれうる。

---

## 14. FFI

### 14.1 C 関数の呼び出し

```kumi
extern "C" lib "fastconv" {
  type FcRaw                                                // 不透明型
  fn fc_new(ir: Span[F32], block: U32) -> Ptr[FcRaw] uses {Alloc}
  rt fn fc_process(h: Ptr[FcRaw], input: Span[F32], inout output: Span[F32])
  fn fc_free(h: Ptr[FcRaw]) uses {Alloc}
}
```

- extern ブロックの中の `type 名前`（`=` なし）は不透明型の宣言。
- extern 宣言の **効果行と `rt` は検証されない主張**。C 側がヒープを使うなら `uses {Alloc}`、ブロックするなら `uses {Block}` と宣言する。`kumi audit` が一覧にし、ポリシー（§15.4）で許可されたパッケージにしか書けない。
- `unsafe` を必要としない引数型は、スカラ、`CSize`、`@repr(c)` 構造体、`Span[T]`（ポインタ + 長さとして渡し、呼び出し中だけ有効）、借用した `Str`（読み取り専用）。
- `CSize` は C の `size_t` で、extern の宣言の中でだけ使える。Kumi 側では `U32` として見え、`U32` に収まらない値が返ると panic する。
- `Ptr[T]` を引数や返り値に含む extern 関数は、`unsafe { }` の中でしか呼べない。

安全なラッパの例:

```kumi
pub struct Conv {
  h: Ptr[FcRaw],
}

impl Drop for Conv {
  fn drop(move self) uses {Alloc} {
    unsafe { fc_free(self.h) }
  }
}

impl Conv {
  pub fn new(ir: Span[F32], block: U32) -> Conv uses {Alloc} {
    Conv { h: unsafe { fc_new(ir, block) } }
  }

  pub rt fn process(inout self, input: Span[F32], inout output: Span[F32]) {
    unsafe { fc_process(self.h, input, inout output) }
  }
}
```

`Conv` の破棄は `Alloc` を要し、rt でない。したがって `rt` 関数の中では `inout` でしか扱えず、解放は必ず非 rt の文脈で起こる。

### 14.2 export

関数は `export "C"` で C の ABI に出す。

```kumi
export "C" fn kumi_version() -> U32 { 2 }
```

flow はソースではなくマニフェストの `[export]`（§15.3）で export する。export する場所を一つにするためである。生成されるヘッダは次の通り（`voice` は §17.4 の flow。数値は例）。

```c
/* kumi_voice.h（kumi build が生成する） */
#include "kumi.h"                 /* kumi_param_info などの共通定義 */

#define KUMI_VOICE_SIZE       48      /* fast 領域のバイト数 */
#define KUMI_VOICE_BULK_SIZE  0       /* bulk 領域のバイト数 */
#define KUMI_VOICE_ALIGN      8

typedef struct kumi_voice kumi_voice;
typedef struct { float f0; float vowel_f1; float vowel_f2; float gain; } kumi_voice_params;

/* Config が空なので引数は sample_rate のみ。bulk は BULK_SIZE が 0 なら NULL でよい */
void kumi_voice_init(kumi_voice* s, void* bulk, float sample_rate);
void kumi_voice_reset(kumi_voice* s);
void kumi_voice_params_default(kumi_voice_params* p);
int  kumi_voice_process(kumi_voice* s, const kumi_voice_params* p,
                        float* out, size_t frames);
     /* 0: ok, 1: poisoned, 2: 入出力の部分的な重なり */

extern const kumi_param_info kumi_voice_param_info[4];   /* @param のメタデータ */

/* Alloc を提供するターゲットだけで生成される */
kumi_voice* kumi_voice_new(float sample_rate);
void        kumi_voice_free(kumi_voice* s);
```

- メモリは呼び出し側が用意する。`_new` / `_free` は、ヒープのあるターゲットでの便宜にすぎない。
- 入力と出力のバッファは、完全に同じポインタ（in-place 処理）であってよい。部分的な重なりは検出して 2 を返す。
- export した flow を、既存の C/C++ ホスト（JUCE, CLAP, VST3, AU, 組込み HAL）へ組み込む第一の経路とする。組込みでの使い方は §17.5。

---

## 15. モジュール・パッケージ・ターゲット

### 15.1 モジュール

- 1 ファイル = 1 モジュール。モジュールのパスはパッケージルートからのファイルパスで、`mod` 宣言は無い。
- 可視性は `pub`（パッケージ外に公開）と `pub(pkg)`（パッケージ内に公開）。無指定はモジュール内のみ。
- `use std.fs.{Fs, Path}`。グロブ import は無い。再公開は `pub use` のみ。
- モジュール間の循環 import は禁止（E0310）。
- 暗黙の prelude は `Option Result Some None Ok Err` と組込み型だけ。

### 15.2 target 宣言（条件コンパイルの代替）

```kumi
// audio/device.kumi
target type Device
target fn open(sample_rate: F32) -> Result[Device, DeviceError]
target rt fn read_input(inout d: Device, inout buf: Span[F32])
```

`target` 宣言は、**実装をビルドターゲットが与える** 宣言である。実装モジュールはターゲットごとにマニフェストの `bind` で割り当てる（OCaml/dune の virtual library と同じ考え方）。ソースの中に `#if` や `cfg` は無いので、**ソースの意味はターゲットによって変わらない**。

実装モジュールは、同じ名前と同じシグネチャ（`rt` と効果行を含む）の宣言を持たなければならない。これは検査される。検証されない主張である `extern "C"` とは、この点で異なる。

### 15.3 マニフェスト `kumi.toml`

```toml
[package]
name = "voice"
edition = "2026"

[dependencies]
std = "0.2.0"           # 完全一致。解決結果は kumi.lock に固定する

[export]
prefix = "kumi_"        # C のシンボルは prefix + flow 名
flows = ["voice", "echo"]

[targets.cli]
kind = "exe"
platform = "macos-arm64"
numeric = "strict"
provides = ["Fs", "Stdout", "Clock", "Alloc"]

[targets.plugin]
kind = "clap"
platform = "macos-arm64"
numeric = "strict"
provides = ["Alloc"]

[targets.web]
kind = "source"
lang = "js"             # 移植可能な核だけを変換する（§13）
numeric = "strict"

[targets.daisy]
kind = "staticlib"
platform = "thumbv7em-none-eabihf"
numeric = "strict-ftz"
provides = []           # ヒープ無し
panic = "trap"
panic_messages = false
main_frame = "static"

[targets.daisy.memory]
bulk_threshold = 4096   # 4 KiB 以上の配列は bulk 領域へ（§12.4）

[targets.daisy.bind]
"audio.device" = "daisy_hal.audio"
```

**ターゲット** は次の組で定義する。

1. プラットフォーム（トリプル）。`kind = "source"` では変換先の言語（`lang`）
2. 数値プロファイル
3. 提供する handler の集合（`provides`）。`Alloc` を含むかどうかで、ヒープの有無が決まる
4. `target` 宣言の割り当て（`bind`）
5. エントリの種類（`exe`, `clap`, `vst3`, `au`, `wasm-worklet`, `staticlib`, `source`）
6. メモリの設定（`bulk_threshold`、`main_frame`）と panic の設定

- `main` または export される関数の効果行に、`provides` に無い効果が含まれていれば E0610。
- `[export]` の flow は、`staticlib`・プラグイン・`source` のターゲットに出力される。
- ビルドはハーメティック（ネットワークも環境変数も読まない）で、`kumi.lock` が同じなら成果物は同一。

### 15.4 ポリシー `kumi.policy`

人間の判断に残すもの（効果の付与、unsafe、公開インタフェース）は、ソースとは別のファイルに集める。

```toml
[effects]
main = ["Fs", "Stdout", "Alloc"]   # main の効果行がこれを超えたら E0620

[unsafe]
packages = ["daisy_hal"]           # unsafe / extern を書けるパッケージ

[interface]
frozen = ["voice"]                 # 公開シグネチャとパラメータ ID の変更は E0630
```

`kumi check` はポリシーへの違反をエラーにする。`kumi audit` はポリシーと unsafe・extern の差分を表示する。運用では、エージェントにこのファイルの書き込み権限を与えない。

### 15.5 数値プロファイル

| プロファイル | 内容 | 再現性 |
|---|---|---|
| `strict`（既定） | IEEE 754、最近接偶数丸め、FMA への縮約なし、再結合なし、非正規化数あり。`std.math` は Kumi 自身で実装され、libm を使わない。 | 同じ入力なら全ターゲット・全変換先でビット一致 |
| `strict-ftz` | `strict` + 非正規化数をゼロに（FTZ / DAZ） | FTZ をサポートするターゲット間でビット一致 |
| `relaxed` | FMA と再結合を許可（ベクトル化のため） | 保証しない |

`relaxed` はターゲット全体には指定できない。flow や関数ごとに `@relaxed` で付け、`kumi audit` に列挙される。

---

## 16. 並行性

- **構造化並行性**: `task.scope(fn(s) { ... })` の中で `s.spawn(...)` したタスクは、スコープを抜ける前に必ず合流する。`Spawn` 効果（`blocking`）を要求する。
- データ競合は型で排除する。スレッド間で共有できるのは Copy 値と Shared 値（不変）、および同期型だけ。Affine 値は `move` で一つのタスクに移す。
- 同期型（`std.sync`）:

| 型 | 用途 | rt で使える操作 |
|---|---|---|
| `Chan[T]` | 一般のメッセージング。`send` / `recv` は `uses {Sync}` | なし |
| `Spsc[T, const N: U32]` | 単一生産者・単一消費者の lock-free キュー（容量固定） | `push`, `pop` |
| `Atomic[T]` | `T: Copy`。大きさはターゲットが lock-free で扱える幅まで（超えるとビルド時に E0650） | `load`, `store`, `swap` |
| `Swap[T]` | `T: Copy`。トリプルバッファで最新値を受け渡す | `latest` |

- 同期型の生成は、共有のためにヒープを使う（`Alloc`）。ヒープの無いターゲットで静的領域に置く方法は未決定（§19）。

オーディオスレッドと制御スレッドの典型的な接続:

```kumi
// 制御スレッド側（非 rt）
params.publish(voice.Params { f0: 110.0, vowel_f1: 700.0, vowel_f2: 1220.0, gain: 0.5 })

// オーディオコールバック（rt）
pub rt fn on_audio(inout st: voice.State, params: Swap[voice.Params], inout out: Span[F32]) {
  voice.process(inout st, params.latest(), inout out)
}
```

async / await は v0.2 には無い（§19）。

---

## 17. 例

この節の例は、§2〜§16 の規則に対して手で検査してある。

### 17.1 純粋な計算

```kumi
pub fn gcd(a: U64, b: U64) -> U64 {
  var x = a
  var y = b
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

test "gcd" {
  assert gcd(12, 18) == 6
  assert gcd(7, 0) == 7
}
```

### 17.2 効果・エラー・handler によるテスト

```kumi
use std.fs.{Fs, Path, IoError}
use std.text.{count_lines}

@derive(Eq, Show)
pub enum ConfigError {
  Io(IoError),
  Empty,
}

pub fn line_count(path: Path) -> Result[U64, ConfigError] uses {Fs, Alloc} {
  let text = Fs.read(path).map_err(ConfigError.Io)?
  if text.is_empty() {
    return Err(ConfigError.Empty)
  }
  Ok(count_lines(text))
}

handler empty_fs: Fs {
  fn read(_: Path) -> Result[Str, IoError] { Ok("") }
  fn write(_: Path, _: Str) -> Result[(), IoError] { Ok(()) }
}

test "empty file is an error" {
  let r = handle { line_count(Path.new("x.txt")) } with empty_fs
  assert r == Err(ConfigError.Empty)
}
```

`line_count` は `Fs.read` から受け取った `Str` を本体の終わりで破棄するので、`Alloc` を要する。

### 17.3 二極レゾネータ

```kumi
use std.math.{exp, cos}
use std.dsp.test.{impulse, energy}

/// 二極レゾネータ。極は r·e^{±jw} にあり、bw > 0 なら |r| < 1 で安定。
/// 入力に (1 - r) を掛けて、ピークのゲインをおおよそ正規化する。
pub flow resonator(x: Sig[F32], fc: Ctl[F32], bw: Ctl[F32]) -> Sig[F32] {
  let r  = exp(-(F32.PI * bw) / sample_rate())        // Ctl
  let w  = (2.0 * F32.PI * fc) / sample_rate()        // Ctl
  let b1 = 2.0 * r * cos(w)                           // Ctl
  let b2 = r * r                                      // Ctl
  let y1 = prev(y, 0.0)                               // Sig: y は下で定義される（過去の値）
  let y2 = prev(y1, 0.0)                              // Sig
  let y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)    // Sig: y[n] = g·x + b1·y[n-1] − r²·y[n-2]
  y
}

test "resonator decays" {
  let o = resonator.render(resonator.Config {},
                           resonator.Params { fc: 500.0, bw: 100.0 },
                           impulse(48000), 48000, 48000.0)
  assert energy(o.out, 47000, 48000) < 1.0e-12
}
```

- 順序: `prev(y, 0.0)` だけが前方の `y` を参照する。遅延を通るので合法（§11.2）。
- レート: `r w b1 b2` は Ctl なので、ブロックごとに 1 回だけ計算される。
- 演算子: どの式も、同じ群の連鎖か括弧付きの混在だけを使っている。`-(F32.PI * bw)` は前置の `-`。
- 状態: `y1` と `y2` の 2 つの F32。`resonator.SIZE` はコンパイル時に決まる。

### 17.4 声の flow

```kumi
// §17.3 と同じモジュール（resonator を参照する）
use std.math.{floor, exp}

/// 素朴なのこぎり波（エイリアシングあり。例示用）
pub flow saw(f0: Ctl[F32]) -> Sig[F32] {
  let phase = wrap01(prev(phase, 0.0) + (f0 / sample_rate()))
  (2.0 * phase) - 1.0
}

pub rt fn wrap01(x: F32) -> F32 {
  x - floor(x)
}

/// Ctl 値を、時定数 time 秒の一次遅れで Sig に滑らかにする
pub flow smooth(x: Ctl[F32], time: Init[F32]) -> Sig[F32] {
  let a = exp(-1.0 / (time * sample_rate()))        // Init: init で 1 回
  let y = x + (a * (prev(y, 0.0) - x))
  y
}

pub flow voice(
  @param(min: 20.0, max: 2000.0, default: 110.0, unit: "Hz", scale: "log")
  f0: Ctl[F32],
  @param(min: 200.0, max: 1200.0, default: 700.0, unit: "Hz")
  vowel_f1: Ctl[F32],
  @param(min: 600.0, max: 3000.0, default: 1220.0, unit: "Hz")
  vowel_f2: Ctl[F32],
  @param(min: 0.0, max: 1.0, default: 0.5)
  gain: Ctl[F32],
) -> Sig[F32] {
  let src = saw~(f0)
  let f1  = resonator~(src, vowel_f1, 80.0)         // 80.0: 定数から Ctl へ昇格
  let f2  = resonator~(src, vowel_f2, 120.0)
  (f1 + f2) * smooth~(gain, 0.01)
}
```

flow の中で、`~` の付いた `saw` `resonator` `smooth` は状態を持つインスタンス、`wrap01` `exp` `floor` は状態を持たない関数である。呼び出しの形だけで区別できる。

遅延線を持つ例:

```kumi
const MAX_ECHO: U32 = 96000                       // 48 kHz で 2 秒、96 kHz で 1 秒

pub flow echo(
  x: Sig[F32],
  @param(min: 0.01, max: 1.0, default: 0.3, unit: "s")
  time: Ctl[F32],
  @param(min: 0.0, max: 0.95, default: 0.5)
  feedback: Ctl[F32],
) -> Sig[F32] {
  let d = time * sample_rate()                      // Ctl（サンプル数）
  let y = x + (feedback * vdelay(y, d, MAX_ECHO, 0.0))
  y
}
```

`echo` の遅延線（約 384 KB）は `bulk_threshold` を超えるので bulk 領域に入る。`KUMI_ECHO_BULK_SIZE` はコンパイル時に決まり、組込みでは外部 SDRAM に置ける。

ホスト側（Kumi で WAV に書き出す）:

```kumi
use std.fs.{Fs, Path, IoError}
use std.audio.wav

pub fn render_vowel(path: Path) -> Result[(), IoError] uses {Fs, Alloc} {
  let sr: F32 = 48000.0
  var st = voice.init(voice.Config {}, sr)
  var out: Buf[F32] = Buf.zeroed(48000)
  voice.process(inout st, voice.params_default(), inout out)
  wav.write(path, out, sr)
}
```

`out` は `Buf` で、本体の終わりで破棄されるので `Alloc` が要る。`st` は固定サイズの値で、ヒープを使わない。

### 17.5 組込み: C のホストから使う

`daisy` ターゲット（ヒープ無し、§15.3）で `voice` を静的ライブラリにし、C のファームウェアから呼ぶ。

```c
#include "kumi_voice.h"

static uint8_t voice_mem[KUMI_VOICE_SIZE] __attribute__((aligned(KUMI_VOICE_ALIGN)));
static kumi_voice* voice;
static kumi_voice_params params;

void setup(void) {
  voice = (kumi_voice*)voice_mem;
  kumi_voice_init(voice, NULL, 48000.0f);       /* BULK_SIZE が 0 なので NULL */
  kumi_voice_params_default(&params);
}

void audio_callback(const float* const* in, float* const* out, size_t frames) {
  kumi_voice_process(voice, &params, out[0], frames);
}
```

ヒープもスタック上の大きな値も使わない。必要なメモリの量はヘッダの定数で分かり、リンク時に確定する。

### 17.6 DSP 以外のコード: ポリフォニー

FAUST ではボイスの割り当てを言語の外（アーキテクチャファイル）で書く。Kumi では同じ言語で書け、rt とヒープ不使用が検査される。

```kumi
use std.array
use std.math.{exp2}

const MAX_VOICES: U32 = 8

pub struct Poly {
  voices: [voice.State; MAX_VOICES],
  params: [voice.Params; MAX_VOICES],
  notes: [Option[U8]; MAX_VOICES],
  next: U32,
}

pub rt fn midi_to_hz(note: U8) -> F32 {
  440.0 * exp2(((note as F32) - 69.0) / 12.0)
}

impl Poly {
  pub fn new(sample_rate: F32) -> Poly {
    Poly {
      voices: array.from_fn(fn(_) { voice.init(voice.Config {}, sample_rate) }),
      params: [voice.params_default(); MAX_VOICES],
      notes: [None; MAX_VOICES],
      next: 0,
    }
  }

  /// 空きを探さず、順番に割り当てる（最も古い発音を奪う）
  pub rt fn note_on(inout self, note: U8, velocity: F32) {
    let i = self.next
    self.notes[i] = Some(note)
    self.params[i].f0 = midi_to_hz(note)
    self.params[i].gain = velocity
    voice.reset(inout self.voices[i])
    self.next = (i + 1) % MAX_VOICES
  }

  pub rt fn note_off(inout self, note: U8) {
    for i in 0..MAX_VOICES {
      if self.notes[i] == Some(note) {
        self.notes[i] = None
        self.params[i].gain = 0.0                   // smooth により 10 ms で減衰する
      }
    }
  }

  pub rt fn process(inout self, inout out: Span[F32], inout scratch: Span[F32]) {
    out.fill(0.0)
    for i in 0..MAX_VOICES {
      voice.process(inout self.voices[i], self.params[i], inout scratch)
      out.add_from(scratch)
    }
  }
}
```

- `Poly.new` は効果を持たない。`Poly` は固定サイズの値で、その大きさは `kumi interface` に出る。
- `self.voices[i]`（`inout`）と `self.params[i]`（借用）は異なるフィールドなので重ならない（§5.2）。
- `array.from_fn` に渡す無名関数は `sample_rate` をコピーで捕捉する。引数の位置だけで使うので、ヒープを使わない（§5.3）。

---

## 18. 診断とツール

### 18.1 診断

```json
{
  "code": "E0811",
  "message": "`resonator` is a flow; calling it creates a stateful instance and needs `~`",
  "span": { "file": "dsp/voice.kumi", "line": 12, "col": 13, "end_col": 22 },
  "found": "resonator(src, vowel_f1, 80.0)",
  "fixes": [
    { "replace": "resonator~(src, vowel_f1, 80.0)" }
  ]
}
```

| 範囲 | 分類 |
|---|---|
| E00xx | 字句・構文・演算子の群 |
| E03xx | モジュール・名前解決・シャドーイング・循環 |
| E04xx | 型・アリティ・フィールド・リテラルの型 |
| E05xx | 網羅性 |
| E06xx | 効果・`Alloc`・ターゲットの provides・ポリシー |
| E07xx | 引数モード・排他性・Affine・第二級の値 |
| E08xx | flow（順序と因果性・レート・遅延・@param・`~`） |
| E09xx | rt |
| E10xx | FFI・unsafe・トランスパイル |

- **型付きホール**: 式の位置に `_` を書くと、期待される型、使える効果、スコープ内の候補が報告され、ビルドは失敗する。
- エラーは **最初に検出された関数の中** で止まる（P1）。
- 既存言語の書き方（`&mut x`、`<T>`、`::`、`;`、`i32`、`proc`、FAUST の `+ ~ _`）には、Kumi での書き方を修正候補として示す。

### 18.2 コマンド

| コマンド | 内容 |
|---|---|
| `kumi check [--json]` | 型・効果・rt・flow・ポリシーの検査 |
| `kumi fmt [--check]` | 唯一の表記への正規化 |
| `kumi test [--backends all]` | `test` と `prop` を実行。`--backends` で変換先間のビット一致も検査（§13.4） |
| `kumi interface <mod>` | 公開シグネチャ、種、大きさ、効果、rt、@param だけを出力 |
| `kumi audit [--stack] [--memory]` | extern、unsafe、`@relaxed`、ポリシーとの差分。スタックの上限と flow の状態の大きさ |
| `kumi graph <flow>` | flow の信号グラフ（SVG / DOT）。ノード名は `let` の名前 |
| `kumi transpile <target>` | 各言語のソースへ変換。段階 1 では移植可能な核だけ（§13） |
| `kumi play <flow>` | flow を音で鳴らす。@param から UI を作る |
| `kumi probe <flow>.<name>` | 名前の付いた信号をタップし、波形とスペクトルを表示する |
| `kumi diff --ast` | 構造的な差分 |
| `kumi explain <code>` | 診断コードの説明と修正例 |
| `kumi primer [--std]` | この版の言語要約と標準ライブラリのインタフェースを、LLM のコンテキスト向けに出力 |
| `kumi lsp` | LSP。DSP 向けの拡張（グラフ、パラメータ、プローブ、ホットリロード）を含む |

### 18.3 IDE

FAUST の IDE に相当する環境は、`kumi lsp` の上に作る。言語の側で次を保証する。

- **局所的な検査**: シグネチャが全て注釈されているので、編集した関数だけを検査し直せばよい。
- **パラメータの UI**: `@param` から自動で作る。パラメータの一覧はシグネチャだけで分かる。
- **プローブ**: 全ての信号に名前があるので、ソースを変えずに任意の信号を観測できる。
- **ホットリロード**: 状態のフィールドは `let` の名前を持つ。再コンパイルの後、名前と型が一致するフィールドは状態を引き継ぎ、それ以外は `init` で初期化する。
- **試聴**: IDE は C バックエンド（デスクトップ）または WASM（ブラウザ）で flow を実行する。`strict` なら、試聴した音と組込み機器で鳴る音はビット一致する。

---

## 19. 未決定事項

- マルチレート: オーバーサンプリング、FFT / STFT、リサンプリング（明示的なクロックの導入を検討中）
- flow の `Ctl` 出力（エンベロープの終了通知など）と、`Sig` 入力に struct を使うこと
- 分岐の中の flow インスタンスを停止させるか（クロック付きの `if`）
- 単位の型（`Hz`, `Sec`, `Samples` を newtype ではなく単位代数で扱う）
- 固定小数点型（`Q15`, `Q31`、飽和演算）を標準ライブラリに置くか、言語に入れるか
- Kumi で書いたファームウェアのエントリ: 割り込みとメインループが状態を共有する方法（同期型を静的領域に置く方法を含む）
- `Alloc` の確保失敗を、panic ではなく値として扱う API
- ホットリロードで、型の変わったフィールドの扱い
- 変換先の優先順位（C の次に何を作るか）
- 言語全体の変換（段階 2）の既知の差: 言語ごとの FFI、JavaScript の 64 ビット整数と文字列の性能、arena の枯渇（§13.5）
- 逃げるクロージャ（保存できるコールバック）、トレイトオブジェクト
- async / await
- 実装しない機能の一覧を、拒否の理由とともに保守すること

---

## 20. 実装の順序

コンパイラは Rust で書く。ブラウザの IDE で動かすため、WASM にもビルドできるようにする。

**第 1 期: 移植可能な核（§13.2）だけを実装する。** 効果、handler、Shared 型、参照カウントは作らない。核だけでも、C の export、組込み、IDE での試聴という「FAUST の代わり」に要るものが揃う。

1. 核の構文解析器と検査器（`kumi check --json`、型付きホール）。本仕様の例のうち核に入るものが全て通ることを、最初の回帰テストにする。
2. インタプリタ（`kumi test`、`render`）
3. flow の降下（順序と因果性、レートの巻き上げ、状態の配置）
4. C バックエンドと export。ヒープ無し、静的な大きさ、fast / bulk の二領域。組込みとプラグインの入口が一度に得られる。
5. IDE の核: `kumi lsp`、`play`、`probe`、`graph`、`@param` からの UI
6. JavaScript への変換（ブラウザでの試聴に要る）と、ビット一致の適合性テスト

**第 2 期: fn 世界。**

7. 効果と handler、`Alloc`、Shared 型と参照カウント、標準ライブラリ
8. LLVM と WASM のバックエンド
9. `interface` / `audit`（スタック、メモリ）/ `primer`

**第 3 期: 変換先の拡大。**

10. C++ と Rust への変換（段階 1）
11. 言語全体の変換（段階 2）。§13.5 の既知の差を解消した変換先から順に
