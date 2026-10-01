# Kumi 言語仕様 Draft 0.1

> Kumi（組み / 組紐）: 小さな部品を、検査可能な継ぎ目で組み上げる言語。

Ori Draft 0.1 と同じ目的、つまり「LLM が書き、人間が監査し、コンパイラが局所的に否定する」ための言語を、別の判断で設計し直したもの。Ori との比較は [`docs/comparison-ori-kumi.md`](docs/comparison-ori-kumi.md) を参照。

---

## 0. 目的と設計原則

### 0.1 目的

- LLM が本体を書き、人間がモジュール境界・効果・数値の意味を監査し、コンパイラが誤りを **局所・高速・決定的** に否定する。
- 汎用のアプリケーションコードと、リアルタイム信号処理（オーディオ DSP）を **一つの言語** で書ける。
- 既存のホスト（C/C++ プラグイン、組込み、WASM）に組み込める。

### 0.2 原則

| # | 原則 | 帰結 |
|---|---|---|
| P1 | **局所性** — 意味・型・エラーは関数の中で閉じる | 全関数のシグネチャは完全注釈。推論は関数本体の中だけ（双方向型検査）。関数をまたぐ推論はしない。 |
| P2 | **一意性** — 一つの意図に書き方は一つ | 糖衣を増やさない。同じ概念を二つ持たない。`kumi fmt` が唯一の表記に正規化する。 |
| P3 | **新規性の予算** — 新しさは意味論に使い、構文には使わない | 表面構文は Rust / Swift / Go の最大公約数に寄せ、LLM の事前知識を最大限使う。 |
| P4 | **世界への接触はシグネチャに出る** | 効果（`uses {...}`）で表す。仕組みは効果 + handler の一つだけ。 |
| P5 | **リアルタイム性は型で検査する** | `rt` 修飾。フラグやビルド単位ではなく関数単位。 |
| P6 | **修復ループは言語機能** | 安定診断コード、JSON 診断、型付きホール、インタフェース抽出、監査コマンド。 |
| P7 | **仕様の例は全て検査を通る** | 仕様内のコード例はプライマーとして LLM に渡される前提で書く。 |

### 0.3 非目標

- Rust の借用検査器を再現すること（参照は第二級に限定し、ライフタイムを持たない）
- 遅延評価、高階型、型レベル計算
- マクロによる構文拡張
- 「人間が小説のように読める」表面

---

## 1. 全体構成

```
.kumi ── parse ── resolve ── check (types / effects / rt / exclusivity / causality)
                                   │
                               Kumi Core（正準 IR）
                                   │
          ┌────────────────────────┼─────────────────────┐
       C backend               LLVM backend            WASM
 (export, 組込み, 既存ホスト)    (native)              (web audio)
```

言語は二つの宣言種別を持つが、式の構文は共通。

- **fn 世界**: 関数、型、trait、効果。通常のプログラム。
- **proc 世界**: 同期データフロー（Lustre 系）の信号処理ノード。Core の `fn` と `struct` に降下する（§11）。

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
fn rt proc struct enum trait impl effect handler handle with uses
let var if else match for in while break continue return
pub use extern export unsafe virtual test prop assert
const type as inout sink self Self true false
```

`prev` `delay` `vdelay` `sample_rate` は proc 内で予約された組込み名（§11.4）。

### 2.3 命名規則（エラー、lint ではない）

| 種類 | 規則 | 例 |
|---|---|---|
| 値・関数・proc・モジュール | `snake_case` | `one_pole`, `line_count` |
| 型・trait・効果・列挙子 | `UpperCamel` | `Buf`, `Ord`, `Fs`, `Some` |
| 型パラメータ | `UpperCamel` 1 語 | `T`, `Item` |
| 効果行変数 | `snake_case` 1 語 | `e` |
| 定数 | `UPPER_SNAKE` | `MAX_VOICES` |

名前の種別が字面で決まるので、`Fs.read(p)` が効果操作、`fs.read(p)` がモジュール関数であることが局所的に分かる。

### 2.4 リテラル

- 整数: `42`, `0xFF`, `0b1010`, `1_000_000`
- 浮動小数: `1.0`, `2.5e-3`（小数点の両側に数字が必須。`1.` や `.5` は不可）
- 文字: `'a'`（Unicode スカラ値）
- 文字列: `"..."`（UTF-8）。補間は `{名前}` または `{名前.フィールド...}` のみで、任意の式は書けない。補間される値は `Show` を実装していなければならない。`{{` と `}}` はエスケープ。
- 型は文脈から決まる。文脈が無い場合、整数は `I64`、浮動小数は `F64`。

### 2.5 文の区切り

- ブロック `{ }` の中では、改行で文が終わる。ただし行末のトークンが二項演算子、`=`、`->` の場合、または次の行が `.` で始まる場合は継続する。判定は隣接する 2 行で決まり、インデントは意味を持たない。
- 丸括弧・角括弧・構造体リテラル・`match` の腕の並びの中では、改行は空白として扱う（要素は `,` で区切る）。
- `else` は直前の `}` と同じ行に書く（E0003）。
- `;` は使わない。

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

前置の `-` と `!`、後置の呼び出し `f(x)`・フィールド `.f`・添字 `[i]`・`?` は、どの二項演算子よりも強く結合する。覚える表は無い。

### 3.2 演算子は trait に脱糖する

`+` は `Add.add`、`<` は `Ord.lt` など（§6.3）。オーバーロードはこの経路だけで、型ごとに実装は高々一つ。

### 3.3 変換

`as` は **情報を失わない拡大変換** だけに使える（`I32 as I64`、`F32 as F64`、`I32 as F64`、`U8 as I16` など。`I64 as F64` や `USize as F64` は値が失われうるので不可）。それ以外は、変換元の型のメソッドを使う。

```kumi
let n = i as I64                 // OK
let k = n.narrow_i32()           // I64 -> Option[I32]
let s = x.round_f32()            // F64 -> F32、最近接偶数丸め
let c = xs.len().round_f64()     // USize -> F64、最近接偶数丸め
let j = y.trunc_i32()            // F32 -> I32、範囲外は panic
```

`as` 式を二項演算子のオペランドにするときは括弧が必要（E0011）: `acc + (x as F64)`。

暗黙の数値変換は一切無い。唯一の暗黙変換は proc のレート昇格（§11.3）で、これは値を変えない。

---

## 4. 型

### 4.1 組込み型

| 分類 | 型 |
|---|---|
| 整数 | `I8 I16 I32 I64 U8 U16 U32 U64 ISize USize` |
| 浮動小数 | `F32 F64`（IEEE 754 binary32 / binary64） |
| その他スカラ | `Bool Char ()` |
| 文字列・バイト列 | `Str`（UTF-8, 不変）, `Bytes`（不変） |
| 固定長配列 | `[T; N]`（`N` はコンパイル時定数） |
| 列 | `Array[T]`（不変・永続、参照カウント） |
| バッファ | `Buf[T]`（アフィン、可変、長さ固定） |
| 集合 | `Map[K, V]`, `Set[T]` |
| 標準 enum | `Option[T]`（`Some` / `None`）, `Result[T, E]`（`Ok` / `Err`） |
| 関数 | `fn(A, B) -> R uses {E}` |
| FFI | `Ptr[T]`（保持はできるが、受け渡す extern の呼び出しは `unsafe` 内のみ、§12） |

`Option` と `Result` の列挙子だけは修飾なしで書ける。他の enum の列挙子は常に `Type.Variant` と書く。

### 4.2 ユーザ定義型

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
- フィールドアクセス `p.x` は、`p` の型が注釈またはその場の推論で既知であることを要求する（E0420）。型からフィールドを逆推論しない。

### 4.3 ジェネリクス

```kumi
pub fn clamp[T: Ord](x: T, lo: T, hi: T) -> T {
  if x < lo { lo } else if x > hi { hi } else { x }
}

pub struct Ring[T, const N: USize] {
  data: [T; N],
  head: USize,
}
```

- 宣言位置で `[...]`。呼び出し位置で型引数は書かない（期待型の注釈で決める）。このため、式の中の `[...]` は常に添字であり、構文が曖昧にならない。
- const ジェネリクスは等値比較のみ（`N + 1` のような型レベル算術は無い）。
- 型パラメータは既定で Copy か Shared の型しか受け付けない。Affine 型も受け付けるには `[T: Move]` と宣言する。その場合、`T` の値は借用・`inout`・`sink` でしか扱えない（返り値として借用を複製することはできない）。
- `Buf[T]` の要素型は `T: Copy` に限る。

### 4.4 種（kind）: Copy / Shared / Affine

全ての型は構造から次のどれかに分類される。注釈は不要で、`kumi interface` に表示される。

| 種 | 該当 | コピー | 備考 |
|---|---|---|---|
| Copy | スカラ、Copy 要素の固定長配列・タプル・構造体 | ビットコピー | |
| Shared | `Str` `Bytes` `Array` `Map` `Set`、それらを含む型 | 参照カウントで共有、書き込み時コピー | 不変なので循環は生じない |
| Affine | `Buf`、`Drop` 実装型、proc の状態、それらを含む型 | 不可（ムーブのみ） | 暗黙に複製されない |

---

## 5. 値・変数・引数モード（可変値意味論）

### 5.1 束縛

```kumi
let x: I32 = 1     // 不変
var acc = 0.0      // 可変（ローカルのみ）。文脈が無いので F64
acc = acc + (x as F64)
```

- 代入は **値** の代入。`var b = a` の後で `b` を変えても `a` は変わらない（Shared 型は書き込み時コピー、一意なら in-place。Perceus 方式の参照カウント）。
- 参照は値として存在しない。したがってライフタイムも無い。

### 5.2 引数モード

| モード | 宣言 | 呼び出し位置 | 意味 |
|---|---|---|---|
| 借用（既定） | `x: T` | `f(x)` | 読み取り専用。呼び出し中は変更されない。 |
| `inout` | `inout x: T` | `f(inout x)` | 排他的な可変借用。呼び出し側は `var` であること。 |
| `sink` | `sink x: T` | `f(sink x)` | 所有権を受け取る。Affine 値はこの後使えない。 |

- `inout` と `sink` は **呼び出し位置にも書く**。読み手は呼び出し 1 行で、何が変わるかを知る。
- 同じ変数を一つの呼び出しで二度 `inout` に渡すとエラー（E0702）。
- メソッドのレシーバは `self` / `inout self` / `sink self` と宣言する。レシーバの `inout` は呼び出し位置に書かない（宣言から分かる）が、レシーバは `var` でなければならない。
- 借用は第二級。返り値や構造体のフィールドに保存できない。クロージャは値をコピーで捕捉し、`inout` 引数と Affine 値は捕捉できない。

---

## 6. 関数と trait

### 6.1 関数

```kumi
pub fn mean(xs: Array[F64]) -> Option[F64] {
  if xs.is_empty() {
    return None
  }
  Some(xs.sum() / xs.len().round_f64())
}
```

- 引数・返り値・効果は全て注釈する。返り値が `()` の場合だけ `->` を省略する（省略が唯一の書き方）。
- ブロックの値は最後の式。`return` は途中脱出にだけ使う（末尾の `return` は `kumi fmt` が除去する）。
- 多重定義、既定引数、可変長引数、名前付き引数は無い。
- 無名関数は `fn(x: F32) -> F32 { x * 2.0 }`。期待型が分かる位置では注釈を省略できる: `xs.map(fn(x) { x * 2.0 })`。

### 6.2 メソッド

```kumi
impl Point {
  pub fn new(x: F32, y: F32) -> Point { Point { x: x, y: y } }   // 関連関数: Point.new(...)
  pub fn norm(self) -> F32 { sqrt((self.x * self.x) + (self.y * self.y)) }
  pub fn scale(inout self, k: F32) {
    self.x = self.x * k
    self.y = self.y * k
  }
}
```

`impl` 内の関数はドット記法でのみ呼ぶ（`p.norm()`, `Point.new(1.0, 2.0)`）。自由関数は前置でのみ呼ぶ。同じ関数に二つの呼び方は無い。

### 6.3 trait

```kumi
pub trait Show {
  fn show(self) -> Str
}

impl Show for Point {
  fn show(self) -> Str { "({self.x}, {self.y})" }
}
```

- **一貫性**: `impl Tr for Ty` は `Tr` か `Ty` を定義したモジュールにしか書けない（孤児規則）。重複実装、特殊化は無い。
- ジェネリック trait（`Iter[T]` など）は、一つの型について高々一つしか実装できない。これにより関連型を別概念として持たずに済む。
- 既定メソッドは可。トレイトオブジェクト（動的ディスパッチ）は v0.1 には無い。動的な差し替えは効果 handler か関数値で行う。
- 演算子 trait: `Add Sub Mul Div Rem Neg Eq Ord BitAnd BitOr BitXor Shl Shr`。
- 標準 trait: `Eq`, `Ord`（演算子用。浮動小数は IEEE 比較）、`TotalOrd`（ソート・順序付き Map 用。浮動小数は実装しない）、`Hash`, `Show`, `Default`, `Iter[T]`, `IntoIter[T]`, `Drop`, `Num`, `Float`。

### 6.4 derive

```kumi
@derive(Eq, Hash, Show)
pub struct Key {
  id: U32,
}
```

`@derive` で書けるのは `Eq Ord TotalOrd Hash Show Default` の閉じた一覧だけ。ユーザ定義の derive やマクロは無い。

### 6.5 属性（全て）

`@derive(...)`, `@repr(c)`, `@relaxed`, `@deprecated("...")`。これ以外の属性は無い。

### 6.6 コンパイル時定数

```kumi
const TABLE_SIZE: USize = 1024
const SINE: [F32; 1024] = make_sine_table()   // 効果行が空の関数だけがコンパイル時に評価できる
```

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
- 範囲 `a..b` は `for` の見出しにしか書けない（演算子ではない）。
- 末尾呼び出しの最適化は **保証しない**。反復は `for` / `while` で書く。

---

## 8. 効果

### 8.1 宣言と使用

```kumi
pub effect Fs {
  fn read(path: Path) -> Result[Str, IoError]
  fn write(path: Path, data: Str) -> Result[(), IoError]
}

pub fn load(path: Path) -> Result[Str, IoError] uses {Fs} {
  Fs.read(path)
}
```

- 効果行は **効果単位**（`Fs`）で書く。操作単位ではない。粒度が必要なら効果を分ける（標準ライブラリは `FsRead` と `FsWrite` を分けている。本仕様の例では簡単のため `Fs` を使う）。
- 効果行が空なら `uses` を書かない。それが純粋関数。
- 効果の多相:

```kumi
pub fn map[T, U, e](xs: Array[T], f: fn(T) -> U uses {e}) -> Array[U] uses {e} { ... }
```

### 8.2 暗黙の効果: `Alloc` と `Block`

- `Alloc`（ヒープ確保・解放）と `Block`（ロック、システムコール、待機）は、`rt` でない全ての関数に **暗黙に含まれる**。書かない。
- `rt fn` はこの二つを含まない関数である（§10）。
- `Alloc` と `Block` は handler で処理できない。

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
- handler 自身が使う効果は、`handle` 式の効果行に加わる。
- インライン形式 `handle { ... } with Fs { fn read(...) ... }` も同じ意味。

### 8.4 main と実行環境

```kumi
pub fn main() -> Result[(), AppError] uses {Fs, Stdout} { ... }
```

`main` の効果行の各効果について、ビルドターゲットが handler を提供しなければならない（E0610、§13）。capability を値として渡す仕組みは無い。権限は効果行だけで表す。

時刻と乱数も効果（`Clock`, `Random`）。テストでは handler を差し替えるだけで決定的になる。

---

## 9. エラーと panic

### 9.1 回復可能なエラー

`Result[T, E]` と後置 `?`。

```kumi
pub fn line_count(path: Path) -> Result[U64, ConfigError] uses {Fs} {
  let text = Fs.read(path).map_err(ConfigError.Io)?
  ...
}
```

`?` は、関数の返り値の `E` と **同じ型** のエラーにしか使えない。暗黙の変換（`From` 相当）は無い。変換は `map_err` で明示する。

### 9.2 panic（バグ）

次の場合は panic する。

- 整数のオーバーフロー（`+ - *`。ラップアラウンドは `wrapping_add` などで明示する）
- 整数のゼロ除算
- 範囲外の添字アクセス `xs[i]`（範囲外を許す取得は `xs.get(i)` で、`Option` を返す）
- `unwrap`、`assert` の失敗、`panic(msg)`

panic は効果行に現れない。挙動はビルド設定に依存せず、常に同じ。

| 文脈 | panic の挙動 |
|---|---|
| 通常の実行 | メッセージと位置を出力してプロセスを終了する（巻き戻しは無い） |
| テスト | そのテストを失敗にする |
| `rt` 関数（proc の `process` を含む） | その呼び出しを中断し、出力バッファをゼロで埋め、インスタンスを **poisoned** にする。以後の `process` は無音を出力し、`reset` まで復帰しない。export された C API は戻り値で通知する。 |
| export された関数 | panic は FFI 境界を越えない。エラーコードに変換する。 |

---

## 10. リアルタイム（`rt`）

```kumi
pub rt fn soft_clip(x: F32) -> F32 {
  x / (1.0 + abs(x))
}
```

`rt fn` の検査規則は次の通り（違反は E09xx）。

1. 効果行に `Alloc` と `Block` を含まない。`rt` でない関数は呼べない。
2. Shared 型の値を **生成・変更しない**（読み取りの借用は可）。
3. 所有している Affine 値を、`Drop` を伴ってスコープ外に出さない（`inout` で受け取って操作する）。
4. ループの上限は検査しない（停止性は対象外）。

- `rt` は関数型の一部（`rt fn(F32) -> F32`）で、高階関数でも保持される。
- `extern` 宣言の `rt` は検証されない主張として扱い、`kumi audit` に列挙する（§12）。

参考: Clang の `[[clang::nonblocking]]` / `[[clang::nonallocating]]`（関数効果解析）と同種の検査を、言語の型に組み込んだもの。

---

## 11. proc: 信号処理

### 11.1 考え方

proc は **同期データフロー方程式** の集合（Lustre / SCADE 系）。FAUST と同じく、

- 状態は遅延にしか現れない
- 結線の誤りはコンパイル時に落ちる
- タイトなループに降下する

という性質を持つ。ただし point-free ではなく、**全ての信号に名前がある**。グラフは名前の参照関係そのもので、`kumi graph` で図にできる。

### 11.2 宣言

```kumi
pub proc one_pole(x: Sig[F32], p: Ctl[F32]) -> (y: Sig[F32]) {
  y = ((1.0 - p) * x) + (p * prev(y, 0.0))
}
```

- 入力は `(名前: レート型, ...)`、出力は `-> (名前: レート型, ...)`。
- 本体は方程式 `名前 = 式` の集合で、**順序に意味は無い**。`let` / `var` / 代入文は書けない（proc 本体であることが構文で分かる）。
- 各出力と各局所名は、ちょうど一度だけ定義する（E0802 未定義、E0803 二重定義）。
- 自己参照・相互参照は、`prev` / `delay` / `vdelay` を経由する場合だけ許される（因果性の検査、E0801）。

### 11.3 レート

| レート型 | 意味 | 評価のタイミング |
|---|---|---|
| `Const[T]` | 初期化時の定数 | `init` で 1 回 |
| `Ctl[T]` | ブロックレート | `process` の呼び出しごとに 1 回 |
| `Sig[T]` | サンプルレート | サンプルごと |

- レートは `Const < Ctl < Sig` の順に並ぶ。式のレートはオペランドのレートの最大値。
- 低いレートから高いレートへの昇格は暗黙に行う（値は変わらない。言語で唯一の暗黙変換）。高いレートから低いレートへの変換は無い。間引きが要る場合は明示的な proc（`sample_and_hold` など）を使う。
- コンパイラは各方程式を、そのレートに応じたループの外側へ巻き上げる。係数計算をサンプルループの外に出すことが、型から保証される。

### 11.4 組込み

| 名前 | 型（概略） | 意味 |
|---|---|---|
| `prev(e, init)` | `Sig[T] -> Sig[T]` | 1 サンプル遅延。最初のサンプルは `init` |
| `delay(e, N, init)` | `N: Const[USize]` | N サンプル遅延（固定長の状態） |
| `vdelay(e, d, MAX, init)` | `d: Sig[F32]`, `MAX: Const[USize]` | 可変遅延（線形補間）。`d` は `[0, MAX]` に飽和する |
| `sample_rate()` | `Const[F32]` | サンプルレート |

### 11.5 呼び出しの規則

proc 本体の中での呼び出しは、呼び出す相手によって意味が決まる。

| 呼び出す相手 | 意味 |
|---|---|
| 効果行が空の `rt fn` | 点ごとに適用する。結果のレートは引数のレートの最大値。 |
| `proc` | 呼び出し位置ごとに独立した状態を持つインスタンスを作る。 |
| 効果行が空の非 `rt` fn | `Const` レートの引数でのみ呼べる。`init` で評価される（テーブル生成などに使う）。 |
| 効果を持つ fn | 呼べない（E0805）。I/O はホスト側で行う。 |

- `if c { a } else { b }` は点ごとの選択。**両方の分岐の proc インスタンスは常に進む**（クロックによる停止は v0.1 には無い）。
- proc 本体の中に再帰呼び出しやループは無い。

### 11.6 Core との接続（生成される API）

`proc p(...) -> (...)` を宣言すると、コンパイラは名前空間 `p` に次を生成する。

```kumi
// 型
p.State                 // Affine。固定サイズ。遅延線もここに含まれる
p.Config                // Const 入力のフィールドを持つ struct（Copy）
p.Params                // Ctl 入力のフィールドを持つ struct（Copy）
p.Inputs                // Sig[T] 入力ごとに Buf[T] のフィールドを持つ struct
p.Outputs               // Sig[T] 出力ごとに Buf[T] のフィールドを持つ struct

// 関数
fn p.init(cfg: p.Config, sample_rate: F32) -> p.State
rt fn p.reset(inout s: p.State)
rt fn p.process(inout s: p.State, params: p.Params, input: p.Inputs,
                inout output: p.Outputs, frames: USize)
fn p.render(cfg: p.Config, params: p.Params, input: p.Inputs,
            frames: USize, sample_rate: F32) -> p.Outputs   // テストと一括処理用
```

- proc は第一級の値ではない。外から扱う手段は、この生成された名前空間だけ。
- `init` と `render` は `rt` でない（テーブルの生成や確保ができる）。`process` と `reset` は `rt`。
- `frames` が `input` / `output` のどれかのバッファ長を超えると panic する（§9.2 の poisoned）。
- 状態の所有者は呼び出し側。サンプルレートを変えるときは、`init` を呼び直して新しい状態を作る。
- v0.1 では、proc の出力は `Sig` だけ（`Ctl` 出力は未決定、§17）。

### 11.7 テスト用の補助

一括処理は生成された `p.render`（§11.6）で行う。`std.dsp.test` には次を置く。

- `impulse(n: USize) -> Buf[F32]`
- `magnitude_at(buf: Buf[F32], freq: F32, sample_rate: F32) -> F32`
- `energy(buf: Buf[F32], from: USize, to: USize) -> F64`（半開区間 `[from, to)` の二乗和）
- `assert_near(a: F64, b: F64, tol: F64)`

---

## 12. FFI

### 12.1 C 関数の呼び出し

```kumi
extern "C" lib "fastconv" {
  type FcRaw                                              // 不透明型
  fn fc_new(ir: Buf[F32], block: U32) -> Ptr[FcRaw]
  rt fn fc_process(h: Ptr[FcRaw], input: Buf[F32], inout output: Buf[F32])
  fn fc_free(h: Ptr[FcRaw])
}
```

- extern ブロックの中の `type 名前`（`=` なし）は不透明型の宣言。
- extern 宣言の **効果行と `rt` は検証されない主張**。`kumi audit` が一覧にし、ポリシー（§13.4）で許可されたパッケージにしか書けない。
- `unsafe` を必要としない引数型は、スカラ、`@repr(c)` 構造体、借用した `Buf[T]`（ポインタ + 長さとして渡し、呼び出し中だけ有効）、借用した `Str`（読み取り専用）。
- `Ptr[T]` を引数や返り値に含む extern 関数は、`unsafe { }` の中でしか呼べない。
- Affine 値を C 側に保持させる正規の手段は無い。保持が必要なら、`unsafe` の中で C 側が自分で確保・複製する。

安全なラッパの例:

```kumi
pub struct Conv {
  h: Ptr[FcRaw],
}

impl Drop for Conv {
  fn drop(sink self) {
    unsafe { fc_free(self.h) }
  }
}

impl Conv {
  pub fn new(ir: Buf[F32], block: U32) -> Conv {
    Conv { h: unsafe { fc_new(ir, block) } }
  }

  pub rt fn process(inout self, input: Buf[F32], inout output: Buf[F32]) {
    unsafe { fc_process(self.h, input, inout output) }
  }
}
```

`Conv` は `Drop` を実装しているので Affine になる。`rt` 関数の中では `inout` でしか扱えず、解放は必ず非 rt の文脈で起こる。

### 12.2 export

```kumi
export "C" fn kumi_version() -> U32 { 1 }

export proc voice as "kumi_voice"
```

`kumi build --emit c-header` は次のようなヘッダを生成する（`voice` は §15.4 の proc）。

```c
typedef struct kumi_voice kumi_voice;
typedef struct { float f0; float vowel_f1; float vowel_f2; float gain; } kumi_voice_params;

kumi_voice* kumi_voice_new(float sample_rate);           /* Config が空なので引数は sample_rate のみ */
void        kumi_voice_reset(kumi_voice* s);
int         kumi_voice_process(kumi_voice* s, const kumi_voice_params* p,
                               const float* const* in, float* const* out, size_t frames);
                                                          /* 0: ok, 1: poisoned */
void        kumi_voice_free(kumi_voice* s);
```

proc の export を、既存の C/C++ ホスト（JUCE, CLAP, VST3, AU, 組込み HAL）へ組み込む第一の経路とする。

---

## 13. モジュール・パッケージ・ターゲット

### 13.1 モジュール

- 1 ファイル = 1 モジュール。モジュールのパスはパッケージルートからのファイルパスで、`mod` 宣言は無い。
- 可視性は `pub`（パッケージ外に公開）と `pub(pkg)`（パッケージ内に公開）。無指定はモジュール内のみ。
- `use std.fs.{Fs, Path}`。グロブ import は無い。再公開は `pub use` のみ。
- モジュール間の循環 import は禁止（E0310）。
- 暗黙の prelude は `Option Result Some None Ok Err` と組込み型だけ。

### 13.2 virtual モジュール（条件コンパイルの代替）

```kumi
// audio/device.kumi
virtual type Device
virtual fn open(sample_rate: F32) -> Result[Device, DeviceError]
virtual rt fn read_input(inout d: Device, inout buf: Buf[F32])
```

`virtual` 宣言だけを持つモジュールは、インタフェースだけを定める。実装モジュールはターゲットごとにマニフェストで割り当てる（OCaml/dune の virtual library と同じ考え方）。ソースの中に `#if` や `cfg` は無いので、**ソースの意味はターゲットによって変わらない**。

### 13.3 マニフェスト `kumi.toml`

```toml
[package]
name = "voice"
edition = "2026"

[dependencies]
std = "0.1.0"           # 完全一致。解決結果は kumi.lock に固定する

[targets.cli]
kind = "exe"
platform = "macos-arm64"
numeric = "strict"
provides = ["Fs", "Stdout", "Clock"]

[targets.plugin]
kind = "clap"
platform = "macos-arm64"
numeric = "strict"
export = ["voice"]

[targets.daisy]
kind = "bare"
platform = "thumbv7em-none-eabihf"
numeric = "strict-ftz"
provides = ["Log"]

[targets.daisy.bind]
"audio.device" = "daisy_hal.audio"
```

**ターゲット** は次の 5 つ組で定義する。

1. プラットフォーム（トリプル）
2. 数値プロファイル
3. 提供する handler の集合（`provides`）
4. virtual モジュールの割り当て（`bind`）
5. エントリの種類（`exe`, `clap`, `vst3`, `au`, `wasm-worklet`, `bare`, `staticlib`）

`main` の効果行に、`provides` に無い効果が含まれていれば E0610 になる。ビルドはハーメティック（ネットワークも環境変数も読まない）で、`kumi.lock` が同じなら成果物は同一。

### 13.4 ポリシー `kumi.policy`

§0 で人間の判断に残したもの（効果の付与、unsafe、公開インタフェース）は、ソースとは別のファイルに集める。

```toml
[effects]
main = ["Fs", "Stdout"]          # main の効果行がこれを超えたら E0620

[unsafe]
packages = ["daisy_hal"]         # unsafe / extern を書けるパッケージ

[interface]
frozen = ["voice"]               # 公開シグネチャの変更は E0630（ポリシーの更新が必要）
```

`kumi check` はポリシーへの違反をエラーにする。`kumi audit` はポリシーと unsafe・extern の差分を表示する。運用では、エージェントにこのファイルの書き込み権限を与えない。

### 13.5 数値プロファイル

| プロファイル | 内容 | 再現性 |
|---|---|---|
| `strict`（既定） | IEEE 754、最近接偶数丸め、FMA への縮約なし、再結合なし、非正規化数あり。`std.math` は Kumi 自身で実装され、libm を使わない。 | 同じ入力なら全ターゲットでビット一致 |
| `strict-ftz` | `strict` + 非正規化数をゼロに（FTZ / DAZ） | FTZ をサポートするターゲット間でビット一致 |
| `relaxed` | FMA と再結合を許可（ベクトル化のため） | 保証しない |

`relaxed` はターゲット全体には指定できない。proc や関数ごとに `@relaxed` で付け、`kumi audit` に列挙される。

---

## 14. 並行性

- **構造化並行性**: `task.scope(fn(s) { ... })` の中で `s.spawn(...)` したタスクは、スコープを抜ける前に必ず合流する。`Spawn` 効果を要求する。
- データ競合は型で排除する。スレッド間で共有できるのは Copy 値と Shared 値（不変）、および同期型だけ。Affine 値は `sink` で一つのタスクに移す。
- 同期型（`std.sync`）:

| 型 | 用途 | rt で使える操作 |
|---|---|---|
| `Chan[T]` | 一般のメッセージング | なし（`Block`） |
| `Spsc[T, const N: USize]` | 単一生産者・単一消費者の lock-free キュー（容量固定） | `push`, `pop` |
| `Atomic[T]` | `T: Copy`、8 バイト以下 | `load`, `store`, `swap` |
| `Swap[T]` | `T: Copy`。トリプルバッファで最新値を受け渡す | `latest` |

オーディオスレッドと制御スレッドの典型的な接続:

```kumi
// 制御スレッド側（非 rt）
params.publish(voice.Params { f0: 110.0, vowel_f1: 700.0, vowel_f2: 1220.0, gain: 0.5 })

// オーディオコールバック（rt）
pub rt fn on_audio(inout st: voice.State, params: Swap[voice.Params],
                   inout outs: voice.Outputs, frames: USize) {
  voice.process(inout st, params.latest(), voice.Inputs {}, inout outs, frames)
}
```

async / await は v0.1 には無い（§17）。

---

## 15. 例

この節の例は、§2〜§14 の規則に対して手で検査してある。

### 15.1 純粋な計算

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

### 15.2 効果・エラー・handler によるテスト

```kumi
use std.fs.{Fs, Path, IoError}
use std.text.{count_lines}

@derive(Eq, Show)
pub enum ConfigError {
  Io(IoError),
  Empty,
}

pub fn line_count(path: Path) -> Result[U64, ConfigError] uses {Fs} {
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

### 15.3 二極レゾネータ（Ori §10.3 に相当）

```kumi
use std.math.{exp, cos}
use std.dsp.test.{impulse, energy}

/// 二極レゾネータ。極は r·e^{±jw} にあり、bw > 0 なら |r| < 1 で安定。
/// 入力に (1 - r) を掛けて、ピークのゲインをおおよそ正規化する。
pub proc resonator(x: Sig[F32], fc: Ctl[F32], bw: Ctl[F32]) -> (y: Sig[F32]) {
  r  = exp(-(F32.PI * bw) / sample_rate())        // Ctl
  w  = (2.0 * F32.PI * fc) / sample_rate()        // Ctl
  b1 = 2.0 * r * cos(w)                           // Ctl
  b2 = r * r                                      // Ctl
  y1 = prev(y, 0.0)                               // Sig
  y2 = prev(y1, 0.0)                              // Sig
  y  = ((1.0 - r) * x) + (b1 * y1) - (b2 * y2)    // Sig: y[n] = g·x + b1·y[n-1] − r²·y[n-2]
}

test "resonator decays" {
  let out = resonator.render(resonator.Config {},
                             resonator.Params { fc: 500.0, bw: 100.0 },
                             resonator.Inputs { x: impulse(48000) }, 48000, 48000.0)
  assert energy(out.y, 47000, 48000) < 1.0e-12
}
```

- 因果性: `y → y1 → y` の閉路は `prev` を通るので合法。
- レート: `r w b1 b2` は Ctl なので、ブロックごとに 1 回だけ計算される。
- 演算子: どの式も、同じ群の連鎖か括弧付きの混在だけを使っている。`-(F32.PI * bw)` は前置の `-`。

### 15.4 声の proc と、ホスト側のコード

```kumi
// §15.3 と同じモジュール（resonator を参照する）
use std.math.{floor, exp}

/// 素朴なのこぎり波（エイリアシングあり。例示用）
pub proc saw(f0: Ctl[F32]) -> (y: Sig[F32]) {
  phase = wrap01(prev(phase, 0.0) + (f0 / sample_rate()))
  y = (2.0 * phase) - 1.0
}

pub rt fn wrap01(x: F32) -> F32 {
  x - floor(x)
}

/// Ctl 値を、時定数 time 秒の一次遅れで Sig に滑らかにする
pub proc smooth(x: Ctl[F32], time: Const[F32]) -> (y: Sig[F32]) {
  a = exp(-1.0 / (time * sample_rate()))           // Const: init で 1 回
  y = x + (a * (prev(y, 0.0) - x))
}

pub proc voice(f0: Ctl[F32], vowel_f1: Ctl[F32],
               vowel_f2: Ctl[F32], gain: Ctl[F32]) -> (out: Sig[F32]) {
  src = saw(f0)
  f1  = resonator(src, vowel_f1, 80.0)             // 80.0: Const から Ctl へ昇格
  f2  = resonator(src, vowel_f2, 120.0)
  out = (f1 + f2) * smooth(gain, 0.01)
}

export proc voice as "kumi_voice"
```

ホスト側（Kumi で WAV に書き出す）:

```kumi
use std.fs.{Fs, Path, IoError}
use std.audio.wav

pub fn render_vowel(path: Path) -> Result[(), IoError] uses {Fs} {
  let sr: F32 = 48000.0                            // 注釈が無いと F64 になる（§2.4）
  var st = voice.init(voice.Config {}, sr)
  var outs = voice.Outputs { out: Buf.zeroed(48000) }
  let params = voice.Params { f0: 110.0, vowel_f1: 700.0, vowel_f2: 1220.0, gain: 0.5 }
  voice.process(inout st, params, voice.Inputs {}, inout outs, 48000)
  wav.write(path, outs.out, sr)
}
```

---

## 16. 診断とツール

### 16.1 診断

```json
{
  "code": "E0010",
  "message": "operators from different groups need parentheses",
  "span": { "file": "dsp/res.kumi", "line": 9, "col": 10, "end_col": 24 },
  "found": "x + y * z",
  "fixes": [
    { "replace": "x + (y * z)" },
    { "replace": "(x + y) * z" }
  ]
}
```

| 範囲 | 分類 |
|---|---|
| E00xx | 字句・構文・演算子の群 |
| E03xx | モジュール・名前解決・循環 |
| E04xx | 型・アリティ・フィールド |
| E05xx | 網羅性 |
| E06xx | 効果・ターゲットの provides・ポリシー |
| E07xx | 引数モード・排他性・Affine |
| E08xx | proc（因果性・定義の重複・レート） |
| E09xx | rt |
| E10xx | FFI・unsafe |

- **型付きホール**: 式の位置に `_` を書くと、期待される型、使える効果、スコープ内の候補が報告され、ビルドは失敗する。
- エラーは **最初に検出された関数の中** で止まる。シグネチャが全て注釈されているので、ある関数の誤りが別の関数のエラーとして現れることはない（P1）。

### 16.2 コマンド

| コマンド | 内容 |
|---|---|
| `kumi check [--json]` | 型・効果・rt・因果性・ポリシーの検査 |
| `kumi fmt [--check]` | 唯一の表記への正規化 |
| `kumi test` | `test` と `prop`（シード固定のプロパティテスト）を実行 |
| `kumi interface <mod>` | 公開シグネチャ、種、効果、rt だけを出力 |
| `kumi audit` | extern、unsafe、`@relaxed`、ポリシーとの差分 |
| `kumi graph <proc>` | proc の方程式グラフを出力（SVG / DOT） |
| `kumi diff --ast` | 構造的な差分 |
| `kumi explain <code>` | 診断コードの説明と修正例 |
| `kumi primer [--std]` | この版の言語要約と標準ライブラリのインタフェースを、LLM のコンテキスト向けに出力 |

`kumi primer` は、コーパスの無い言語で LLM が API を捏造する問題への、言語としての対策である。出力は edition と std のバージョンに固定される。

---

## 17. 未決定事項

- マルチレート: オーバーサンプリング、FFT / STFT、リサンプリング（`block proc` と、明示的なクロックの導入を検討中）
- proc の配列ポート（`[Sig[F32]; N]`）と、N 個のインスタンスの生成
- proc の `Ctl` 出力（エンベロープの終了通知など）
- 分岐の中の proc インスタンスを停止させるか（クロック付きの `if`）
- 単位の型（`Hz`, `Sec`, `Samples` を newtype ではなく単位代数で扱う）
- async / await
- トレイトオブジェクト
- 実装しない機能の一覧を、拒否の理由とともに保守すること

---

## 18. 実装の順序

1. 構文解析器と Core の検査器（`kumi check --json`、型付きホール）。最初に、本仕様の例が全て通ることを回帰テストにする。
2. インタプリタ（`kumi test`）
3. proc の降下（方程式の整列、因果性、レートの巻き上げ）と `render`
4. C バックエンド（`-ffp-contract=off` で数値プロファイルを守る）。export、組込み、プラグインの入口が一度に得られる。
5. `interface` / `audit` / `primer` / LSP
6. LLVM と WASM のバックエンド
