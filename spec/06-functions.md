## 6. 関数と trait

### 6.1 関数

```onsa
use std.math.{sum}

pub fn mean[const N: U32](xs: [F64; N]) -> Option[F64] {
  if xs.len() == 0 {
    return None
  }
  Some(sum(xs) / (xs.len() as F64))
}
```

- 引数・返り値・効果は全て注釈する。返り値が `()` の場合だけ `->` を省略する（省略が唯一の書き方。`-> ()` と書いても受理し、`onsa fmt` が外す。関数の型 `fn(F32) -> ()` でも同じ）。
  無名関数の `-> ()` は返り値の型の注釈で、省くと期待型と本体から決まる形になり意味が違うので、外さない。
- ブロックの値は最後の式。`return` は途中脱出にだけ使う（末尾の位置の値のある `return e` は `onsa fmt` が除去する。末尾の位置は、関数と無名関数の本体の最後と、そこにある `if` / `match` の各分岐の最後で、再帰的にたどる。ループの中や末尾の位置でない `return` は早期の脱出なので残す）。
  値の無い末尾の `return` は書いても受理するが、書かない。取り除くと直前の文の値が本体の値になり検査の結果が変わる形があるので、`onsa fmt` は取り除かない（§18.2）。
- ブロックの途中の文に書いた式は、型が `()` でなければ E0418（発散する式は除く、§7）。値を捨てるときは `let _ = e` と書き、捨てていることを明示する（P10）。修正候補は `let _ = e` で、次の行が `-` か `^` で始まるときは前の行とつないだ形（`a - b`）も並べる（行頭の演算子は前の行に続かない、§2.5）。`for` / `while` の本体と、`()` を返す関数の最後の式は、`()` の位置なので型の不一致（E0401）になる。
- 多重定義、既定引数、可変長引数、名前付き引数は無い。
- 無名関数は `fn(x: F32) -> F32 { x * 2.0 }`。期待型が分かる位置では注釈を省略できる: `array.from_fn(fn(i) { i * 2 })`（`i` は `U32`、返り値の型は本体から決まる）。
  引数のモード（`inout`、`move`）も名前付き関数と同じ形で書く: `fn(inout x: F32) { x = x * 2.0 }`（型は `fn(inout F32)`）。
  `std` の最初の版で関数値（無名関数を含む）を受け取るのは `array.from_fn`、`std.test.check`、`Result` の `map_err`（§9.1）だけである（`Array` の `map` / `filter` は延期、§19.1）。どれも既定のモードの関数型の引数で受けるので、捕捉する無名関数も渡せる（§5.2）。
- 関数値（引数、ローカルの束縛、フィールド、要素、呼び出しの結果）は `.(` で呼ぶ: `f.(x)`、`s.f.(x)`、`ops[i].(acc)`、`pick(true).(5)`（例は節の末尾）。
  `fn` で宣言した関数（項目）、関連関数、名前空間の関数、効果の操作、列挙子の構築は `f(x)` と書く（`inc(1)`、`Point.new(1.0, 2.0)`、`voice.init(sr)`、`Fs.read(path)`、`Some(x)`）。形の誤りは E0020 で、修正候補は正しい形である。どの段で決まるかは呼び先で分かれる。
  呼び先が名前の経路でも、名前の経路に `[…]` を付けた形でもない呼び出し（`(s.f)(x)`、`pick(true)(5)`）は項目でありえないので構文の段で決まる（修正候補は `s.f.(x)` など）。
  タプルの添字で終わる呼び先（`t.0(x)`、`s.t.0(x)`、`mk2().0(x)`）も、添字は名前でない（§2.3）ので項目・メソッド・flow を指せず、前が何であっても値で、同じく構文の段で決まる（修正候補は `t.0.(x)`）。タプルの添字の後に `[…]` を付けた呼び先（`t.0[1](x)`）も同じで、`t.0` は項目を指せないので、修正候補は `t.0[1].(x)` の一つに決まる。
  それ以外の名前の経路の呼び出しは名前の解決で決まる（`f(x)` の `f` がローカルの束縛か引数なら修正候補は `f.(x)`、`inc.(1)` の `inc` が項目なら修正候補は `inc(1)`）。
  名前の経路に `[…]` を付けた呼び先（`ops[i](x)`）も、修正候補が `ops` の種類で分かれる（項目なら型引数の `ops::[…](x)`、§4.5。値なら `ops[i].(x)`）ので名前の解決で決まる。`s.f(x)` は型の段で決まる（§6.2）。`(s.f)(x)` は構文の段の誤りなので、`onsa fmt` はその括弧を外さない（§18.2）。
  呼び先が静的に決まる直接の呼び出しと、関数値を通した間接の呼び出し（捕捉した環境を伴いうる、§5.2）を見た目で分けるためである（P10）。間接の呼び出しは、呼び先を知るのに値の出どころを辿る必要があり、インライン展開などの最適化が止まる位置でもある。
- 関連関数と名前空間の関数は、項目の関数と同じく値として使える（`let mk = Point.new` の後に `mk.(1.0, 2.0)`）。総称の関数は、型引数を書いて取り出せる（`let g = id::[U8]` の後に `g.(250)`。§4.5）。メソッドと効果の操作は値にできない。
  `p.norm` は E0413（`norm` というフィールドが無い）、`Point.norm` と `Fs.read` を値の位置に書くと E0308 で、どちらも、メソッドと効果の操作は呼び出しだけで使うことを note で示す。メソッドを値にすると受け手を捕捉したクロージャになり、一つの関数の呼び方を一つに限る規則（§6.2）にも反する。
  効果の操作は、呼び出しの位置の handler で意味が決まる（§8.3）。
- `mean` は `xs` を借用して読むだけである。`xs` は値の配列なので、ヒープを使わず `Alloc` も要しない（§12.2）。

関数値の呼び出しの例:

```onsa
pub struct Shaper {
  gain: F32,
  curve: fn(F32) -> F32, // 関数型のフィールド
}

fn soft_clip(x: F32) -> F32 {
  x / (1.0 + x * x)
}

fn twice(f: fn(F32) -> F32, x: F32) -> F32 {
  f.(f.(x)) // 引数の関数値は `.(` で呼ぶ
}

fn shape(s: Shaper, x: F32) -> F32 {
  s.curve.(x) * s.gain // フィールドの関数値も `.(` で呼ぶ
}

fn demo(x: F32) -> F32 {
  let s = Shaper { gain: 0.5, curve: soft_clip } // 項目を値として置く
  shape(s, twice(soft_clip, soft_clip(x)))       // 項目そのものは `f(x)` で呼ぶ
}
```

### 6.2 メソッド

```onsa
use std.math.{sqrt}

impl Point {
  pub fn new(x: F32, y: F32) -> Point { Point { x: x, y: y } } // 関連関数: Point.new(...)
  pub rt fn norm(self) -> F32 { sqrt(self.x * self.x + self.y * self.y) }
  pub rt fn scale(inout self, k: F32) {
    self.x = self.x * k
    self.y = self.y * k
  }
}
```

`impl` 内の関数はドット記法でのみ呼ぶ（`p.norm()`, `Point.new(1.0, 2.0)`）。自由関数は前置でのみ呼ぶ。同じ関数に二つの呼び方は無い。関数型のフィールドの値は `s.f.(x)` で呼ぶ（§6.1）。`s.f(x)` は常にメソッドの呼び出しで、メソッドが無く関数型のフィールドがあれば E0020（修正候補は `s.f.(x)`）。
`s.f(x)` を、フィールドの関数の呼び出しと読む言語（Swift、JavaScript、Python）と、メソッドの呼び出しと読む言語（Rust、Ruby）があるからである。

総称の型の `impl` は、`impl` の直後の `[ ]` に型パラメータと境界を宣言し、対象にそのまま並べる（`impl[T, const N: U32] Ring[T, N] { … }`、`impl[T: Show] Show for Pair[T] { … }`）。宣言の形は関数の型パラメータ（§4.5）と同じである。
対象の型引数は、`impl` の型パラメータを一度ずつ並べたものに限る（具体的な型の `impl Ring[F32, 4]`、同じパラメータの重複 `impl[T] Pair2[T, T]`、対象に現れないパラメータは E0307）。
対象の型引数の数が宣言と合わなければ E0412（§4.5）で、並びの規則は判定しない（`impl P[I32]` の `P` が型引数を取らないとき、`impl W[I32, I32]`）。引数に書いた別名は、別名そのものが誤りの型でもパラメータでないので E0307 で（§18.1）、見つからない名前の引数は判定しない（失敗した名前、§18.1）。
対象の型引数は型の宣言の型パラメータの要求を満たさなければならず（E0416、§4.5）、`impl` の型パラメータが満たすかは `impl` の `[ ]` に書いた境界だけで決まる（`struct N[T: Num]` の後の `impl[T] N[T]` は E0416 で、`impl[T: Num] N[T]` と書く）。見出しの誤りである（§18.1）。
一つの `impl` は常にその型の全ての具体化を覆うので、実装は重ならない（特殊化は無い、§6.3）。
具体的な型だけのメソッドは、境界で書く（`impl[T: Float] Buf[T] { … }`）。境界の違う `impl` を同じ型に複数書いてよい。型の名前の後の `.` で引く名前（メソッド、関連定数、enum の列挙子）は一つの空間で、重なると E0304。
列挙子との重なりは書いた順によらず `impl` のメンバに付けて列挙子を note で示し、メンバどうしはソースの順で後の宣言に付けて前を note で示す。見出しが誤り（E0307、E0412、E0416）の `impl` のメンバもこの空間に入る（§18.1）。

### 6.3 trait

```onsa
pub trait Describe {
  fn describe(self) -> Str uses {Alloc}
}

impl Describe for Point {
  fn describe(self) -> Str uses {Alloc} { "({self.x}, {self.y})" }
}
```

- **一貫性**: `impl Tr for Ty` は `Tr` か `Ty` を定義したモジュールにしか書けず、固有の `impl Ty` は `Ty` を定義したモジュールにしか書けない（孤児規則、E0307）。`Tr` と `Ty` は宣言の名前で書き、型別名は書けない（§4.4）。組込み型（§4.1）は std で定義されたものとして扱う（§11.6 の生成された型と同じ扱い）。
  したがって、組込み型のメソッド・関連関数・関連定数と標準 trait の実装を書けるのは std だけで、利用者が組込み型に足せるのは、自分で定義した trait の実装だけである。型のメソッドは型の定義と同じ所で見つかり、全てのパッケージに効く追加は生まれない。重複実装、特殊化は無い（同じ型への同じ trait の `impl` が二つあると E0304）。
  `impl` を書ける場所と対象の書き方の規則は、全て E0307 である: この孤児規則、宣言の名前で書くこと（§4.4）、対象の型引数（§6.2）、組込み型だけが実装する trait（`Float`、下記）と derive でだけ実装する trait（`Ordinal`、§6.4）。
- ジェネリック trait（`Iter[T]` など）は、一つの型について高々一つしか実装できない（二つ目は E0304）。
- 既定メソッドは可。トレイトオブジェクト（動的ディスパッチ）は無い（§19）。
- 演算子 trait: `Add Sub Mul Div Rem Neg PartialEq PartialOrd BitAnd BitOr BitXor Shl Shr Not WrappingAdd WrappingSub WrappingMul SaturatingAdd SaturatingSub SaturatingMul`。演算子との対応は §3.2、意味は §3.4。
  各演算子は、被演算子の型がその演算子の trait を満たすことを要する。ラップと飽和の trait は Rust の標準ライブラリに無い。
- 標準 trait: `PartialEq`, `PartialOrd`（演算子用。浮動小数は IEEE 比較で、NaN は何とも等しくなく大小も無い）、`Eq`, `Ord`（全順序。ソートと `Map` / `Set` の鍵に使う。浮動小数は実装しない）、`Hash`, `Show`, `Default`, `Iter[T]`, `IntoIter[T]`（ユーザ定義型の反復は必要になるまで延期、§19.1）, `Drop`, `AnyNum`, `Num`, `Float`, `Int`, `Unsigned`, `Ordinal`（§6.4）。
  `Copy` と `Dup` は trait ではなく種の制約である（§4.6）。名前は Rust と同じで、意味は次の項と下の約束で定める（§0.3 の規則 3）。数の trait（`AnyNum` `Num` `Float` `Int` `Unsigned`）は Rust の標準ライブラリに無いので、次の項で定める。
  標準 trait は std で `trait` として宣言され、組込み型の実装（下の表）も std の `impl` である（孤児規則、上記）。演算子 trait と標準 trait は全て prelude にあり、`use` 無しで境界と derive に書ける（§15.1）。
- 等値・順序・ハッシュの約束: `PartialEq` の `==` は対称で推移的（浮動小数の NaN は自分とも等しくない）。`Eq` は加えて反射的（`a == a`）。`PartialOrd` の大小は `==` と矛盾しない。`Ord` は `Eq` と矛盾しない全順序である。`Hash` は、`==` で等しい値に等しいハッシュを与える。
  derive した実装と組込み型の実装はこれを満たす。利用者の `impl` もこれを守る（コンパイラは検査しない。破ると、ソートや `Map` / `Set` の結果が未規定になるが、メモリの安全は損なわない）。
- trait の宣言の頭に `: trait + trait` と書くと、その trait を実装する型が先に満たすべき trait（上位の trait）になる（`pub trait Ord: PartialOrd + Eq`）。境界（§4.5）と derive（§6.4）と同じく「左の型が右の trait を満たす」と読む。上位の trait を満たさない型への `impl` は E0416。
  `T: Ord` の境界からは、上位の trait（`PartialOrd`、`Eq`、`PartialEq`）も使える。
- 数の trait は次の 5 つで、上位の trait の関係は `Num: AnyNum`、`Float: Num`、`Int: AnyNum`、`Unsigned: Int` である。
  - `AnyNum` は、符号なしを含む全ての数を表す。`Copy` `Add` `Sub` `Mul` `Div` `Rem` `PartialEq` `PartialOrd` を満たし、関連定数 `ZERO: Self`（加法の単位元。浮動小数では `+0.0` で、`-0.0 + ZERO` は `+0.0` になる、§3.4）を持つ。
    符号なし整数の引き算が 0 を下回ると、具体的な型と同じく実行時に panic する（§3.4）。`Copy` を含めるのは、数を値として扱い、総称の数値のコードで `Copy` を重ねて書かずに済むようにするためである（`Copy` の無い `T` の破棄は `Alloc` を要する、下記）。
  - `Num` は、負の数を持つ数（符号付き整数、浮動小数、固定小数点）を表す。`AnyNum` と `Neg` を満たす。符号なし整数は `Num` を満たさない。総称の数値のコードは負の値を前提にすることが多く（`a + (b - a) * t` は `b < a` でも成り立つと考えて書く）、符号なしを受け付けると、普通の入力で実行時に panic するからである。数の境界は `Num` を既定とし、符号なしも受けるときだけ `AnyNum` と書く（P10）。
  - `Float` は、浮動小数を表す。`Num` を満たし、関連定数 `ONE`（乗法の単位元）、`PI`、`MAX`、`EPSILON`、`INFINITY`、`NAN`（全て `Self`）を持つ。`Float` を実装するのは組込みの浮動小数（`F32`、`F64`）だけで、利用者の型への `impl Float` は E0307（標準 trait の実装を書ける場所の規則、上記）。
    超越関数（§13.4）と `vdelay`（§11.4）は、組込みの浮動小数のプリミティブで計算するからである。利用者の型に開くかは §19.1。
  - `Int` は、全ての整数を表す。`AnyNum` `Eq` `Ord` `Hash` `BitAnd` `BitOr` `BitXor` `Shl` `Shr` `Not` と、ラップ・飽和の 6 つの演算子 trait を満たし、関連定数 `ONE` `MIN` `MAX`（`Self`）と `BITS`（`U32`）を持つ。符号付き整数は `Num` と `Int` を満たす。符号付き整数だけを受けるときは `T: Num + Int` と書く。
  - `Unsigned` は、符号なし整数を表す印で、`Int` を満たす。負の数を持たず、`>>` は論理シフトである（§3.4）。
  - `ONE` を `AnyNum` と `Num` に置かないのは、固定小数点（Q15 / Q31、範囲は `[-1, 1)`）が 1 を表せず、`Num` を実装できなくなるからである。利用者の型も `impl AnyNum for Q15 { const ZERO: Q15 = ... }` と `impl Num for Q15 {}` のように実装できる（演算子 trait も実装する）。
    `std.math` の `abs`（`Num`）と `min` / `max`（`AnyNum`）は、利用者の数の型では std の本体で計算される（§13.4）。
- 演算子の被演算子の型がその演算子の trait を満たさないと E0401。総称の関数での修正候補は、演算子 trait ではなく、その演算子を含む数の trait に境界を絞る形で出す。
  否定は `Num`（`T: AnyNum` は `T: Num` に、`T: Int` は `T: Int + Num` に）、ビット演算・`!`・ラップ・飽和は `Int`（`T: AnyNum` は `T: Int` に、`T: Num` は `T: Num + Int` に）。
  比較と算術の演算子では、`==` `!=` は `PartialEq`、`<` `<=` `>` `>=` は `PartialOrd`、`+ - * / %` は `Num`（数の境界の既定）に絞る。既にある境界が候補の trait に含まれるときは置き換える（`T: PartialOrd` に `+` を使えば `T: Num`）。
  比較を数の trait に絞らないのは、数でない型も比較を持ち、`clamp` のような関数を誤った境界に導くからである。絞れないとき（`T: Unsigned` の否定、`T: Float` のビット演算）は候補を出さない。符号なし整数の否定の E0401 には、2 の補数の否定の書き方（`0 -% u`、`T.ZERO -% x`）を note で示す。
  数の trait の境界を満たさない型を渡した E0416 は、その型が満たす数の trait を note で示す（`U32` なら `AnyNum`、`Int`、`Unsigned`）。
- `Default` は関連関数 `default() -> Self` を持つ。具体的な型では `P.default()`、総称の関数では `T.default()`（`T: Default`）と呼ぶ（§6.6 の `T.ZERO` と同じ形）。
- 組込み型が実装する標準 trait と演算子 trait は、次の表で全てである（閉じた一覧）。`PartialEq` と `PartialOrd` は演算子 trait でもあり、左の欄に書いた。足すときは、必要な実例を添えて議論する（[`decisions/A/`](../decisions/A/README.md)）。`Copy` / `Dup` は種で決まる（§4.6）。

| 型 | 実装する trait | 演算子 trait（`PartialEq` `PartialOrd` を除く） |
|---|---|---|
| 符号付き整数（`I8`〜`I64`） | `PartialEq` `Eq` `PartialOrd` `Ord` `Hash` `Show` `Default`（0） `AnyNum` `Num` `Int` | `Add` `Sub` `Mul` `Div` `Rem` `Neg` `BitAnd` `BitOr` `BitXor` `Shl` `Shr` `Not` `WrappingAdd` `WrappingSub` `WrappingMul` `SaturatingAdd` `SaturatingSub` `SaturatingMul` |
| 符号なし整数（`U8`〜`U64`） | `PartialEq` `Eq` `PartialOrd` `Ord` `Hash` `Show` `Default`（0） `AnyNum` `Int` `Unsigned` | `Add` `Sub` `Mul` `Div` `Rem` `BitAnd` `BitOr` `BitXor` `Shl` `Shr` `Not` `WrappingAdd` `WrappingSub` `WrappingMul` `SaturatingAdd` `SaturatingSub` `SaturatingMul` |
| 浮動小数 | `PartialEq` `PartialOrd`（IEEE 比較） `Show` `Default`（`+0.0`） `AnyNum` `Num` `Float` | `Add` `Sub` `Mul` `Div` `Rem` `Neg` |
| `Bool` | `PartialEq` `Eq` `Hash` `Show` `Default`（`false`） | `Not` |
| `Char` | `PartialEq` `Eq` `PartialOrd` `Ord`（コードポイントの順） `Hash` `Show` | なし |
| `Str` | `PartialEq` `Eq` `PartialOrd` `Ord`（バイト列の辞書順、§4.2） `Hash` `Show` `Default`（空） | なし |
| `Bytes` | `PartialEq` `Eq` `PartialOrd` `Ord`（辞書順） `Hash` `Default`（空） | なし |
| `()` | `PartialEq` `Eq` `Default` | なし |
| タプル、`[T; N]` | 要素が全て実装するとき `PartialEq` `Eq` `PartialOrd` `Ord`（先頭から辞書式） `Hash` `Show` `Default` | なし |
| `Option[T]`、`Result[T, E]` | 中身が全て実装するとき `PartialEq` `Eq` `Hash` `Show`（§4.1 の宣言の derive による） | なし |
| `Array[T]` | 要素が実装するとき `PartialEq` `Eq` | なし |
| `Map`、`Set`、`Buf`、`Span`、関数値 | なし | なし |

- タプルと `[T; N]` の実装は、処理系が構造から与える（derive と同じ扱いで、std に要素の数ごとの `impl` は書かない）。
- タプルと `[T; N]` の比較: `==` は全ての要素が等しいとき真。大小は、先頭から見て最初の等しくない要素の組で決める（辞書式）。その組が比べられない（浮動小数の NaN）なら、`<` `<=` `>` `>=` は全て偽で、スカラの IEEE の比較と同じである（`[1.0, NaN] < [2.0, 0.0]` は先頭で決まるので真、`[NaN, 0.0] < [1.0, 0.0]` は偽）。
- `Show` の文字列: 整数は 10 進、`Bool` は `true` / `false`、`Char` はその文字、`Str` はそのまま。浮動小数は、その型（`F32` / `F64`）の値に読み戻せる最短の 10 進表記で、Onsa の浮動小数のリテラルとして読める形にする（小数点を必ず含む: `1.0`、`0.1`、`-0.0`）。
  絶対値が `1.0e21` 以上か `1.0e-7` 未満なら指数で書く（`1.0e21`、`1.5e-8`）。`NaN` は `NaN`、無限大は `inf` / `-inf`。全ての変換先で同じ文字列になる（§13.4）。
- 複合の値の `Show` は、Onsa の式の形で書く: struct は `Point { x: 1.0, y: 2.0 }`（宣言順で、`priv` を含む全てのフィールド）、enum は `Shape.Circle(1.0)` と `Mode.Off`、`Option` / `Result` は `Some(1)`、`None`、`Ok(1)`、`Err(e)`、タプルは `(1, 2.0)`、`[T; N]` は `[1, 2]`。
  型名にモジュールのパスと型引数は付けない。中に入る `Str` と `Char` は Onsa のリテラルとして書く（引用符とエスケープを付け、`{` と `}` は `{{` と `}}`）。最上位の `Str` をそのまま書くのは、補間で地の文に入れるためで、中に入れたときは値の区切りを読めるようにする。
- `Drop` の `drop(move self)` は、`rt` を付けること、`uses {Alloc}` を持つことだけが許される。値が破棄される位置は、その型の破棄が必要とするもの（`Alloc`、非 rt）を要求する（E0601 / E0901）。
- `Drop` を実装する型の所有する値は、分解するパターン（`let`、`match move`）にも、フィールドの取り出し（§5.2）にも使えない（E0711）。全体の移動と破棄だけなので、`drop` を飛ばして資源を漏らすことが無い（§14.1 の `Conv` の `h`）。`drop(move self)` の本体の終わりでは、`self` は `drop` を呼び直さずにフィールドごとに破棄される。本体の中では `self` を分解でき、フィールドを取り出せる。
- ジェネリックな型パラメータ `T` の値の破棄は、`T: Copy` の制約が無い限り `Alloc` を要する（`?Dup` の `T` も同じ）。したがって `rt fn` の中で `T` の値を破棄できるのは `T: Copy` のときだけである。捨てる操作を持たない関数（借用で受け取り、複製して返す、または移動する）はこの規則に触れない。標準ライブラリはこの様式で書き、捨てる操作（`clear` など）だけが `uses {Alloc}` を持つ。

### 6.4 derive

```onsa
pub struct Key: PartialEq + Eq + Hash + Show {
  id: U32,
}
```

型の宣言の頭に `: trait + trait` と書くと、その trait の実装を構造から自動で生成する（derive）。境界の `[T: Eq]`（§4.5）と同じく、「左の型が右の trait を満たす」と読む。

- 書く位置は、名前（と型パラメータ）の後で本体の `{` の前（`pub enum Shape: PartialEq {`、`pub struct Ring[T, const N: U32]: PartialEq {`）。
- 書けるのは `PartialEq Eq PartialOrd Ord Hash Show Default Ordinal` の閉じた一覧だけ（一覧に無い trait は E0416 で、手で `impl` を書くことを note で示す。種の制約の `Copy` と `Dup` は E0020、§4.6）。
  `Eq` は `PartialEq` を、`Ord` は `PartialOrd` と `Eq` を要求する。各フィールド（列挙子の中身）の型がその trait を満たさなければ E0416。struct の `Default` は、各フィールドの既定値を並べたものである。enum には `Default` を並べられない（E0416）。
  どの列挙子を既定にするかを宣言の順に頼らず、`impl Default for Mode { fn default() -> Mode { Mode.Off } }` と手で書く。総称の型（`struct Pair[T]: PartialEq`）は、型引数が満たすときだけ満たす。
- 並べた trait は全て自動で生成する。手で実装するときは `impl Tr for Ty` と書き、宣言には並べない（両方に書くと E0304）。
- 生成する実装の意味: `PartialEq` / `Eq` は、全てのフィールド（enum は列挙子と中身）が等しいとき等しい。`PartialOrd` / `Ord` は、struct ではフィールドの宣言順の辞書式（タプルと同じ規則で、NaN の扱いも同じ、§6.3）、enum では列挙子の宣言順（先に書いたものが小さい）で、同じ列挙子なら中身の辞書式である。
  struct のフィールドの順は配置（§12.4）と C の構造体でも、enum の列挙子の順は `Ordinal` の番号（下記）でも意味を持つ。`Hash` は §6.3 の約束を満たす。`Show` の書式は §6.3。
- `Ordinal` は、列挙子に中身の無い enum にだけ並べられる（それ以外は E0416）。列挙子と、宣言順の 0 始まりの番号を変換する: `m.ordinal() -> U32` と `Mode.from_ordinal(n: U32) -> Option[Mode]`（範囲外は `None`）。
  保存したデータ、C の API、`@param` の値（§19.1）など、列挙子を整数で表すときに使う。宣言の印は、列挙子の順が外に出る（並べ替えると保存したデータの意味が変わる）ことを示す（P10）。番号の値を指定する書き方は無く、手書きの `impl Ordinal` は書けない（E0307）。
- 属性（§6.5）にしないのは、trait の実装が受理されるプログラムと型を変える、型の定義の一部だからである。旧形の `@derive(...)` は E0020（修正候補は宣言に書く形）。

### 6.5 属性（全て）

`@repr(c)`, `@fp(...)`（§15.5）、`@param(...)`（§11.7）、`@host(...)`（§11.7）、`@latency(...)`（§11.6）、`@mem(...)`（§12.4）、`@export`（§14.2）。これ以外の属性は無い（`@deprecated` は必要になったら定義する、§19.1）。
属性を付けられる構文の場所は決まっている: `@repr` は struct、`@fp` は fn と flow、`@param` と `@host` は flow の入力、`@latency` は flow、`@mem` は `let`、`@export` はトップレベルの fn と flow。一覧に無い属性と、その場所に付けられない属性は E0005。
付けられる場所の中での意味の条件と値の誤りは、各属性のコードで報告する（`@param`・`@host`・`@latency` は E0809。`sample` の入力の `@param` など。`@mem` は E0818。遅延でない `let` の `@mem` など）。`@repr` と `@fp` の値の誤り（`@repr(rust)`、`@fp(fast)`）と `@host` の種類の誤りは E0005 で、修正候補は一覧の値である。
`@export` は引数を取らず、`@export(…)` は E0005 で、修正候補は `@export` である。
これらの検査（場所、意味の条件、値）はターゲットに依らないので、export するかによらず `onsa check` が出す（ターゲットで決まる条件は、§11.7 のプラグインの条件や §12.4 の E0819 のように、各節のとおりそのビルド）。
置き換え先の決まった旧形（`@derive(...)`、`@relaxed`、`@bulk`）は E0020（修正候補は今の形）。

属性は、ターゲットに固有の事情が関わらない段までのプログラムの解釈（型と計算の結果）を変えない付与情報である: C との間の配置（`@repr`）、浮動小数の演算の緩和（`@fp`）、UI とホストのための情報（`@param`、`@host`、`@latency`）、記憶域の配置（`@mem`）、C の ABI に出す項目の印（`@export`）。
属性の値を読むのは、ターゲットの段（C の API、ラッパー、WASM）と道具（`onsa interface`、`onsa test --flows`、IDE）である。この版の Onsa のコードには、属性の値を読む手段が無い。
どのプログラムを受理するかには関わりうる（位置と値の検査、export する項目の `pub`（E0303）・名前の末尾の `_`（E0320）・境界の型（E0810）・関数のシグネチャと、export する flow の `block` の入力の `@param` か `@host`、bulk を持つ状態の置き場所の E0819、`@repr(c)` の FFI）ので、その検査は各節に書く。型の定義に関わる trait の自動生成は、属性ではなく型の宣言に書く（§6.4）。

### 6.6 コンパイル時定数

```onsa
const TABLE_SIZE: U32 = 1024
const SINE: [F32; 1024] = make_sine_table()
```

- 初期化式から呼べるのは、効果行が空か `{Alloc}` だけの関数。`Alloc` はコンパイラが提供する。
- コンパイル時の評価（定数式、`const` の初期化式、`@param` の値）が panic すると（溢れ、ゼロ除算、添字の範囲外、`unwrap` の失敗、`panic(...)` など）、その式の位置で E0419。呼び出しの深さの上限（§12.5）を超えた場合も同じである。直し方は、どの評価でも式か値を直すことである。
- 初期化式の超越関数（`std.math` の `exp`、`sin` など）は、`std.math` の Onsa で書いた実装（musl の移植）で評価する。結果はビルドする機械の libm に依らず、§15.3 の「`onsa.lock` が同じなら成果物は同一」を保つ。焼き込んだ値と、実行時に同じ式を変換先で計算した値は、最後の桁が違いうる（§13.4 の許容誤差の範囲）。
- 結果の型は、**静的に配置できる型** でなければならない（E0407）。静的に配置できる型は、Copy の型、`Str`・`Bytes`、要素・フィールド・ペイロードが全て静的に配置できる `Array[T]`・`[T; N]`・タプル・struct・enum（`[Str; 2]`、`(Str, U32)`、`Option[Str]`）である。
  `Map` / `Set` は表の配置が実装に依存するので対象外で、Affine の型を含む型も置けない。結果は読み取り専用の静的領域（組込みではフラッシュ）に置かれる。
  中のヒープのオブジェクト（`Str`・`Bytes`・`Array`）はヘッダ付きの静的オブジェクト（§12.8）として、値の型の部分は静的領域の値として書き出され、`Alloc` 無しで使える。この版では、Shared を含む型の `const` は E0200 である（第 2 期）。
  宣言の型が型パラメータを含み、その型パラメータが `Copy` の境界（数の trait を含む）を持たなければ、Shared でありうるので同じく E0200 である（`impl[T] W[T] { const Z: Option[T] = None }`。`T: ?Dup` も同じ）。Shared を含み、置けない部分（`Map`・`Set`・Affine）も含む型（`(Str, Buf[F32])`）は、版によらない E0407 である（§18.1 の E0200 と同じ見方）。
  この判定（E0407 と、Shared を含む型の E0200）は宣言の型だけで決まり、値の検査より先に行う。位置は宣言の型で、値に失敗した名前があっても報告する（値の位置で単位の以後を止める §18.1 は、値に頼らないこの判定に当たらない）。
- 初期化式が、直接または他の定数を経由して自分自身を参照すると E0312（`const A: U32 = B` と `const B: U32 = A`）。定数の宣言の型が長さで自分に戻る循環は E0311（§4.4）。数と位置と note は宣言をまたぐ循環の規則（§18.1）による。循環の定数は評価せず、誤りの値として扱う（それを読む定数や型の中の長さには診断を出さない）。
  E0312 を付けた定数の単位は名前の段で止まり（§18.1）、集まりの他の定数の単位はそれぞれ検査する（型は宣言に書くので、値に頼らない）。
- `impl` と `trait` の中にも同じ形で書ける（関連定数）: `impl Point { const ORIGIN: Point = Point { x: 0.0, y: 0.0 } }`、`trait AnyNum { const ZERO: Self }`。参照は `Point.ORIGIN`、`F32.PI`、型パラメータでは `T.ZERO`。
  組込み型の関連定数は std が宣言する（§6.3 の孤児規則）。字面は `UpperCamel.UPPER_SNAKE` で、関連関数や効果の操作（`Fs.read`）と区別できる。
- 組込み型の関連定数は、次の表で全てである（閉じた一覧。足すときは、必要な実例を添えて議論する、[`decisions/A/`](../decisions/A/README.md)）。

| 型 | 関連定数 |
|---|---|
| 整数 | `ZERO`（`AnyNum`）、`ONE` `MIN` `MAX` `BITS`（`Int`。`BITS` は `U32`、他は `Self`） |
| 浮動小数 | `ZERO`（`AnyNum`）、`ONE` `PI` `MAX` `EPSILON` `INFINITY` `NAN`（`Float`） |

- 浮動小数の関連定数の値は、数学的な値を最近接偶数で型に丸めた値である（リテラルと同じ規則、§2.4）。`ZERO` は `+0.0`、`ONE`、`MAX`（最大の有限値）、`EPSILON`（`F32` は `2^-23`、`F64` は `2^-52`）、`INFINITY` は正確に表せる。
  `PI` は π を丸めた値で、`to_bits()` は `F32` が `0x40490FDB`、`F64` が `0x400921FB54442D18` である。`NAN` は NaN で、ビットは §3.4 のとおり未規定である。
- 浮動小数に `MIN` は無い（E0302。修正候補は `-F32.MAX`）。Rust の `f32::MIN` は最も負の有限値、C の `FLT_MIN` は最小の正の正規化数で、どちらの読み方でも検査を通るのに意味が違う（§0.3 の規則 4）。最も負の有限値は `-F32.MAX` と書く。`MAX` と `EPSILON`（1 と、1 の次に大きい表現可能な数の差）は C と Rust で同じ意味である。
- リテラルは型パラメータ `T` の値にならない（`[T: Float]` の関数の中で `x + 0.0` とは書けない）。総称の関数では、0 と 1 を `T.ZERO`、`T.ONE`（`T: Float` か `T: Int`）で書く。具体的な型ではリテラルで足りる。

---

