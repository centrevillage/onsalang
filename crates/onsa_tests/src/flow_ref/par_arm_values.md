# W7-17 の par~・par・if~・match~ の中のイベントの値の表（P1・P2・A1 の抜き出し）

別の助言が実装を読まずに仕様の字と決定だけから書いた表の P1・P2・A1 の節を、そのまま写した。
各事例は共通の部品の次に `flow top(x: U32 at sample, y: U32 at sample, c: U32 at sample) -> U32 at sample { … }` の中身として置かれ、入力の列は位置 0 からの値で、書いていない入力は全て 0。
評価器の表の試験（`par_arm_tests.rs`）が、評価器の出力を「手で出した期待」と比べる。表を正とせず、食い違えば字を手で追う。

## 共通の部品

```onsa
rt fn some_if(c: Bool, v: U32) -> Option[U32] { if c { Some(v) } else { None } }
enum V { A(U32), B }
impl Default for V { rt fn default() -> V { V.B } }

flow gen(x: U32 at sample) -> U32 at event { some_if(x != 0, x) }       // sample の段で、0 でない x を出す
flow genz(x: U32 at sample) -> U32 at event { if x != 0 { Some(x - 1) } else { None } }  // x - 1 を出す（値 0 のイベントを作れる）。`some_if(x != 0, x - 1)` は引数を先に評価するので、x が 0 の位置で U32 の引き算が溢れて panic する（元の表の誤り）
flow genv(x: U32 at sample) -> V at event {                             // 1〜5 は V.A(x)、6 以上は V.B を出す
  if x == 0 { None } else if x > 5 { Some(V.B) } else { Some(V.A(x)) } }
flow fwd(e: U32 at event) -> U32 at event { Some(e * 10) }              // 入力のイベントごとに出す
flow tk() -> U32 at event { Some(sample_tick()) }                       // 本体の sample の刻みごとに、その時間を出す
flow kk() -> U32 at event { let k: U32 = prev~(^k) + 1                  // 刻みごとに、動いた刻みの数を出す
  Some(k) }
flow tick4() -> U32 at event { Some(sample_tick()) at (sample / 4) }    // 本体の sample / 4 の刻みごとに時間を出す
flow beat(e: U32 at event) -> U32 at event { let n: U32 = prev~(^n) + e // sample の刻みごとに、イベントの和を出す
  Some(n at sample) }
flow cnt(e: U32 at event) -> U32 at sample { let n: U32 = prev~(^n) + e // イベントの値の和
  n }
flow seq(e: U32 at event) -> U32 at sample { let n: U32 = prev~(^n) * 10 + e   // 来た順に 10 進の桁に並べる
  n }
flow ek(e: U32 at event) -> U32 at sample { let n: U32 = prev~(^n) * 10 + e + 1  // 値 + 1 を桁に並べる（値 0 の刻みも見える）
  n }
flow acc(e: U32 at event) -> U32 at sample {                            // 動いた sample の刻みの数 * 100 + イベントの和
  let n: U32 = prev~(^n) + e
  let k: U32 = prev~(^k) + 1
  k * 100 + n }
flow last(e: U32 at event) -> U32 at sample { e }                       // イベントの値の欄
flow inc(e: U32 at event) -> U32 at sample { e + 1 }                    // イベントの段の計算した式
flow inc2(e: U32 at event) -> U32 at sample { (e at sample) + 1 }       // sample で計算する式
flow stamp(e: U32 at event) -> U32 at sample { let t: U32 = e * 1000 + sample_tick()   // イベントの段の時間
  t }
flow pe(e: U32 at event) -> U32 at sample { let p = prev~(e)            // 一つ前のイベントの値
  p }
flow runs() -> U32 at sample { let k: U32 = prev~(^k) + 1               // 動いた刻みの数
  k }
flow pv(x: U32 at sample) -> U32 at sample { prev~(x, 9) }
flow idf(x: U32 at sample) -> U32 at sample { x }
flow mix(e: U32 at event, s: U32 at sample) -> U32 at sample { s * 100 + e }
flow hit(a: U32 at event, b: U32 at event) -> U32 at sample { cnt~(a).reset_if~(b != 0) }
flow wa(e: U32 at event, c: U32 at sample) -> U32 at sample { acc~(e).when~(c != 0) }
flow inner(x: U32 at sample) -> U32 at sample { let d = gen~(x)
  d at sample }
flow in2() -> U32 at sample { let d = tk~()
  stamp~(d) }
flow w2() -> U32 at event { let d = tk~().up~(2)                        // 一回の sample の段で二つ出す
  Some(d) }
flow w3() -> U32 at event { let d = w2~()
  Some(d) }
flow w4() -> U32 at event { let d = w2~().up~(2)                        // 一回の段で四つ
  Some(d) }
flow wb() -> U32 at event { let d = tk~().up~(2).down~(2)               // 塊の境界の位置で二つ
  Some(d) }
flow pp(e: U32 at event, x: U32 at sample) -> U32 at sample {
  let s = par i in 0 ..< 2 { x + (e + i + 1) }
  s[0] * 100 + s[1] }
flow lastof(x: U32 at (sample * 2)) -> U32 at sample { x[1] }           // 変換の flow: 二つの走りの後の方
flow both2(x: U32 at (sample * 2)) -> U32 at sample { x[0] * 1000 + x[1] }
// 事例の本体は flow top(x: U32 at sample, y: U32 at sample, c: U32 at sample) -> U32 at sample { … } の中身
```

### P1-1（P1）

```onsa
let s = par~ i in 0 ..< 2 { cnt~(gen~(x * (i + 1))) }
s[0] * 100 + s[1]
```

- 入力: x = 0 3 0 1
- 手で出した期待: `0 306 306 408`
- 根拠: §11.5「複製ごとに別のインスタンス」、§11.11「par~ の中では、その複製の本体」。

### P1-2（P1）

```onsa
let d = gen~(x)
let s = par~ i in 0 ..< 2 { prev~(d) + i + 1 }
let t = s at sample
t[0] * 100 + t[1]
```

- 入力: x = 0 3 0 5
- 手で出した期待: `0 102 102 405`
- 根拠: §11.4（イベントのクロックの遅延）、§11.11（イベントの段の式）。複製の値は d の刻みで評価するので、最初のイベントの前は 0（i + 1 ではない）。

### P1-7（P1）

```onsa
let d = gen~(x)
let s = par~ i in 0 ..< 2 { (prev~(d) at sample) + i + 1 }
s[0] * 100 + s[1]
```

- 入力: x = 0 3 0 5
- 手で出した期待: `102 102 102 405`
- 根拠: §11.3（sample で計算する）。P1-2 と値が違うのが正しい。

### P1-3（P1）

```onsa
let d = gen~(x)
let s = par~ i in 0 ..< 2 { acc~(d).when~(c != i) }
s[0] * 1000 + s[1]
```

- 入力: x = 0 3 0 5、c = 0 1 1 0
- 手で出した期待: `100 103100 203100 203208`
- 根拠: §11.10（複製ごとに別の条件で止まり、どちらもイベントは処理する）。

### P1-4（P1）

```onsa
let d = gen~(x)
let r = gen~(y)
let s = par~ i in 0 ..< 2 { acc~(d).reset_if~(r > i) }
s[0] * 1000 + s[1]
```

- 入力: x = 0 3 0 5 0 0、y = 0 0 1 0 2 0
- 手で出した期待: `100100 203203 100303 205408 100100 200200`
- 根拠: §11.10（イベントの条件、複製ごと）。戻した位置の sample の刻みで一歩動く。

### P1-5（P1）

```onsa
let s = par~ i in 0 ..< 2 { gen~(x * (i + 1)) at sample }
s[0] * 100 + s[1]
```

- 入力: x = 0 3 0 1
- 手で出した期待: `0 306 306 102`
- 根拠: §11.5「複製の中で at sample を付ける」（S-1096）。

### P1-6（P1）

```onsa
let s = par~ i in 0 ..< 2 { runs~().reset_if~(gen~(x) > i) }
s[0] * 100 + s[1]
```

- 入力: x = 0 1 0 2 0
- 手で出した期待: `101 102 203 101 202`
- 根拠: §11.3「引数と修飾子の条件を字面の順に評価してから、初期化と部品の段」。条件の中の作り手が出し、そのイベントの刻みで戻し、同じ位置の sample で一歩。

### P2-1（P2）

```onsa
let d = gen~(x)
let s = par i in 0 ..< 2 { x + (d + i + 1) }
s[0] * 100 + s[1]
```

- 入力: x = 0 3 0 2
- 手で出した期待: `0 708 405 506`
- 根拠: §11.3「段が刻みの計算した部分式は、より速い式の中でもその刻みで評価し、値を隠れたフィールドに置く」、§11.5「`par` は状態のフィールドを作らない（本体の巻き上げの欄（§11.3）は持ちうる。…）」。`d + i + 1` の欄は複製ごとで、最初のイベントの前は 0。

### P2-1b（P2）

```onsa
let d = gen~(x)
let s = par i in 0 ..< 2 { x + ((d at sample) + i + 1) }
s[0] * 100 + s[1]
```

- 入力: x = 0 3 0 2
- 手で出した期待: `102 708 405 506`
- 根拠: §11.3（sample で計算する）。P2-1 と位置 0 が違うのが正しい。

### P2-2（P2）

```onsa
let d = gen~(x)
let s = par i in 0 ..< 2 { d * (i + 2) }
let t = s at sample
t[0] * 100 + t[1]
```

- 入力: x = 0 3 0 2
- 手で出した期待: `0 609 609 406`
- 根拠: §11.11（par の全体が d のクロックの式）。

### P2-3（P2）

```onsa
let d = gen~(x)
pp~(d, x).reset_if~(c != 0)
```

- 入力: x = 0 3 0 0 2、c = 0 0 1 0 0
- 手で出した期待: `0 708 0 0 506`
- 根拠: §11.10（par の中の欄も T.default() に戻る）。

### A1-1（A1）

```onsa
let d = gen~(x)
if~ c != 0 { cnt~(d) } else { acc~(d) }
```

- 入力: x = 0 3 0 5、c = 1 0 1 0
- 手で出した期待: `0 203 3 408`
- 根拠: §11.5「全ての枝の状態を持つものが進み」（イベントの段も）。

### A1-2（A1）

```onsa
if~ c != 0 { gen~(x) at sample } else { 0 }
```

- 入力: x = 0 3 0 5、c = 1 0 1 1
- 手で出した期待: `0 0 3 5`
- 根拠: §11.5（取られない腕の作り手も出す。位置 1 の 3 を位置 2 で読む）。

### A1-3（A1）

```onsa
let d = gen~(x)
if~ c != 0 { runs~() + (d + 1) } else { 0 }
```

- 入力: x = 0 0 3 0、c = 1 1 1 0
- 手で出した期待: `1 2 7 0`
- 根拠: §11.3「条件の位置は、…`if~` / `match~` の腕は含めない）」。腕の中の `d + 1` は d の刻みで評価する欄（最初のイベントの前は 0）。

### A1-4（A1）

```onsa
let g = genz~(y)
if~ g == 0 { runs~() } else { 100 }
```

- 入力: y = 0 0 1 0 3 0
- 手で出した期待: `100 100 3 4 100 100`
- 根拠: §11.3（if~ の最初の条件は条件の位置でない。`g == 0` は g の刻みの欄で、最初のイベントの前は false）。

### A1-5（A1）

```onsa
let v = genv~(x)
match~ v { V.A(n) => ek~(n), V.B => 7 }
```

- 入力: x = 0 3 7 2 0
- 手で出した期待: `7 4 7 413 413`
- 根拠: §11.5「match~ の取られない腕の束縛は…T.default()」「腕の本体で読む束縛のクロックは、対象のクロック…」、§11.11「インスタンスのその入力のクロックは引数のクロックに結び付く」。腕の受け手は v の全てのイベントで刻み、V.B のイベント（位置 2）では 0 を受ける。
- 注: 取られたイベントでだけ刻む読みでは位置 3 が 43（報告の「字で決まらない形」の確かめ）。v の欄の初めの値は V.default()（V.B）。

### A1-6（A1）

```onsa
let v = genv~(x)
match~ v { V.A(n) if n > 2 => ek~(n), _ => 7 }
```

- 入力: x = 0 3 7 2 4
- 手で出した期待: `7 4 7 7 4115`
- 根拠: §11.5（ガードの中で読む束縛は対象のクロック。ガードが偽のイベントでも受け手は刻み、束縛は 0）。
- 注: ガード付きの match~ がこの版で値まで動くかは確かめていない（普通の match は W8-06）。

### A1-7（A1）

```onsa
let d = gen~(x)
if~ c != 0 { prev~(d) at sample } else { d at sample }
```

- 入力: x = 0 3 0 5 0 2、c = 1 1 0 1 1 1
- 手で出した期待: `0 0 3 3 3 5`
- 根拠: §11.5、§11.4（腕の中のイベントのクロックの遅延は、選びによらずイベントごとに刻む）。

### A1-8（A1）

```onsa
let d = gen~(x)
if~ cnt~(d) > 4 { runs~() } else { 0 }
```

- 入力: x = 0 3 0 5
- 手で出した期待: `0 0 0 4`
- 根拠: §11.5（条件の中の受け手。選ぶ側が先、腕は常に進む）。

### A1-9（A1）

```onsa
if~ c != 0 { gen~(x) } else { gen~(y) }
```

- 入力: x = 0 3 0 0、y = 0 0 5 0、c = 1 0 0 1
- 手で出した期待: `0 0 5 3`
- 根拠: §11.11「条件…が周期の刻みのクロックの値…なら…周期のクロックの式で、要素と腕はその位置までの最後の値」（S-1239 (B2)）。

### A1-10（A1）

```onsa
let v = genv~(x)
match~ v { V.A(n) => runs~() * 100 + n, V.B => 0 }
```

- 入力: x = 0 3 7 2 0
- 手で出した期待: `0 203 0 402 502`
- 根拠: §11.5（束縛を sample の式で読む。値は `let n = …` と `if~` で書いた形と同じ）。

### A1-12（A1）

```onsa
let d = gen~(x)
if~ c != 0 { runs~().reset_if~(d != 0) } else { 0 }
```

- 入力: x = 0 0 3 0 0、c = 1 1 0 1 1
- 手で出した期待: `1 2 0 2 3`
- 根拠: §11.5・§11.10（取られない腕の中でも、イベントの刻みで戻し、sample で進む）。
