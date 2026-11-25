# イベント（§11.11）の値の表（W7-11 段 1、仕様の字だけから）

- 期待の出力は、模型を回す前に字から手で書いた値である。「模型: 一致」は `model.py` の出力と同じという意味で、81 件の全てが一致した。
- 作り直すとき: `python3 -B cases.py`（突き合わせ）、`python3 -B cases.py --md`（この表の本文）。
- 入力の列は位置 0 からの値、イベントは `(位置,入力,値)` を境界が渡す順に並べた。イベントの出力は `(位置,値)`。`Bool` は 0・1 で書いた。
- 模型は式のクロックを推論しない。各式のクロックは、組むときに §11.3・§11.11 の規則で手で決めた（`cases.py` の `Let` の第 2 引数）。
- 【字で決まらない】の印のある事例の値は、模型が選んだ読みの値である（報告の表に、割れる読みと値を並べた）。

## 共通の部品

```onsa
rt fn some_if(c: Bool, v: U32) -> Option[U32] { if c { Some(v) } else { None } }
rt fn stamp(m: U32, t: U32) -> U32 { t }

flow gen(x: U32 at sample) -> U32 at event { some_if(x != 0, x) }          // sample の式から出す
flow tick4() -> U32 at event { Some(1) at (sample / 4) }                   // sample / 4 の刻みごとに出す
flow fwd(e: U32 at event) -> U32 at event { Some(e * 10) }                 // イベントごとに出す
flow tally(e: U32 at event) -> U32 at event { let n = prev~(^n) + e
  Some(n) }
flow odd(e: U32 at event) -> U32 at event { some_if(e % 2 == 1, e) }
flow cnt(e: U32 at event) -> U32 at sample { let n = prev~(^n) + e          // イベントの値を足し、sample で読む
  n }
flow two(a: U32 at event, b: U32 at event) -> U32 at sample {
  let na = prev~(^na) + a
  let nb = prev~(^nb) + b
  (na at sample) * 100 + (nb at sample) }
flow hit(a: U32 at event, b: U32 at event) -> U32 at sample { cnt~(a).reset_if~(b != 0) }
flow part(m: U32 at event, s: U32 at sample) -> (U32, U32, U32) at event {  // 走りごとに (イベントの和, 頭の入力, 時間) を出す
  let n = prev~(^n) + m
  Some((n at sample, s, sample_tick())) }
flow partb(m: U32 at event, s: U32 at block) -> (U32, U32, U32) at event { // part の s を block にしたもの
  let n = prev~(^n) + m
  Some((n at sample, s at sample, sample_tick())) }
flow epart(m: U32 at event) -> (U32, U32) at event { Some((m, sample_tick())) }  // イベントごとに (値, 時間) を出す
flow acc(m: U32 at event) -> U32 at sample {                               // 動いた刻みの数 * 100 + イベントの和
  let n = prev~(^n) + m
  let k = prev~(^k) + 1
  k * 100 + n }
flow runs() -> U32 at sample { let k = prev~(^k) + 1                        // 動いた刻みの数
  k }
flow lastv(m: U32 at event) -> U32 at sample { m }
flow idf(x: U32 at sample) -> U32 at sample { x }
```

## (a) sample の式から出し、別の flow の at event の入力で受けて数え、sample で読む

### a1

```onsa
flow a1(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  cnt~(e)
}
```

- 入力 `x`: `0 1 0 2 0 0 3 0`
- フレーム: 8
- 期待の出力: `0 1 1 3 3 3 6 6`
- 模型: 一致
- 注: 同じ位置で見える。§11.11「受け手は名前の順で作り手より下にあり、その位置の受け手の段の前に届く」

### a2

```onsa
flow cnt2(e: U32 at event) -> U32 at sample { let n = prev~(^n) + e
  let m = n at (sample / 2)
  m at sample }
flow a2(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  cnt2~(e)
}
```

- 入力 `x`: `0 1 0 2 0 0 3 0 0 0`
- フレーム: 10
- 期待の出力: `0 0 1 1 3 3 3 3 6 6`
- 模型: 一致
- 注: sample の段が出したイベントは、同じ位置の sample / 2 の刻みには見えず、次の刻みから。§11.9「同じ位置で速い段が出したイベントは、それより遅い周期の刻みには次の刻みで見える」。位置 6 のイベントは位置 8 から

### a3

```onsa
flow a3(m: U32 at event) -> U32 at sample { cnt~(m) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',5) (1,'m',7) (3,'m',1)`
- フレーム: 4
- 期待の出力: `0 12 12 13`
- 模型: 一致
- 注: 入力のイベント。§11.11「サンプルのクロックの式からは、その位置のイベントを全て処理した後の状態が見える」

### a4

```onsa
flow a4(m: U32 at event) -> U32 at sample { let pm = prev~(m, 9)
  pm }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',5) (4,'m',7)`
- フレーム: 6
- 期待の出力: `0 0 9 9 5 5`
- 模型: 一致
- 注: 最初のイベントの前に sample で読む値は init の 9 でなく T.default() の 0。§11.11「最初のイベントの前は T.default()」、§11.3「刻みで書いて速い段が読むフィールド…の初めの値…は T.default()」。9 は最初のイベントの刻みの値

### a5

```onsa
flow a5(e: U32 at event) -> U32 at sample { let n = prev~(^n) + 1
  n }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'e',5) (1,'e',7) (3,'e',1)`
- フレーム: 4
- 期待の出力: `1 2 3 4`
- 模型: 一致
- 注: イベントの値を読まない輪は、at event の入力を持つ flow の中でも本体の sample で刻み、サンプルを数える（§11.3「外から刻みのクロックが入らなければ、本体の sample である（let c = prev~(^c) + 1）」）。イベントを数えるには輪にイベントの値を入れる（a6）

### a6

```onsa
rt fn bump(e: U32, n: U32) -> U32 { n + 1 }
flow a6(e: U32 at event) -> U32 at sample { let n = bump(e, prev~(^n))
  n }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'e',5) (1,'e',7) (3,'e',1)`
- フレーム: 4
- 期待の出力: `0 2 2 3`
- 模型: 一致
- 注: 輪に e が入るので e のクロックで刻み、イベントを数える（§11.11「let v = assign(m, prev~(^v)) は m の刻みの式」）


## (b) イベント → イベントと、その三段

### b1

```onsa
flow b1(m: U32 at event) -> U32 at event {
  let e1 = fwd~(m)
  let e2 = fwd~(e1)
  let e3 = fwd~(e2)
  Some(e3)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (2,'m',2) (2,'m',3)`
- フレーム: 3
- 期待の出力（位置, 値）: `(0,1000) (2,2000) (2,3000)`
- 模型: 一致
- 注: 三段とも入力のイベントの位置で、そのイベントの刻みの直後に続く。§11.11「入力 m のイベントの値なら m のイベントごと」「出したイベントの刻みは出した刻みの直後に並ぶ」

### b2

```onsa
flow b2(m: U32 at event) -> U32 at event {
  let e1 = tally~(m)
  let e2 = tally~(e1)
  let e3 = tally~(e2)
  Some(e3)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (1,'m',1) (3,'m',1)`
- フレーム: 4
- 期待の出力（位置, 値）: `(1,1) (1,4) (3,10)`
- 模型: 一致
- 注: 各段の prev~ は自分の入力のイベントで一つ前（§11.4「第 1 引数がイベントの値なら一つ前のイベント」）

### b3

```onsa
flow b3(m: U32 at event) -> U32 at sample {
  let o = odd~(m)
  cnt~(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (0,'m',2) (1,'m',3) (3,'m',4)`
- フレーム: 4
- 期待の出力: `1 4 4 4`
- 模型: 一致
- 注: None は出さない

### b4

```onsa
flow b4(m: U32 at event) -> U32 at sample {
  let e1 = fwd~(m)
  cnt~(m).reset_if~(e1 != 0)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',5) (1,'m',6) (1,'m',7)`
- フレーム: 3
- 期待の出力: `5 7 7`
- 模型: 一致
- 注: 【字で決まらない】m の一つの刻みの中で、作り手 fwd より下の m の段（cnt）と、fwd が出した e1 の刻み（初期化）の順。模型は「作り手の呼び出しの直後」（初期化が先で、数えた値が残る）。「m の刻みの全体の後」と読むと 0 0 0


## (c) 同じ位置で、二つの作り手のイベントを一つの受け手が別の入力で受ける

### c1

```onsa
flow c1(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ea = gen~(x)
  let eb = gen~(y)
  two~(ea, eb)
}
```

- 入力 `x`: `0 1 1 0`
- 入力 `y`: `0 2 0 2`
- フレーム: 4
- 期待の出力: `0 102 202 204`
- 模型: 一致
- 注: 受け手の中で二つの入力の状態は交わらないので、順は見えない

### c2

```onsa
flow c2(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let eb = gen~(y)
  let ea = gen~(x)
  two~(ea, eb)
}
```

- 入力 `x`: `0 1 1 0`
- 入力 `y`: `0 2 0 2`
- フレーム: 4
- 期待の出力: `0 102 202 204`
- 模型: 一致
- 注: c1 と同じ

### c3

```onsa
flow c3(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ea = gen~(x)
  let eb = gen~(y)
  hit~(ea, eb)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 0 0 0`
- 模型: 一致
- 注: 順が見えるのは初期化。ea が先: 数えてから初期化（値の欄も T.default() に戻る）。§11.11「出したイベントの刻みは出した刻みの直後」＝ 作り手の let の順

### c4

```onsa
flow c4(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let eb = gen~(y)
  let ea = gen~(x)
  hit~(ea, eb)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 1 1 1`
- 模型: 一致
- 注: eb が先: 初期化してから数える。引数の順は同じで、let の順だけが違う

### c5a

```onsa
flow c5(a: U32 at event, b: U32 at event) -> U32 at sample { hit~(a, b) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',1) (1,'a',1) (1,'b',1)`
- フレーム: 2
- 期待の出力: `1 0`
- 模型: 一致
- 注: 入力をまたいだ順は境界が渡す列の順（§11.11 同じ位置の順、§11.6「入力をまたいだ順は列の順だけで決まる」）

### c5b

```onsa
flow c5(a: U32 at event, b: U32 at event) -> U32 at sample { hit~(a, b) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',1) (1,'b',1) (1,'a',1)`
- フレーム: 2
- 期待の出力: `1 1`
- 模型: 一致
- 注: 列の順を入れ替えた


## (d) `cnt~(ex).reset_if~(ey != 0)`

### d1

```onsa
flow d1(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ex = gen~(x)
  let ey = gen~(y)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 0 0 0`
- 模型: 一致
- 注: c3 を直に書いた形。ex が先

### d2

```onsa
flow d2(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ey = gen~(y)
  let ex = gen~(x)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 1 1 1`
- 模型: 一致
- 注: ey が先

### d3

```onsa
flow d3(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ex = gen~(x)
  let ey = tick4~()
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `1 1 1 1 1 1`
- 入力 `y`: `0 0 0 0 0 0`
- フレーム: 6
- 期待の出力: `1 2 3 4 1 2`
- 模型: 一致
- 注: ey は遅い刻みの段から出るので、let の順によらず sample の段の ex より先（§11.9「入力のイベントの刻み、遅い刻み、sample の刻みの順」「修飾子の無い部品の中の遅い刻みは、呼び出し側の同じ比の段に…入る」）

### d3r

```onsa
flow d3r(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ey = tick4~()
  let ex = gen~(x)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `1 1 1 1 1 1`
- 入力 `y`: `0 0 0 0 0 0`
- フレーム: 6
- 期待の出力: `1 2 3 4 1 2`
- 模型: 一致
- 注: d3 の let の順を入れ替えた。同じ

### d4

```onsa
flow d4(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ex = tick4~()
  let ey = gen~(y)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 0 0`
- 模型: 一致
- 注: ex が遅い刻みの段。位置 4 は、数えて（2）から sample の段の ey で初期化

### d4r

```onsa
flow d4r(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ey = gen~(y)
  let ex = tick4~()
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 0 0`
- 模型: 一致
- 注: let の順を入れ替えても同じ（段の順が先）

### d5

```onsa
flow d5(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ey = gen~(y)
  let ex = tick4~().when~(true)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 1 1`
- 模型: 一致
- 注: d4r に when~(true) を付けると値が変わる。W は sample（イベントの出力なので P）で、中の sample / 4 の刻みは W の段の呼び出しの位置で動く（§11.9「when~ で止まる部品では、W より遅い中の刻みも、その W の段の中で先に動く」）。ey の初期化が先になり、数えた 1 が残る

### d6

```onsa
flow d6(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ex = tick4~().when~(true)
  let ey = gen~(y)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 0 0`
- 模型: 一致
- 注: d5 の let の順を入れ替えると、sample の段の中の書いた順で ex が先


## (e) `.down~`・`.up~`・塊の部品のイベントの入力と出力

### e1

```onsa
flow e1(m: U32 at event) -> (U32, U32, U32) at event {
  let o = part~(m, sample_tick()).down~(4)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (4,'m',2) (5,'m',4)`
- フレーム: 10
- 期待の出力（位置, 値）: `(0,(0,0,0)) (4,(3,4,1)) (8,(7,8,2))`
- 模型: 一致
- 注: イベントは来た位置で処理し、走り（位置 0・4・8）は、その位置の入力のイベントまで見る（位置 4 の走りは位置 4 の 2 を含む 3）。頭の sample_tick() は呼び出し側の sample / 4 の刻みの時間（位置）、部品の中は 1/4（§11.4）

### e2

```onsa
flow e2(m: U32 at event, b: U32 at block) -> (U32, U32, U32) at event {
  let o = partb~(m, b).up~(2)
  Some(o)
}
```

- `block` の入力 `b`: `7`
- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (2,'m',2)`
- フレーム: 3
- 期待の出力（位置, 値）: `(0,(0,7,0)) (0,(0,7,1)) (1,(1,7,2)) (1,(1,7,3)) (2,(3,7,4)) (2,(3,7,5))`
- 模型: 一致
- 注: .up~(2) だけの頭の sample の入力は sample * 2 になり、パラメータの種類しか渡せない（§11.4・§11.11）。イベントはその位置の最初の刻みの前。出すイベントは同じ位置に内側の刻みの順

### e3

```onsa
flow e3(m: U32 at event, x: U32 at sample) -> (U32, U32, U32) at event {
  let o = part~(m, x).up~(2).down~(2)
  Some(o)
}
```

- 入力 `x`: `10 11 12 13 14 15`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (2,'m',4) (3,'m',8)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(1,0,0)) (0,(1,0,1)) (2,(7,10,2)) (2,(7,11,3)) (4,(15,12,4)) (4,(15,13,5))`
- 模型: 一致
- 注: 塊。位置 2 の境界の走りは、入力 x[0]・x[1]（2 サンプル遅れ）を読みながら、位置 2 までのイベント（7）を見る（§11.11「走りは、読む入力より 1〜N サンプル後の位置のイベントまで見ている」）。出すイベントは二つとも境界の位置

### e4

```onsa
flow e4(m: U32 at event) -> (U32, U32, U32) at event {
  let o = part~(m, sample_tick()).up~(2).down~(4)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (4,'m',2) (6,'m',4)`
- フレーム: 10
- 期待の出力（位置, 値）: `(0,(0,0,0)) (0,(0,0,1)) (4,(3,0,2)) (4,(3,2,3)) (8,(7,4,4)) (8,(7,6,5))`
- 模型: 一致
- 注: 頭の入力は呼び出し側の sample / 2 で、境界（sample / 4）で二つ集める（位置 c − 4・c − 2 の時間）。位置 6 のイベントは位置 8 の走りから

### e5

```onsa
flow e5(m: U32 at event) -> (U32, U32) at event {
  let o = epart~(m).down~(4)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',0) (1,'m',1) (2,'m',2) (3,'m',3) (4,'m',4) (5,'m',5)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(0,0)) (1,(1,0)) (2,(2,0)) (3,(3,0)) (4,(4,1)) (5,(5,1))`
- 模型: 一致
- 注: 入力のイベントごとの出力は来た位置で出る（§11.11「全ての位置のイベントで動く」）。時間は位置を 4 で割って切り捨て（§11.4「イベントの段の式ではその位置の値」。.up~ の何歩目かは字に無く、S-1229 の事例の式 floor(p / N) * M で読んだ）

### e6

```onsa
flow e6(m: U32 at event) -> (U32, U32) at event {
  let o = epart~(m).up~(2)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',0) (1,'m',1) (2,'m',2) (3,'m',3) (4,'m',4) (5,'m',5)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(0,0)) (1,(1,2)) (2,(2,4)) (3,(3,6)) (4,(4,8)) (5,(5,10))`
- 模型: 一致
- 注: 入力のイベントごとの出力は来た位置で出る（§11.11「全ての位置のイベントで動く」）。時間は位置の 2 倍（最初の刻みの前なので 0 歩目）（§11.4「イベントの段の式ではその位置の値」。.up~ の何歩目かは字に無く、S-1229 の事例の式 floor(p / N) * M で読んだ）

### e7

```onsa
flow e7(m: U32 at event) -> (U32, U32) at event {
  let o = epart~(m).up~(2).down~(2)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',0) (1,'m',1) (2,'m',2) (3,'m',3) (4,'m',4) (5,'m',5)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(0,0)) (1,(1,0)) (2,(2,2)) (3,(3,2)) (4,(4,4)) (5,(5,4))`
- 模型: 一致
- 注: 入力のイベントごとの出力は来た位置で出る（§11.11「全ての位置のイベントで動く」）。時間は floor(p / 2) * 2。奇数の位置でも境界の刻みの時間（§11.4「イベントの段の式ではその位置の値」。.up~ の何歩目かは字に無く、S-1229 の事例の式 floor(p / N) * M で読んだ）

### e8

```onsa
flow e8(m: U32 at event) -> (U32, U32) at event {
  let o = epart~(m).up~(2).down~(4)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',0) (1,'m',1) (2,'m',2) (3,'m',3) (4,'m',4) (5,'m',5)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(0,0)) (1,(1,0)) (2,(2,0)) (3,(3,0)) (4,(4,2)) (5,(5,2))`
- 模型: 一致
- 注: 入力のイベントごとの出力は来た位置で出る（§11.11「全ての位置のイベントで動く」）。時間は floor(p / 4) * 2（§11.4「イベントの段の式ではその位置の値」。.up~ の何歩目かは字に無く、S-1229 の事例の式 floor(p / N) * M で読んだ）

### e9

```onsa
flow e9(x: U32 at sample) -> (U32, U32, U32) at event {
  let e = gen~(x)
  let o = part~(e, sample_tick()).down~(4)
  Some(o)
}
```

- 入力 `x`: `0 0 0 0 5 0 0 0 0`
- フレーム: 9
- 期待の出力（位置, 値）: `(0,(0,0,0)) (4,(0,4,1)) (8,(5,8,2))`
- 模型: 一致
- 注: e1 と違い、位置 4 のイベントは sample の段が出すので、位置 4 の走り（遅い刻み）には見えず、位置 8 から（§11.9「同じ位置で速い段が出したイベントは…次の刻みで見える」）


## (f) `when~` で止まった部品

### f1

```onsa
flow f1(m: U32 at event, c: Bool at sample) -> U32 at sample { acc~(m).when~(c) }
```

- 入力 `c`: `0 0 1 1 0 0 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (4,'m',2) (5,'m',4)`
- フレーム: 7
- 期待の出力: `0 0 101 201 201 201 307`
- 模型: 一致
- 注: 止まっている間のイベント（位置 0・4・5）も処理するが、出力は保持で、次に動く刻み（位置 2・6）の値に出る。一度も動く前は T.default()（§11.10）

### f2

```onsa
flow f2(m: U32 at event, c: Bool at sample) -> U32 at event {
  let o = fwd~(m).when~(c)
  Some(o)
}
```

- 入力 `c`: `0 0 0 0`
- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (3,'m',2)`
- フレーム: 4
- 期待の出力（位置, 値）: `(1,10) (3,20)`
- 模型: 一致
- 注: 止まっていても、入力のイベントごとの出力は出る（§11.10・§11.11）

### f3

```onsa
flow f3(x: U32 at sample, c: Bool at sample) -> U32 at event {
  let o = gen~(x).when~(c)
  Some(o)
}
```

- 入力 `x`: `1 2 3 4`
- 入力 `c`: `1 0 0 1`
- フレーム: 4
- 期待の出力（位置, 値）: `(0,1) (3,4)`
- 模型: 一致
- 注: 周期のクロックの式の出力は、止まっている間は出さない（§11.11）

### f4

```onsa
flow f4(m: U32 at event, x: U32 at sample, c: Bool at sample) -> (U32, U32, U32) at event {
  let o = part~(m, x).when~(c)
  Some(o)
}
```

- 入力 `x`: `10 11 12 13`
- 入力 `c`: `0 1 0 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (2,'m',2)`
- フレーム: 4
- 期待の出力（位置, 値）: `(1,(1,11,1)) (3,(3,13,3))`
- 模型: 一致
- 注: when~ の中の sample_tick() は外と同じ（動いた数でない、§11.4）

### f5

```onsa
flow f5(m: U32 at event) -> U32 at sample { acc~(m).when~(m != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1) (4,'m',0) (5,'m',3)`
- フレーム: 6
- 期待の出力: `0 0 101 201 201 304`
- 模型: 一致
- 注: イベントの値の条件は、W の刻みでその位置までの最後の値の水準。イベントの位置の sample の刻みから動く／止まる（§11.10）

### f6

```onsa
flow f6(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  acc~(e).when~(e != 0)
}
```

- 入力 `x`: `0 5 0 0`
- フレーム: 4
- 期待の出力: `0 105 205 305`
- 模型: 一致
- 注: sample の段が出したイベントも、下の受け手の条件は同じ位置で見る


## (g) `reset_if~` のイベントの条件

### g1

```onsa
flow g1(x: U32 at sample, r: U32 at event) -> U32 at sample { prev~(x, 9).reset_if~(r != 0) }
```

- 入力 `x`: `1 2 3 4 5`
- イベント（位置, 入力, 値。境界が渡す順）: `(2,'r',1)`
- フレーム: 5
- 期待の出力: `9 1 9 3 4`
- 模型: 一致
- 注: 受け手が遅延。イベントの刻みで init に戻り、その位置の sample の刻みが init を出す（§11.10「その刻みに続く x の段の前に」）

### g2a

```onsa
flow g2(m: U32 at event, r: U32 at event) -> U32 at sample { cnt~(m).reset_if~(r != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (2,'r',1) (3,'m',4) (4,'r',0) (5,'r',1) (5,'m',8)`
- フレーム: 6
- 期待の出力: `1 3 0 4 4 8`
- 模型: 一致
- 注: 受け手がインスタンス。位置 2 で値の欄も T.default() に戻る（S-1186）。r の値が 0 のイベント（位置 4）は条件が偽で初期化しない

### g2b

```onsa
flow g2(m: U32 at event, r: U32 at event) -> U32 at sample { cnt~(m).reset_if~(r != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (2,'r',1) (3,'m',4) (4,'r',0) (5,'m',8) (5,'r',1)`
- フレーム: 6
- 期待の出力: `1 3 0 4 4 0`
- 模型: 一致
- 注: 位置 5 の列の順を入れ替えた

### g3a

```onsa
flow g2(m: U32 at event, r: U32 at event) -> U32 at sample { cnt~(m).reset_if~(r != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (2,'r',1) (2,'m',5) (2,'r',0)`
- フレーム: 4
- 期待の出力: `1 1 5 5`
- 模型: 一致
- 注: 同じ位置に二つの r。条件はイベントの刻みごとに読む（真の刻みだけ初期化）

### g3b

```onsa
flow g2(m: U32 at event, r: U32 at event) -> U32 at sample { cnt~(m).reset_if~(r != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (2,'r',0) (2,'m',5) (2,'r',1)`
- フレーム: 4
- 期待の出力: `1 1 0 0`
- 模型: 一致
- 注: 真の刻みが後

### g4a

```onsa
flow g4a(m: U32 at event, r: U32 at event, c: Bool at sample) -> U32 at sample {
  acc~(m).when~(c).reset_if~(r != 0)
}
```

- 入力 `c`: `1 1 0 0 1 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (3,'r',1)`
- フレーム: 6
- 期待の出力: `101 201 201 0 100 200`
- 模型: 一致
- 注: 受け手が連鎖。止まっている間（位置 3）に初期化し、保持した出力も T.default() に戻る（§11.10 合成）

### g4b

```onsa
flow g4b(m: U32 at event, r: U32 at event, c: Bool at sample) -> U32 at sample {
  acc~(m).reset_if~(r != 0).when~(c)
}
```

- 入力 `c`: `1 1 0 0 1 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (3,'r',1)`
- フレーム: 6
- 期待の出力: `101 201 201 201 100 200`
- 模型: 一致
- 注: 内の reset_if~ も止まっている間に初期化する。違いは保持した出力（位置 3 の 201）を戻さないことだけ（§11.10）

### g5

```onsa
flow g5(m: U32 at event, r: U32 at event) -> U32 at sample {
  let y = lastv~(m).reset_if~(r != 0)
  y * 10 + m
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',7) (2,'r',1) (4,'m',8)`
- フレーム: 5
- 期待の出力: `77 77 7 7 88`
- 模型: 一致
- 注: 値の欄の戻り（S-1186）。部品の中の m の欄は T.default() に戻り、呼び出し側の m の欄（一の位）は戻らない

### g6

```onsa
flow g6(m: U32 at event, r: U32 at event) -> U32 at sample {
  let y = cnt~(m).down~(4).reset_if~(r != 0)
  y at sample
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (5,'r',1) (6,'m',4)`
- フレーム: 10
- 期待の出力: `1 1 1 1 3 3 3 3 4 4`
- 模型: 一致
- 注: 格子の外の位置 5 で初期化する（走りの時点でない）。呼び出し側の y は次の走り（位置 8）まで前の値 3（§11.9「.down~(N) の出力は…次の自分の刻みまで前の値である（保持した出力の欄は持たない）」）。位置 8 は初期化の後の 4 だけ

### g7

```onsa
flow g7(m: U32 at event) -> U32 at sample { cnt~(m).reset_if~(m != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',3) (1,'m',4) (2,'m',0)`
- フレーム: 3
- 期待の出力: `3 4 4`
- 模型: 一致
- 注: 同じイベントが条件と入力の両方。初期化が先で、その刻みの受け手の段が後（§11.10「その刻みに続く x の段の前に」）。0 でないイベントの値だけが残る


## (h) イベントの値の読み方

### h1

```onsa
flow h1(v: U32 at event) -> U32 at sample { v at sample }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 5 5 5 5 0 7 7 7 7`
- 模型: 一致
- 注: その位置までの最後の値（§11.11 読み方）

### h2

```onsa
flow h2(v: U32 at event) -> U32 at sample { (v at (sample / 4)) at sample }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 0 0 0 5 5 5 5 7 7`
- 模型: 一致
- 注: sample / 4 の刻みで留めた値（§11.11「変換の場所を留める」）。位置 5 の 0 は格子に当たらず見えない

### h3

```onsa
flow h3(v: U32 at event) -> U32 at sample { let m = v at (sample / 4)
  m at sample }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 0 0 0 5 5 5 5 7 7`
- 模型: 一致
- 注: let に分けても h2 と同じ（§11.3「let は名前を付けるだけ」）

### h4

```onsa
flow h4(v: U32 at event) -> U32 at sample { let w = v
  w }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 5 5 5 5 0 7 7 7 7`
- 模型: 一致
- 注: v を読むだけの let は v のクロックの式（§11.11）。値は h1 と同じ

### h5

```onsa
flow h5(v: U32 at event) -> U32 at sample { runs~().when~(v != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 1 2 3 4 4 5 6 7 8`
- 模型: 一致
- 注: 条件の水準は sample の刻みごとの最後の値

### h6

```onsa
flow h6(v: U32 at event) -> U32 at sample { let m = v at (sample / 4)
  runs~().when~(m != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 0 0 0 1 2 3 4 5 6`
- 模型: 一致
- 注: W（sample）より遅い値は保持で読む（§11.10）。位置 5 の 0 は格子に当たらないので止まらない

### h7

```onsa
flow h7(v: U32 at event) -> U32 at sample { let y = runs~().down~(4).when~(v != 0)
  y at sample }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'v',5) (5,'v',0) (6,'v',7)`
- フレーム: 10
- 期待の出力: `0 0 0 0 1 1 1 1 2 2`
- 模型: 一致
- 注: 受け手の出力が sample / 4 なので W は sample / 4。イベントの値の水準は格子の刻み（位置 0・4・8）でだけ読む（§11.10 の W、S-1209）。位置 5 の 0 は見えない

### h8

```onsa
flow h8(v: U32 at event) -> U32 at sample { let w = v + 100
  w }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'v',5)`
- フレーム: 4
- 期待の出力: `0 0 105 105`
- 模型: 一致
- 注: w は v のクロックの式で、イベントの刻みでだけ計算する。最初のイベントの前に読むのは結果の型の T.default() の 0 で、100 ではない（§11.3「v * r はイベントの段」、§11.11「最初のイベントの前は T.default()」）

### h9

```onsa
flow h9(v: U32 at event) -> U32 at sample { (v at sample) + 100 }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'v',5)`
- フレーム: 4
- 期待の出力: `100 100 105 105`
- 模型: 一致
- 注: at を書くと sample の式で、v の欄（0）から毎刻み計算する（§11.3「(v at sample) * r…は sample で計算する」）

### h10

```onsa
flow h10(v: U32 at event) -> U32 at sample { runs~().when~(v == 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'v',0) (4,'v',3)`
- フレーム: 6
- 期待の出力: `0 0 1 2 2 2`
- 模型: 一致
- 注: 条件 v == 0 は v のクロックの式。最初のイベントの前は Bool の T.default() の偽で、「v は 0 だから真」にならない（S-1232 の補い「イベントのクロックの式を、when~ は最後の値の水準で…読む」）

### h11

```onsa
flow h11(v: U32 at event) -> U32 at sample { runs~().when~((v at sample) == 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'v',0) (4,'v',3)`
- フレーム: 6
- 期待の出力: `1 2 3 4 4 4`
- 模型: 一致
- 注: at を書くと sample の条件で、最初のイベントの前は v の欄の 0 と比べて真


## (i) `sample_tick()`

### i1

```onsa
flow i1(m: U32 at event) -> U32 at sample {
  let pl = prev~(^last)
  let last = if m != 0 { sample_tick() } else { pl }
  let d = sample_tick() -% last
  let el = sample_tick() -% (last at sample)
  d * 100 + el
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1) (5,'m',0) (6,'m',1)`
- フレーム: 8
- 期待の出力: `0 1 0 1 2 303 0 1`
- 模型: 一致
- 注: d は m のクロックの式で、イベントの位置の時間で止まる（S-1232）。ただし §11.4 の例の「いつも 0」は last を書き換えるイベントに限り、書き換えないイベント（位置 5 の m == 0）では 3 になる

### i2a

```onsa
flow i2a(m: U32 at event) -> U32 at sample {
  let t0 = stamp(m, sample_tick())
  runs~().when~(sample_tick() -% t0 < 2)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1)`
- フレーム: 6
- 期待の出力: `0 0 1 2 3 4`
- 模型: 一致
- 注: 条件は m のクロックの式（S-1232 (1)）。最初のイベントの前は Bool の T.default() の偽で止まり、イベントの後は 0 < 2 の真のまま（経過のゲートにならない）

### i2b

```onsa
flow i2b(m: U32 at event) -> U32 at sample {
  let t0 = stamp(m, sample_tick())
  runs~().when~(sample_tick() -% (t0 at sample) < 2)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1)`
- フレーム: 6
- 期待の出力: `1 2 3 4 4 4`
- 模型: 一致
- 注: at を書くと sample の条件で経過になる。最初のイベントの前は t0 が T.default() の 0 なので、位置 0・1 も開く

### i3

```onsa
flow i3(m: U32 at event) -> (U32, U32) at event { Some((m, sample_tick())) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',7) (3,'m',8)`
- フレーム: 4
- 期待の出力（位置, 値）: `(1,(7,1)) (3,(8,3))`
- 模型: 一致
- 注: イベントの段の sample_tick() はその位置の値（§11.4）

### i4

```onsa
flow i4(m: U32 at event) -> (U32, U32) at event {
  let o = epart~(m).when~(false)
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',7) (3,'m',8)`
- フレーム: 4
- 期待の出力（位置, 値）: `(1,(7,1)) (3,(8,3))`
- 模型: 一致
- 注: 止まっている部品のイベントの段も、外と同じ時間を読む（§11.4「止まっている間も進む」）

### i5a

```onsa
flow i5a(m: U32 at event) -> U32 at sample {
  let t0 = stamp(m, sample_tick())
  idf~(sample_tick() -% t0)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1)`
- フレーム: 5
- 期待の出力: `0 0 0 0 0`
- 模型: 一致
- 注: 頭の引数でも m のクロックの式で、sample の入力は最後の値（いつも 0）を読む（S-1232）

### i5b

```onsa
flow i5b(m: U32 at event) -> U32 at sample {
  let t0 = stamp(m, sample_tick())
  idf~(sample_tick() -% (t0 at sample))
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(2,'m',1)`
- フレーム: 5
- 期待の出力: `0 1 0 1 2`
- 模型: 一致
- 注: at を書いた形は経過


## (j) `par~`・`if~`

### j1

```onsa
flow j1(x: [U32; 2] at sample) -> [U32; 2] at sample {
  par~ i in 0 ..< 2 { a1~(x[i]) }
}
```

- 入力 `x`: `[1,0] [0,2] [3,3]`
- フレーム: 3
- 期待の出力: `[1,0] [1,2] [4,5]`
- 模型: 一致
- 注: 複製の中で作って受けるイベントは複製の中で閉じ、結果は sample の配列（a1 は (a) の flow）

### j2

```onsa
flow j2(m: U32 at event, c: Bool at sample) -> U32 at sample {
  if~ c { cnt~(m) } else { 0 }
}
```

- 入力 `c`: `1 0 0 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',5) (2,'m',6)`
- フレーム: 4
- 期待の出力: `0 0 0 11`
- 模型: 一致
- 注: if~ は全ての腕を進める（§11.5）。腕が選ばれていない刻みに来たイベントも数える


## (k) 名前の flow に包んだ双子

### k-a1

```onsa
flow gw(x: U32 at sample) -> U32 at event { let e = gen~(x)
  Some(e) }
flow ka1(x: U32 at sample) -> U32 at sample {
  let e = gw~(x)
  cnt~(e)
}
```

- 入力 `x`: `0 1 0 2 0 0 3 0`
- フレーム: 8
- 期待の出力: `0 1 1 3 3 3 6 6`
- 模型: 一致
- 注: a1 の双子。値は同じ。作り手を包む

### k-b1

```onsa
flow fw2(m: U32 at event) -> U32 at event { let a = fwd~(m)
  let b = fwd~(a)
  Some(b) }
flow kb1(m: U32 at event) -> U32 at event {
  let e2 = fw2~(m)
  let e3 = fwd~(e2)
  Some(e3)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (2,'m',2) (2,'m',3)`
- フレーム: 3
- 期待の出力（位置, 値）: `(0,1000) (2,2000) (2,3000)`
- 模型: 一致
- 注: b1 の双子。値は同じ。二段を包む

### k-d1

```onsa
flow kd1(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ea = gen~(x)
  let eb = gen~(y)
  hit~(ea, eb)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 0 0 0`
- 模型: 一致
- 注: d1 の双子。値は同じ。受け手の連鎖を包む（c3 と同じ形）

### k-d2

```onsa
flow kd2(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let eb = gen~(y)
  let ea = gen~(x)
  hit~(ea, eb)
}
```

- 入力 `x`: `1 1 0 1`
- 入力 `y`: `0 1 0 1`
- フレーム: 4
- 期待の出力: `1 1 1 1`
- 模型: 一致
- 注: d2 の双子。値は同じ。c4 と同じ形

### k-d4

```onsa
flow wt() -> U32 at event { let e = tick4~()
  Some(e) }
flow kd4(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ex = wt~()
  let ey = gen~(y)
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 0 0`
- 模型: 一致
- 注: d4 の双子。値は同じ。包んでも中の遅い刻みは呼び出し側の同じ比の段に入る（§11.9）

### k-d5

```onsa
flow wtw() -> U32 at event { let e = tick4~().when~(true)
  Some(e) }
flow kd5(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let ey = gen~(y)
  let ex = wtw~()
  cnt~(ex).reset_if~(ey != 0)
}
```

- 入力 `x`: `0 0 0 0 0 0`
- 入力 `y`: `0 0 0 0 1 0`
- フレーム: 6
- 期待の出力: `1 1 1 1 1 1`
- 模型: 一致
- 注: d5 の双子。値は同じ。when~ を本体に持つ flow も同じ（§11.10「名前の flow の本体の when~ も同じ」）

### k-e1

```onsa
flow wp(m: U32 at event, s: U32 at (sample / 4)) -> (U32, U32, U32) at event {
  let o = part~(m, s).down~(4)
  Some(o) }
flow ke1(m: U32 at event) -> (U32, U32, U32) at event {
  let o = wp~(m, sample_tick())
  Some(o)
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',1) (4,'m',2) (5,'m',4)`
- フレーム: 10
- 期待の出力（位置, 値）: `(0,(0,0,0)) (4,(3,4,1)) (8,(7,8,2))`
- 模型: 一致
- 注: e1 の双子。値は同じ。遅い値は sample / 4 のポートで渡す

### k-e3

```onsa
flow wc(m: U32 at event, s: U32 at sample) -> (U32, U32, U32) at event {
  let o = part~(m, s).up~(2).down~(2)
  Some(o) }
flow ke3(m: U32 at event, x: U32 at sample) -> (U32, U32, U32) at event {
  let o = wc~(m, x)
  Some(o)
}
```

- 入力 `x`: `10 11 12 13 14 15`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (2,'m',4) (3,'m',8)`
- フレーム: 6
- 期待の出力（位置, 値）: `(0,(1,0,0)) (0,(1,0,1)) (2,(7,10,2)) (2,(7,11,3)) (4,(15,12,4)) (4,(15,13,5))`
- 模型: 一致
- 注: e3 の双子。値は同じ。塊を包む

### k-f1

```onsa
flow f1(m: U32 at event, c: Bool at sample) -> U32 at sample { acc~(m).when~(c) }
flow kf1(m: U32 at event, c: Bool at sample) -> U32 at sample { f1~(m, c) }
```

- 入力 `c`: `0 0 1 1 0 0 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (4,'m',2) (5,'m',4)`
- フレーム: 7
- 期待の出力: `0 0 101 201 201 201 307`
- 模型: 一致
- 注: f1 の双子。値は同じ。when~ の連鎖を包む

### k-g4a

```onsa
flow f1(m: U32 at event, c: Bool at sample) -> U32 at sample { acc~(m).when~(c) }
flow kg4a(m: U32 at event, r: U32 at event, c: Bool at sample) -> U32 at sample {
  f1~(m, c).reset_if~(r != 0)
}
```

- 入力 `c`: `1 1 0 0 1 1`
- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (3,'r',1)`
- フレーム: 6
- 期待の出力: `101 201 201 0 100 200`
- 模型: 一致
- 注: g4a の双子。値は同じ。包んだ flow の中の保持した出力も初期化の範囲（§11.10「生成する reset…と同じ部分木…保持した出力」）

### k-g6a

```onsa
flow wd(m: U32 at event) -> U32 at (sample / 4) { cnt~(m).down~(4) }
flow kg6a(m: U32 at event, r: U32 at event) -> U32 at sample {
  let y = wd~(m).reset_if~(r != 0)
  y at sample
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (5,'r',1) (6,'m',4)`
- フレーム: 10
- 期待の出力: `1 1 1 1 3 3 3 3 4 4`
- 模型: 一致
- 注: g6 の双子。値は同じ。出力が sample / 4 の flow に包み、at は外に書く

### k-g6b

```onsa
flow ws(m: U32 at event) -> U32 at sample { let y = cnt~(m).down~(4)
  y at sample }
flow kg6b(m: U32 at event, r: U32 at event) -> U32 at sample { ws~(m).reset_if~(r != 0) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'m',1) (1,'m',2) (5,'r',1) (6,'m',4)`
- フレーム: 10
- 期待の出力: `1 1 1 1 3 0 0 0 4 4`
- 模型: 一致
- 注: g6 の双子。値が違う。at を部品の本体の中に書くと、その欄は部品の状態で、初期化で T.default() に戻る（位置 5〜7）。§11.9「部品の外に書いた at の欄も、次の自分の刻みまで前の値である。戻したいときは at を部品の本体の中に書く」

