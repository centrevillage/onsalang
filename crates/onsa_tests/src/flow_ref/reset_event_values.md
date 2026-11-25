# What a `reset_if~` of an event does, in the values (W7-11 U2r/e; §11.10, §11.11, §11.3, S-1236, S-1250 (B))

- The values are worked out by hand from the text. The format is that of `event_values.md` (the table reader `event_table_tests.rs`).
- A delay with a modifier is read where it is written and stored at the end of its stage (§11.3: "flow の値は、`^名前` の値だけを段の終わりのものとして、保存する値を書いた位置で評価して保存したのと同じである"), so a `reset_if~` whose event comes after the read of the delay
  and before its store (an event of a producer written below it) puts it back after the store (S-1250 (B)); one that comes before the read puts it back before the read.
- `e = prev~(^d)` gives the `d` before; with `d = gen~(x)` below and x = 1 6 2 7 3 4 1 1, `e >= 5` holds at the positions 2 and 4 (the events 6 and 7 of the positions before).

## 共通の部品

```onsa
rt fn some_if(c: Bool, v: U32) -> Option[U32] { if c { Some(v) } else { None } }

flow gen(x: U32 at sample) -> U32 at event { some_if(x != 0, x) }
flow cnt(e: U32 at event) -> U32 at sample {
  let n = prev~(^n) + e
  n }
flow hit(a: U32 at event, b: U32 at event) -> U32 at sample { cnt~(a).reset_if~(b != 0) }
```

## (s) a delay of `sample`, the producer of the event below it

### s1

```onsa
flow s1(x: U32 at sample) -> U32 at sample {
  let e = prev~(^d)
  let o = prev~(x, 9).reset_if~(e >= 5)
  let d = gen~(x)
  o
}
```

- 入力 `x`: `1 6 2 7 3 4 1 1`
- フレーム: 8
- 期待の出力: `9 1 6 9 7 9 4 1`
- 注: the reset at the positions 2 and 4 comes after the read and the store of the position: the output of the position is the delay's, the next one is the init (without the reset `9 1 6 2 7 3 4 1`)

### s2

```onsa
flow s2(x: U32 at sample) -> U32 at sample {
  let e = prev~(^d)
  let o = delay~(x, 2, 9).reset_if~(e >= 5)
  let d = gen~(x)
  o
}
```

- 入力 `x`: `1 6 2 7 3 4 1 1`
- フレーム: 8
- 期待の出力: `9 9 1 9 9 9 9 4`
- 注: the line is back to the init with its write place after the store of the positions 2 and 4

### s3

```onsa
flow s3(x: U32 at sample) -> U32 at sample {
  let e = prev~(^d)
  let o = prev~(prev~(x, 9).reset_if~(e >= 5), 7)
  let d = gen~(x)
  o
}
```

- 入力 `x`: `1 6 2 7 3 4 1 1`
- フレーム: 8
- 期待の出力: `7 9 1 6 9 7 9 4`
- 注: the inner delay's output is its value where it is written (a later reset does not change it): the outer one gives the inner outputs `9 1 6 9 7 9 4 1` a position later

### s4

```onsa
flow s4() -> U32 at sample {
  let e = prev~(^d)
  let c: U32 = prev~(^c + 1).reset_if~(e >= 5)
  let d = gen~(c)
  c
}
```

- フレーム: 12
- 期待の出力: `0 1 2 3 4 5 6 0 1 0 1 2`
- 注: the counter reads 0 1 .. 6; at the position 6 `e` is the `d` before (5, held to be 6 at the next event): the event of the position 6 gives e = 5 there and the reset comes after the read and the store: 0 at the position 7; `d` gives c = 1 at the position 8 and e = 6 there, back to 0 at the position 9

### s5

```onsa
flow s5(x: U32 at sample) -> U32 at sample {
  let d = gen~(x)
  let e = prev~(d)
  let o = prev~(x, 9).reset_if~(e >= 5)
  o
}
```

- 入力 `x`: `1 6 2 7 3 4 1 1`
- フレーム: 8
- 期待の出力: `9 1 9 2 9 3 4 1`
- 注: the event of `e` comes before the line of the delay: the reset is before the read (the init is given at the positions 2 and 4) and the stored `x` of the position is what the next one reads

## (t) a delay of an event reset by another event

### t1

```onsa
flow t1(v: U32 at sample, a: U32 at sample) -> U32 at sample {
  let ev = gen~(v)
  let ea = gen~(a)
  let p = prev~(ev, 9).reset_if~(ea > 0)
  p at sample
}
```

- 入力 `v`: `5 0 0 7 0 3 0 0`
- 入力 `a`: `0 0 0 0 1 0 0 0`
- フレーム: 8
- 期待の出力: `9 9 9 5 5 9 9 9`
- 注: what the caller reads (`p at sample`) is the value of the last tick of `ev` until the next tick: the reset at the position 4 puts the delay back, not the value read; the tick of the position 5 gives the init 9

### t2

```onsa
flow t2(a: U32 at event, b: U32 at event) -> U32 at sample {
  let p = prev~(a, 9).reset_if~(b > 0)
  p at sample
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',1) (0,'a',2) (0,'b',1) (1,'a',3)`
- フレーム: 2
- 期待の出力: `1 9`
- 注: two events of one input at one position, each ticks the delay once (the first gives 9, the second 1), and the event of `b` puts it back: the position 1 gives the init

### t3

```onsa
flow t3(a: U32 at event, b: U32 at event) -> U32 at sample {
  let p = prev~(a, 9).reset_if~(b > 0)
  p at sample
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',1) (0,'b',1) (0,'a',2) (1,'a',3)`
- フレーム: 2
- 期待の出力: `9 2`
- 注: the reset between the two ticks: the second tick gives the init 9 too (the last output of the position 0), and what it stores (2) is what the tick of the position 1 gives

## (u) an instance reset by an event of an input

### u1

```onsa
flow u1(a: U32 at event, b: U32 at event) -> U32 at sample { hit~(a, b) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',3) (0,'a',4) (1,'b',1) (2,'a',5) (2,'a',1) (2,'b',1) (3,'b',1) (3,'a',2)`
- フレーム: 4
- 期待の出力: `7 0 0 2`
- 注: position 0: 3 + 4; position 1: the reset; position 2: 5 + 1 and then the reset gives 0; position 3: the reset, then 2 (the events of a position go in the order the boundary gives them)

### u2

```onsa
flow u2(a: U32 at event) -> U32 at sample { cnt~(a).reset_if~(a >= 5) }
```

- イベント（位置, 入力, 値。境界が渡す順）: `(0,'a',3) (1,'a',5) (2,'a',1) (3,'a',9) (3,'a',2)`
- フレーム: 4
- 期待の出力: `3 5 6 11`
- 注: the condition is the event of the input itself: it puts back before the event is added (§11.10: "直に書いた `acc~(m).reset_if~(m != 0)` は戻してから足す"): 3, 5 (back, then 5), 6, then 9 (back, then 9) and 2 (no reset: 11)

### u3

```onsa
flow u3(x: U32 at sample) -> U32 at sample {
  let m = gen~(x)
  cnt~(m).reset_if~(((sample_tick() at (sample / 4)) % 8) == 0)
}
```

- 入力 `x`: `1 1 1 1 1 1 1 1 1 1 1 1`
- フレーム: 12
- 期待の出力: `1 2 3 4 5 6 7 8 1 2 3 4`
- 注: the condition is a tick of `sample / 4`, which holds at the positions 0 and 8 and is read before the `sample` stage: the part is put back before the event of the position is added (§11.10)

## (v) a producer in the condition of a delay

### v1

```onsa
flow v1(x: U32 at sample) -> U32 at sample {
  prev~(x, 9).reset_if~(gen~(x) >= 5)
}
```

- 入力 `x`: `1 6 2 7 3 4 1 1`
- フレーム: 8
- 期待の出力: `9 9 6 9 7 3 4 1`
- 注: the call in the condition is done where the delay is written, and the reset it gives is before the read: the stored 6 and 7 are gone before they are read
