# What a `when~` of an event does, in the values (W7-11 U3/e; §11.10, §11.11, §11.3, S-563, S-1209, S-1232)

- The values are worked out by hand from the text. The format is that of `event_values.md` (the table reader `event_table_tests.rs`).
- `gen~(x)` gives the event `x` where `x != 0`. The condition `e > 2` is an expression of the event (§11.11): its last value is read at each frame of W (`sample`), false before the first event (`Bool.default()`), and it does nothing at the event itself
  (§11.10: "イベントの条件でもイベントの刻みでは何もしない"). `(e at sample) < 3` is an expression of `sample` over the last value of `e` (0 before the first event, §11.3). A part that runs gives its runs; one that is stopped keeps its last output, `T.default()` before its first run.
- With x = `0 3 0 0 5 0 2 0` the events are 3 (position 1), 5 (position 4), 2 (position 6).

## 共通の部品

```onsa
rt fn some_if(c: Bool, v: U32) -> Option[U32] { if c { Some(v) } else { None } }

flow gen(x: U32 at sample) -> U32 at event { some_if(x != 0, x) }
flow runs() -> U32 at sample { let k = prev~(^k) + 1                        // 動いた刻みの数
  k }
flow grid2() -> U32 at sample { let k = prev~(^k at (sample / 2)) + 1       // 動いた刻みの 2 つに 1 つで数える
  k at sample }
flow cnt(e: U32 at event) -> U32 at sample { let n = prev~(^n) + e
  n }
flow flag(m: U32 at event) -> (Bool, U32) at event { Some((m > 2, m)) }
```

## (w) the level of an event

### w1

```onsa
flow w1(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  runs~().when~(e > 2)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 1 2 3 4 5 5 5`
- 注: `e > 2` is false before the first event, true from the event 3 (position 1) and the event 5, false from the event 2 (position 6): the runs are the positions 1 .. 5 (1 .. 5), and the output is kept at 5 after; `T.default()` (0) before the first run

### w2

```onsa
flow w2(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  runs~().when~(e < 3)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 0 0 0 0 0 1 2`
- 注: `e < 3` is an expression of the event, false before the first event (not "0 is under 3"); it is false for 3 and 5 and true at position 6 (the event 2): the runs are the positions 6 and 7

### w3

```onsa
flow w3(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  runs~().when~((e at sample) < 3)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `1 1 1 1 1 1 2 3`
- 注: with `at sample` the comparison is of `sample` over the last value, 0 before the first event: true at position 0 (run 1), false from the event 3 (positions 1 .. 5, the output kept at 1), true at position 6 and 7 (2, 3)

### w4

```onsa
flow w4(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  grid2~().when~(e > 2)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 1 1 2 2 3 3 3`
- 注: the part runs at the positions 1 .. 5 as its runs 0 .. 4, its grid of `sample / 2` ticks at the runs 0 2 4 (1 2 3) and keeps the value between; stopped from position 6 it keeps 3

### w5

```onsa
flow w5(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  let on = e > 2
  runs~().when~(on)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 1 2 3 4 5 5 5`
- 注: the level in a `let` is the same value as w1 (§11.3: a `let` only gives a name)

### w6

```onsa
flow w6(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  runs~().when~(e > 2).when~(e < 5)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 1 2 3 3 3 3 3`
- 注: both levels hold (`e > 2 && e < 5`) at the positions 1 .. 3 only (the event 5 of position 4 is not under 5, and the event 2 is not over 2): the runs 1 2 3, kept after

## (f) the field of an event read under a condition of `sample`

### f1

```onsa
flow f1(m: U32 at event, g: Bool at sample) -> U32 at sample {
  let t = flag~(m)
  if g && (t.0) { 1 } else { 0 }
}
```

- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',3) (3,'m',1) (5,'m',4)`
- 入力 `g`: `1 1 0 1 1 1 0`
- フレーム: 7
- 期待の出力: `0 1 0 0 0 1 0`
- 注: the field `t.0` (a `Bool`) is read at each event whatever `g` says (§11.3, S-1197: "フィールド・組の要素の読みは、条件によらず、守りを付けずに刻みごとに読む"), under parentheses too: false before the first event, true for 3 (positions 1 .. 2), false for 1 (3 .. 4), true for 4 (5 ..). The output is 1 where `g` holds and the field is true (positions 1 and 5)

## (u) a `when~` and the `reset_if~` of an event in one chain (W7-17 U4)

### u1

```onsa
flow u1(x: U32 at sample) -> U32 at sample {
  let e = gen~(x)
  runs~().when~(e > 2).reset_if~(e > 4)
}
```

- 入力 `x`: `0 3 0 0 5 0 2 0`
- フレーム: 8
- 期待の出力: `0 1 2 3 1 2 2 2`
- 注: a `when~` and the `reset_if~` of an event in one chain: `e > 2` runs the part at the positions 1 .. 5 (the event 2 of position 6 stops it, the output kept), and `e > 4` is true from the event 5 (position 4), which sets the part back at the event (the count and the kept output are 0 again) before its run of that position: 0 (not run), 1 2 3, then 1 (the count again from 1), 2, and 2 2 kept (§11.10: "イベントの条件は、外の `when~` が止めている間もその刻みで初期化する", a level: the events 3 and 2 give no true `e > 4`)
