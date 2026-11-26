# A delay of the clock of an event, read at the period (W7-17 U6b-e; §11.4, §11.3, §11.11, S-1237)

- The values are worked out by hand from the text. A delay ticks at the clock of its first argument and its output is the value of that clock: for `prev~(^g)` with `g` an event, the value of `g` at the event before. What a part at `sample` reads of it is the last value, the output at the last event, and `T.default()` before the first.
  An expression of an event (`prev~(^a) == 0`, with no `at sample`) is evaluated at the events and has `T.default()` before the first.
- `plus1` gives `Some(x + 1)` at each frame (x the input at `sample`), `fwd` gives its input as the event, `held_p` gives `Some((m at sample) + 1)` at each frame, m the last event of its input.
- p1 .. p3 are the three tests of event_own_output_read_values.onsa: the delay is written in the call that gives the events it ticks at (`g` of `let g = fwd~(plus1~(prev~(^g)))`), a delay of the events of `g` written in the call of `g`. The other cases are
  the same read in another place of that call (the first argument of a delay, a bracket and an operator, an init), and the call of another one that is called later, and a delay of the events of an input.

## 共通の部品

```onsa
flow fwd(m: U32 at event) -> U32 at event { Some(m) }
flow held_p(m: U32 at event) -> U32 at event { Some((m at sample) + 1) }
flow plus1(x: U32 at sample) -> U32 at event { Some(x + 1) }
```

### p1

```onsa
flow p1() -> U32 at sample {
  let g: U32 = fwd~(plus1~(prev~(^g)))
  g at sample
}
```

- フレーム: 8
- 期待の出力: `1 1 2 2 3 3 4 4`
- 注: the delay gives, at each event of g, the g of the event before (0 first); x is the last of those (0 before the first event), g is x + 1 at each frame: x = 0 0 1 1 2 2 3 3.

### p2

```onsa
flow p2(x: U32 at sample) -> U32 at sample {
  let a: U32 = held_p~(prev~(^a, 5)).when~(prev~(^a) == 0)
  (a at sample) + x
}
```

- 入力 `x`: `0 3 0 0 5 2 0 7`
- フレーム: 8
- 期待の出力: `0 3 0 0 5 2 0 7`
- 注: the condition is of the clock of the events of a, `T.default()` (false) before the first, so the part never runs.

### p3

```onsa
flow p3(x: U32 at sample) -> U32 at sample {
  let a: U32 = held_p~(prev~(^a, 5)).when~((prev~(^a) at sample) == 0)
  (a at sample) + x
}
```

- 入力 `x`: `0 3 0 0 5 2 0 7`
- フレーム: 8
- 期待の出力: `1 9 6 6 11 8 6 13`
- 注: the condition reads the last event of the delay (0 before the first).

### q1

```onsa
flow q1() -> U32 at sample {
  let d = prev~(^g)
  let g: U32 = fwd~(plus1~(d))
  g at sample
}
```

- フレーム: 8
- 期待の出力: `1 1 2 2 3 3 4 4`
- 注: the control of p1: the delay in a `let` of its own, which is a step of the events of g.

### q2

```onsa
flow q2() -> U32 at sample {
  let g: U32 = fwd~(plus1~((prev~(^g) at sample) + 0))
  g at sample
}
```

- フレーム: 8
- 期待の出力: `1 1 2 2 3 3 4 4`
- 注: p1 with the delay under an `at sample` and an operator.

### q3

```onsa
flow q3() -> U32 at sample {
  let g: U32 = fwd~(plus1~(prev~(^g, 7)))
  g at sample
}
```

- フレーム: 8
- 期待の出力: `1 8 2 9 3 10 4 11`
- 注: p1 with the init 7: the delay gives 7 at the first event and then the g of the event before: x = 0 7 1 8 2 9 3 10.

### q4

```onsa
flow q4() -> U32 at sample {
  let g: U32 = fwd~(plus1~(prev~(prev~(^g))))
  g at sample
}
```

- フレーム: 8
- 期待の出力: `1 1 1 2 2 2 3 3`
- 注: a delay in the first argument of a delay: the outer gives at each event the output of the inner at the event before, the g of two events before: x = 0 0 0 1 1 1 2 2.

### q5

```onsa
flow q5() -> U32 at sample {
  let a: U32 = plus1~(prev~(^b, 7))
  let b: U32 = fwd~(a)
  b at sample
}
```

- フレーム: 8
- 期待の出力: `1 8 2 9 3 10 4 11`
- 注: the delay is of the events of `b`, which is called after the call it is written in (the events of `a` come at each frame): the same values as q3.

### q6

```onsa
flow q6(m: U32 at event) -> U32 at sample {
  let y: U32 = plus1~(prev~(m, 9))
  y at sample
}
```

- フレーム: 8
- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',4) (3,'m',6) (6,'m',2)`
- 期待の出力: `1 10 10 5 5 5 7 7`
- 注: a delay of the events of an input, in the argument of a call that is read at `sample`: it gives 9 (its init), 4, 6 at the events, x is the last of them (0 before the first).

### q7

```onsa
flow q7(m: U32 at event) -> U32 at sample {
  let a: U32 = held_p~(m).when~((prev~(m, 1) at sample) == 1)
  a at sample
}
```

- フレーム: 8
- イベント（位置, 入力, 値。境界が渡す順）: `(1,'m',4) (3,'m',6) (6,'m',2)`
- 期待の出力: `0 5 5 5 5 5 5 5`
- 注: the delay of the events of an input in the condition of a `when~`: it gives 1 (its init), 4, 6 at the events, the condition (the last of them is 1) holds in the frames 1 and 2 (0 before the first event: false), and the part gives 4 + 1 = 5 there and holds it after.
