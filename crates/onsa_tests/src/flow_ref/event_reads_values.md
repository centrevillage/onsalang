# What a delay saves reads of the events where a condition with a `^name` chooses the place (W7-11 U2-e2; §11.3, S-1240, S-1244)

- The values are worked out by hand from the text of §11.3: "「`^名前` を読む」… その位置を選ぶ条件に `^名前` を書いたもの". What a condition chooses (the branches of an `if`, an arm after the guard that has the `^name`, the right side of `&&` / `||` whose left side has it)
  reads an event at the end of the stage, and the part of the condition that has no `^name` of its own (`p at sample` in `(p at sample) > ^k`) reads it where it is written, as a read that no `^name` chooses does.
- The input is `x` = 1 .. 9 and `y` = 1 (every sample). `gen` gives the event `x` when `x % 3 != 0` (the samples 0 1 3 4 6 7). `p = prev~(^d)` is the event before: after each sample (`PA`) 0 1 1 2 4 4 5 7 7, before the event of the sample (`PB`) 0 0 1 1 2 4 4 5 7.
  A delay gives what it stored at the sample before (0 at the first).

## 共通の部品

```onsa
flow gen(x: U32 at sample) -> U32 at event { if x % 3 != 0 { Some(x) } else { None } }
```

### r1

```onsa
flow r1(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(if (p at sample) > ^k { p at sample } else { x })
  let k = y
  let d = gen~(x)
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 1 2 3 4 4 4 5 7`
- 注: the condition is `PB > 1` (false for the first four samples, true after), the then side is `PA`, the else side is `x`: the stored values 1 2 3 4 4 4 5 7 7. A condition read at the end of the stage (`PA > 1`) would take `PA` = 2 at the sample 3.

### r2

```onsa
flow r2(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(if (p at sample) > ^k { x } else { p at sample })
  let k = y
  let d = gen~(x)
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 0 1 1 2 5 6 7 8`
- 注: the else side is chosen by the condition with `^k`, so it reads `PA`: stored 0 1 1 2 5 6 7 8 9.

### r3

```onsa
flow r3(x: U32 at sample, b: Bool at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(((p at sample) > 1) && ^k)
  let k = b
  let d = gen~(x)
  if q { 1 } else { 0 }
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `b`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 0 0 0 0 1 1 1 1`
- 注: the left side of `&&` has no `^name` (the `^k` is the right side): `p` is `PB`, `PB > 1` is false for four samples and true after.

### r4

```onsa
flow r4(x: U32 at sample, b: Bool at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(^k && ((p at sample) > 1))
  let k = b
  let d = gen~(x)
  if q { 1 } else { 0 }
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `b`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 0 0 0 1 1 1 1 1`
- 注: the right side is chosen by the left side that has `^k`, so it reads `PA`: `PA > 1` is false for three samples.

### r5

```onsa
flow r5(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(match x % 2 { 0 if ((p at sample) > 0) && (^k > 0) => p at sample, _ => x })
  let k = y
  let d = gen~(x)
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 1 2 3 2 5 4 7 7`
- 注: the guard of the arm of even `x` has `^k`: the `p` in the guard is `PB` (`PB > 0` is false at the sample 1, true at 3 5 7), the arm that it chooses reads `PA` (2 4 7). Stored 1 2 3 2 5 4 7 7 9.

### r6

```onsa
flow r6(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(match x % 3 { 0 if ^k > 5 => x, 1 if (p at sample) > 1 => p at sample, _ => x })
  let k = y
  let d = gen~(x)
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 1 2 3 2 5 6 5 8`
- 注: the guard of the second arm is chosen by the guard before it, which has `^k`, so the `p` in it reads `PA` (`PA > 1` is false at the sample 0, true at 3 and 6) and so does the body (2 and 5). Stored 1 2 3 2 5 6 5 8 9. A guard read where it is written (`PB > 1`) is false at the sample 3.
