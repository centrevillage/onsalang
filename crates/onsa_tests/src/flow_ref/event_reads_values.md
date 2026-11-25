# What a delay saves reads of the events, whatever condition chooses the place (W7-11 U2-t3/e3; §11.3, S-1240, S-1244, S-1249)

- The values are worked out by hand from the text of §11.3 (S-1249): the event that a stored expression reads (the name of an event, the output of a call, a part of an event clock) is the value at the place where the read is written, except a `^name` and a part that has one, which are the value at the end of the stage.
  This holds in a branch, a guard, the right side of `&&` / `||` and an arm, whatever the condition that chooses it reads: `^k` in a condition changes where the part is evaluated (S-1244), never when the `p` in it is read (`p` has no `^`).
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
- 期待の出力: `0 1 2 3 4 2 4 4 5`
- 注: the condition is `PB > 1` (false for the first four samples, true after), the then side is `p` where it is written, `PB` (not `PA`, the `^k` of the condition does not move it): the stored values 1 2 3 4 2 4 4 5 7. A then side read at the end of the stage would give 1 2 3 4 4 4 5 7 7.

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
- 期待の出力: `0 0 0 1 1 5 6 7 8`
- 注: the else side reads `PB` where it is written, the same as the condition: stored 0 0 1 1 5 6 7 8 9. (At the end of the stage it would be 0 1 1 2 5 6 7 8 9.)

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
- 期待の出力: `0 0 0 0 0 1 1 1 1`
- 注: the right side reads `PB` where it is written, as the right side of r3 does, though it is chosen by a left side that has `^k`: `PB > 1` is false for four samples (at the end of the stage `PA > 1` would be false for three).

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
- 期待の出力: `0 1 2 3 1 5 4 7 5`
- 注: the guard of the arm of even `x` has `^k`: the `p` in the guard is `PB` (`PB > 0` is false at the sample 1, true at 3 5 7), and the arm that it chooses reads `PB` too (1 4 5; at the end of the stage 2 4 7). Stored 1 2 3 1 5 4 7 5 9.

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
- 期待の出力: `0 1 2 3 4 5 6 4 8`
- 注: the guard of the second arm is chosen by the guard before it, which has `^k`, and its `p` is `PB` as the body's is: `PB > 1` is false at the samples 0 and 3, true at 6, where the body gives `PB` = 4. Stored 1 2 3 4 5 6 4 8 9. (At the end of the stage `PA > 1` would be true at the sample 3 too.)

### r7

```onsa
flow r7(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(^t)
  let k = y
  let d = gen~(x)
  let t = if k > 0 { p at sample } else { x }
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 0 1 1 2 4 4 5 7`
- 注: the control of r1 .. r6: the `let t` is below the producer and read as `^t`, so it is the value of the end of the stage, `PA` (0 1 1 2 4 4 5 7 7), stored and given one sample later.

### r8

```onsa
flow r8(x: U32 at sample, y: U32 at sample) -> U32 at sample {
  let p = prev~(^d)
  let q = prev~(if ^k > 0 { ^t } else { x })
  let k = y
  let d = gen~(x)
  let t = p at sample
  q
}
```

- 入力 `x`: `1 2 3 4 5 6 7 8 9`
- 入力 `y`: `1 1 1 1 1 1 1 1 1`
- フレーム: 9
- 期待の出力: `0 0 1 1 2 4 4 5 7`
- 注: a `^t` in the branch that `^k` chooses is the end of the stage (`PA`, the `let t` below the producer reads `p` after the event), as a `^name` is wherever it is written; with the branch `p at sample` of r1 it is `PB`.
