# Ori Language Specification (Draft 0.1)

Programs are reconstructable logical structure.
Surface prettiness is secondary. Decomposability, unique meaning, and machine-checkable feedback are primary.

Ori is a small language for humans to audit and for models to write.
It compiles; it is not a prompt.

---

## 0. Design thesis

From the preceding discussion:

1. Source (or IR) is not a human relic. It is the compact, checkable form of intent.
2. If an LLM writes the program, rhetorical readability may drop. Structural readability must not.
3. A language is LLM-suitable when errors are rejected *locally*, *quickly*, and *deterministically*.
4. Expression space must be narrow. C++ fails by permitting too many meanings for one intent.
5. Domain graphs (as in FAUST) are excellent *inside* a signal fragment, not as the whole language.
6. Point-free density is a specification virtue and a cognitive cost. Names are allowed at boundaries.

Non-goals: being a better Python; replacing LLVM; encoding all of Rust's aliasing story; being a golf language.

---

## 1. Layers

```
Intent  →  Ori surface  →  Ori Core (canonical IR)  →  LLVM / C / WASM / DSP graph
                ↑                    ↑
           human audit          fmt --check, types, effects
```

- **Surface**: one syntax, layout-insensitive.
- **Core**: typed lambda + ADTs + linear buffers + effect handlers. Byte-canonical after `ori fmt`.
- **Flow fragment**: synchronous single-rate signal graphs. Lowers into Core.

An Ori file is always Core plus optional Flow. There is no second language.

---

## 2. Surface syntax (one way)

Delimiters are explicit. Indentation is never semantic.
No operator precedence beyond applicative grouping. Infix exists only inside `flow` and only for five graph ops, always parenthesized when mixed.

```
mod filters

use std.{fs, test}

pub type Hz = Float

pub fn clamp(x, lo, hi) =
  if x < lo then lo
  else if x > hi then hi
  else x

pub fn load_text(path: Path) -> String / {fs.read} =
  fs.read(path)

type Either(a, b) = Left(a) | Right(b)

pub fn unwrap_or(e, d) = match e
  | Left(x)  -> x
  | Right(_) -> d
end
```

Rules:

- `fn`, `type`, `mod`, `use`, `pub`, `match`, `if`, `flow`, `effect`, `handler`, `test`.
- Definitions are `name(args) = body` or `name(args) -> T / {eff} = body`.
- Blocks close with `end` when they contain clauses (`match`, `handler`). Single-expression bodies need no `end`.
- Comments are `;;` to end of line. They are not part of Core.
- String interpolation is forbidden. Format through functions.

Forbidden on purpose: inheritance, implicit `this`, macros that invent binders, implicit numeric conversions, nullable types, exceptions as control flow, silent overloads.

---

## 3. Core calculus

A closed program is a module of:

- values
- functions
- algebraic data types
- effect signatures
- tests

Evaluation is deterministic given the same effect traces.
There is no unspecified behaviour in the safe fragment.

### 3.1 Values and types

```
τ ::= Unit | Bool | Int | Float | String | Path
    | τ × τ | List τ | Array τ
    | τ → σ / ε
    | T(τ…)
    | Sig n τ          ;; n-ary signal of sample type τ
    | Buf τ            ;; unique buffer
    | Cap e            ;; capability for effect e
```

- Algebraic data types, no hidden fields.
- Tuples are products. Records are nominal: `type Point = { x: Float, y: Float }`.
- `Option a = None | Some(a)`. No null.
- Generics are prenex. Inference is Hindley–Milner plus row-polymorphic effects.
- Annotations are required at *module boundaries* and *effectful signatures*. Local bindings infer.

### 3.2 Pattern matching

Match is exhaustive. The compiler rejects missing constructors.
No refutable `let`. Use `match`.

### 3.3 Mutation

Default is immutable.
Mutation exists only for:

- `Buf a` (unique, consumed on write unless `copy`)
- `Ref a` inside an explicit `mut` region, cannot escape the region

No shared mutable aliasing across functions without an effect (`mem`).

### 3.4 Control

```
if c then t else e
match e | p -> t | …
loop s = acc in body   ;; tail-recursive loop with named state
for x in xs do e end   ;; sugar over iterators; desugars to loop
```

One iteration story: iterators in libraries, `loop` in Core. No C-style `for`.

---

## 4. Effects and capabilities

Ambient I/O is banned.

```
effect fs {
  read  : Path -> String
  write : Path -> String -> Unit
}

effect audio {
  sample_rate : Float
}

fn save(p, s) -> Unit / {fs.write} =
  fs.write(p, s)

fn main(env: { fs: Cap fs }) / {fs.write} =
  save(Path("out.txt"), "ok")
```

- An effect row `{fs.write, net.get}` is part of the type.
- Calling an effect requires a capability in scope, or a handler.
- Purity is the empty row `{}`.
- Handlers are explicit and typed:

```
handler mock_fs =
  fs.read(_)  -> "stub"
  fs.write(_, _) -> ()
end
```

Tests inject handlers. Production `main` receives OS capabilities from the runtime once.

This is the reconstructability rule: *what the program may do is on the signature*.

---

## 5. Flow: signal graphs

FAUST's lesson: a DSP program *is* a graph of signals, and the compiler should check arity and lower to tight loops.
Ori keeps that fragment, but refuses global point-free style as the only style.

```
flow onepole(p: Float) : Sig 1 Float -> Sig 1 Float =
  rec (y -> add(in, mul(p, y)))

flow mix : Sig 2 Float -> Sig 1 Float =
  seq(par(id, id), add)

flow voice(f0: Sig 1 Float) : Sig 0 Float -> Sig 1 Float =
  let osc  = saw(f0)
      filt = onepole(0.8)
  in  seq(osc, filt)
```

Graph operators, only inside `flow`:

| op | meaning | type sketch |
|---|---|---|
| `seq(f,g)` | series | `(a→b, b→c) → a→c` |
| `par(f,g)` | parallel | `(a→b, c→d) → a+c → b+d` |
| `rec(h)` | feedback + 1-sample delay | `(n+k → n) → k → n` |
| `split(n)` | 1 to n | `1 → n` |
| `merge` | n to 1 by add | `n → 1` |

Infix aliases `:>`, `||`, `~` exist inside `flow` only, and mixed expressions must be parenthesized.
There is no precedence table to memorize.

Rules:

- Channel count is part of the type (`Sig n τ`). Mismatch is a type error, not a runtime surprise.
- `flow` bodies are total and allocating-free after compile. Recursion is only `rec`.
- Named `let` inside `flow` is encouraged. Point-free one-liners are legal for kernels ≤ a few nodes.
- Flow lowers to a Core function over `Buf Float` plus a clock capability `{audio}`.

This is FAUST's algebra without asking either human or model to hold five precedence levels and implicit wires in working memory.

---

## 6. Modules and stability

```
mod synth.voice
  pub type Param = { f0: Hz, gain: Float }
  pub fn render(p: Param) -> Buf Float / {audio}
end
```

- `pub` is the only visibility knob.
- A module's public types and signatures are its contract. `ori interface path` prints only that skeleton (for agents that must not ingest bodies).
- Imports are explicit. No glob except `use m.{a, b}`.
- There is no ADL, no implicit prelude beyond `Unit, Bool, Int, Float, Option, Result, List`.

Canonicalisation:

- `ori fmt` is deterministic.
- Core dumps use De Bruijn internally; surface always reprints stable names.
- Diffs are structural (`ori diff --ast`), not line-based as the source of truth.

---

## 7. Diagnostics (for the repair loop)

Every error has a stable code, a span, and a repair hint with a typed hole.

```
ORI-E0412 type mismatch
  at voice.ori:18:10
  expected: Sig 1 Float
  found:    Sig 2 Float
  hint: wrap with merge or change par to seq
  hole: ( _ : Sig 2 Float -> Sig 1 Float )(found)
```

Categories:

- `E00xx` syntax (unclosed `end`, bad token)
- `E04xx` types / arity
- `E05xx` exhaustiveness
- `E06xx` effects / missing capability
- `E07xx` uniqueness / buffer consumed twice
- `E08xx` flow causality / delay-free loop

The agent loop is: generate → `ori check --json` → patch holes → `ori test` → (optional) `ori play` for flow.

Compilation errors are the first oracle. Sound is the second, and only for `flow`.

---

## 8. Compilation and targets

```
.ori  →  type/effect check  →  Core
Core  →  LLVM            (native, embedded)
      →  WASM
      →  C subset        (for existing DSP hosts)
Flow  →  SDF graph       →  vectorised Core
```

Properties of generated code in the realtime subset (`ori build --rt`):

- no GC
- constant memory after init
- no exceptions
- no hidden allocations in the audio callback

General programs may use a runtime (lists, strings, handlers).
`main` of an `--rt` crate cannot import those.

Ori does not emit raw machine code as source. LLVM remains the deterministic lowering. That was the point of the first discussion.

---

## 9. Tests as part of meaning

```
test clamp_bounds =
  assert clamp(1.2, 0.0, 1.0) == 1.0

test onepole_dc / {audio} =
  let y = run_flow(onepole(0.5), [1.0, 0.0, 0.0, 0.0])
  in  assert abs(y[0] - 1.0) < 1e-9
```

A public function without a test is allowed but `ori lint --strict` fails the module in agent mode.
Tests are not comments. They are the executable clause of the specification.

For flow, the standard library provides `impulse`, `freqz` (magnitude at bins), `energy`, `is_stable`.

---

## 10. Worked examples

### 10.1 Pure logic

```
pub fn gcd(a, b) = loop s = (a, b) in
  match s
    | (x, 0) -> x
    | (x, y) -> continue (y, x % y)
  end
```

### 10.2 Effect boundary

```
pub fn phrase_len(path) -> Int / {fs.read} =
  let t = fs.read(path)
  in  count_mora(t)
```

The body can be replaced by an LLM. The row `{fs.read}` cannot drift silently.

### 10.3 Voice-shaped flow kernel

```
flow formant(fc: Float, bw: Float) : Sig 1 Float -> Sig 1 Float =
  ;; two-pole resonator, named stages
  let r    = exp(0.0 - pi * bw / sr)
      w    = 2.0 * pi * fc / sr
      b1   = 2.0 * r * cos(w)
      b2   = 0.0 - r * r
  in  rec (y1, y2 ->
        let y0 = add(in, sub(mul(b1, y1), mul(b2, y2)))
        in  y0 || y1
      )
```

A human audits poles and energy. A model may rewrite the body. The type `Sig 1 → Sig 1` and the `rec` delay are the structure that must survive.

---

## 11. What was rejected, and why

| Feature | Why rejected |
|---|---|
| Significant indentation | Closing a scope emits no token; repair loops mis-parent. |
| C++-style overload + ADL | Meaning is non-local. |
| Classical OOP inheritance | Intent lives in hidden vtables and lifetimes. |
| Raw `new` / shared pointers | Ownership leaves the type. |
| Macros that bind names | Agents and auditors cannot see the program. |
| Exceptions | Control edges vanish from signatures. |
| Global FAUST precedence | Human and model both drop wires. |
| Direct binary emission as source | Not a specification; not diffable; not portable. |
| Comment-as-spec | Not checkable. Tests and types are. |

| Feature | Why kept |
|---|---|
| HM inference | Types at edges, not on every line. |
| ADTs + exhaustiveness | Local, complete case analysis. |
| Effect rows + capabilities | Reconstructable world-interaction. |
| Unique buffers | Realtime without a borrow saga. |
| Flow algebra with named lets | FAUST's virtue, bounded cognitive load. |
| Canonical fmt + JSON diagnostics | Agent loop is part of the language. |
| Tiny prelude | One way to write each kernel. |

---

## 12. LLM / human division of labour

- **Model writes** function bodies, flow kernels, test vectors, refactors inside a module.
- **Compiler decides** types, exhaustiveness, effects, arity, uniqueness, causality.
- **Human decides** module cuts, effect allowances, numerical meaning (stability, formants, units), and whether the spec matches the research intent.
- **Never the model's alone**: capability grants, `--rt` subset, public interface changes.

The source remains the place where intent is pinned.
The binary remains an artifact of LLVM.

---

## 13. Status of this draft

This is a language *design*, not an implementation.
A minimal path to a usable kernel:

1. Parser + Core + checker (`ori check --json`)
2. Interpreter for tests
3. Flow arity + `rec` lowering
4. LLVM backend for `--rt` callbacks
5. `ori interface` and structural diff

Until those exist, Ori is a constraint on how to write in existing hosts (typed ML subset + FAUST-like graphs + explicit effects in comments-as-headers). The spec is the target, not a claim that the compiler already runs.
