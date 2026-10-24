## 17. 例

この節の例は、§2〜§16 の規則に対して手で検査してある。

### 17.1 純粋な計算

```onsa
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

### 17.2 効果・エラー・handler によるテスト

```onsa
use std.fs.{Fs, Path, IoError}
use std.text.{count_lines}

pub enum ConfigError: PartialEq + Eq + Show {
  Io(IoError),
  Empty,
}

pub fn line_count(path: Path) -> Result[U64, ConfigError] uses {Fs, Alloc} {
  let text = Fs.read(path).map_err(ConfigError.Io)?
  if text.len() == 0 {
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

`line_count` は `Fs.read` から受け取った `Str` を本体の終わりで破棄するので、`Alloc` を要する。

### 17.3 二極レゾネータ

モジュール `dsp`（ファイル `dsp.onsa`）に置く（§17.4 も同じモジュール）。

```onsa
use std.math.{exp, cos}
use std.dsp.test.{impulse, energy}

/// 二極レゾネータ。極は r·e^{±jw} にあり、bw > 0 なら |r| < 1 で安定。
/// 入力に (1 - r) を掛けて、ピークのゲインをおおよそ正規化する。
pub flow resonator(x: F32 at sample, fc: F32 at block, bw: F32 at block) -> F32 at sample {
  let r  = exp(-(F32.PI * bw) / sample_rate()) // block
  let w  = (2.0 * F32.PI * fc) / sample_rate() // block
  let b1 = 2.0 * r * cos(w)                    // block
  let b2 = r * r                               // block
  let y1 = prev~(^y)                           // sample: ^y は下で定義される y（帰還）
  let y2 = prev~(y1)                           // sample
  let y  = (1.0 - r) * x + b1 * y1 - b2 * y2   // sample: y[n] = g·x + b1·y[n-1] − r²·y[n-2]
  y
}

test "resonator decays" {
  let o = resonator.render(resonator.Params { fc: 500.0, bw: 100.0 },
                           impulse(48000), 48000.0)
  assert energy(o.out, 47000, 48000) < 1.0e-12
}
```

- 順序: `prev~(^y)` だけが前方の `y` を参照し、`^` の印で帰還と分かる。遅延を通るので合法（§11.2）。`prev~(y1)` は上で定義済みの `y1` の遅延なので、印は無い。
- レート: `r w b1 b2` は `block` のクロックなので、ブロックごとに 1 回だけ計算される。
- 演算子: 積和は括弧なしで書く（乗法は加法より強い、§3.1）。`-(F32.PI * bw)` は前置の `-` の被演算子なので括弧が要る。
- 状態: 遅延の状態は `y1` と `y2` の 2 つの F32。状態の全体は、他に `sample_rate`、`sample` から読まれる `block` の値（`b1`、`b2`）、巻き上げた部分式（`y.hoist_0` の `1.0 - r`）、`poisoned`、`initialized` を持つ（§12.4）。大きさはコンパイル時に決まり、`onsa interface` に出る（export すればヘッダの `<PREFIX>RESONATOR_SIZE` にも出る）。

### 17.4 声の flow

```onsa
// §17.3 と同じモジュール（resonator を参照する）
use std.math.{floor}

/// 素朴なのこぎり波（エイリアシングあり。例示用）
pub flow saw(f0: F32 at block) -> F32 at sample {
  let phase = wrap01(prev~(^phase) + f0 / sample_rate())
  2.0 * phase - 1.0
}

pub rt fn wrap01(x: F32) -> F32 {
  x - floor(x)
}

/// block の値を、時定数 time 秒の一次遅れでサンプルごとに滑らかにする
pub flow smooth(x: F32 at block, time: F32 at init) -> F32 at sample {
  let a = exp(-1.0 / (time * sample_rate())) // init: init で 1 回
  let y = x + a * (prev~(^y) - x)
  y
}

pub flow voice(
  @param(min: 20.0, max: 2000.0, default: 110.0, unit: "Hz", scale: "log")
  f0: F32 at block,
  @param(min: 200.0, max: 1200.0, default: 700.0, unit: "Hz")
  vowel_f1: F32 at block,
  @param(min: 600.0, max: 3000.0, default: 1220.0, unit: "Hz")
  vowel_f2: F32 at block,
  @param(min: 0.0, max: 1.0, default: 0.5)
  gain: F32 at block,
) -> F32 at sample {
  let src = saw~(f0)
  let f1  = resonator~(src, vowel_f1, 80.0) // 80.0: 定数から block へ昇格
  let f2  = resonator~(src, vowel_f2, 120.0)
  (f1 + f2) * smooth~(gain, 0.01)
}
```

flow の中で、`~` の付いた `saw` `resonator` `smooth` は状態を持つインスタンス、`wrap01` `exp` `floor` は状態を持たない関数である。呼び出しの形だけで区別できる。

遅延線を持つ例:

```onsa
const MAX_ECHO: U32 = 96000 // 48 kHz で 2 秒、96 kHz で 1 秒

pub flow echo(
  x: F32 at sample,
  @param(min: 0.01, max: 1.0, default: 0.3, unit: "s")
  time: F32 at block,
  @param(min: 0.0, max: 0.95, default: 0.5)
  feedback: F32 at block,
) -> F32 at sample {
  let d = time * sample_rate() // block（サンプル数）
  @mem(bulk) let line = vdelay~(^y, d, MAX_ECHO)
  let y = x + feedback * line
  y
}
```

`echo` の遅延線（約 384 KB）は `@mem(bulk)` を付けたので、`memory.bulk = true` のターゲットでは bulk 領域に入る。`VC_ECHO_BULK_SIZE` はコンパイル時に決まり、組込みでは外部 SDRAM に置ける。

ホスト側（Onsa で WAV に書き出す）:

```onsa
use std.fs.{Fs, Path, IoError}
use std.audio.wav

pub fn render_vowel(path: Path) -> Result[(), IoError] uses {Fs, Alloc} {
  let sr: F32       = 48000.0
  var st            = voice.init(sr)
  var out: Buf[F32] = Buf.zeroed(48000)
  let p             = voice.Params { f0: 110.0, vowel_f1: 700.0, vowel_f2: 1220.0, gain: 0.5 }
  voice.process(inout st, p, inout out)
  wav.write(path, out, sr)
}
```

`out` は `Buf` で、本体の終わりで破棄されるので `Alloc` が要る。`st` は固定サイズの値で、ヒープを使わない。パラメータは `@param` の `default` と同じ値をリテラルで書く（Onsa のコードは属性の値を読まない、§6.5）。

### 17.5 組込み: C のホストから使う

`daisy` ターゲット（ヒープ無し、§15.3）で `voice` を静的ライブラリにし、C のファームウェアから呼ぶ。

```c
#include "vc_voice.h"

static _Alignas(VC_VOICE_ALIGN) uint8_t voice_mem[VC_VOICE_SIZE];
static vc_voice* voice;
static vc_voice_params params;

void setup(void) {
  voice = (vc_voice*)voice_mem;
  if (vc_voice_init(voice, NULL, 48000.0f) != 0) {   /* BULK_SIZE が 0 なので NULL。init の入力が無いので cfg は取らない */
    return;                                          /* init が失敗した（1: panic、2: 引数の誤り）。使い始めない */
  }
  vc_voice_params_default(&params);
}

void audio_callback(const float* const* in, float* const* out, size_t frames) {
  vc_voice_process(voice, &params, out[0], (uint32_t)frames);
}

void onsa_reset_hook(void) {   /* panic = "reset"（§15.3）なので定義する。戻らない */
  NVIC_SystemReset();
}
```

ヒープもスタック上の大きな値も使わない。必要なメモリの量はヘッダの定数で分かり、リンク時に確定する。

### 17.6 DSP 以外のコード: ポリフォニー

FAUST ではボイスの割り当てを言語の外（アーキテクチャファイル）で書く。Onsa では同じ言語で書け、rt とヒープ不使用が検査される。

```onsa
use std.array
use std.math.{exp2}

const MAX_VOICES: U32 = 8

pub struct Poly {
  voices: [voice.State; MAX_VOICES],
  params: [voice.Params; MAX_VOICES],
  notes: [Option[U8]; MAX_VOICES],
  next: U32,
}

pub rt fn midi_to_hz(note: U8) -> F32 {
  440.0 * exp2(((note as F32) - 69.0) / 12.0)
}

impl Poly {
  pub fn new(sample_rate: F32) -> Poly {
    Poly {
      voices: array.from_fn(fn(_) { voice.init(sample_rate) }),
      params: [voice.Params { f0: 110.0, vowel_f1: 700.0, vowel_f2: 1220.0, gain: 0.5 }; MAX_VOICES],
      notes: [None; MAX_VOICES],
      next: 0,
    }
  }

  /// 空きを探さず、順番に割り当てる（最も古い発音を奪う）
  pub rt fn note_on(inout self, note: U8, velocity: F32) {
    let i = self.next
    self.notes[i] = Some(note)
    self.params[i].f0 = midi_to_hz(note)
    self.params[i].gain = velocity
    voice.reset(inout self.voices[i])
    self.next = (i + 1) % MAX_VOICES
  }

  pub rt fn note_off(inout self, note: U8) {
    for i in 0 ..< MAX_VOICES {
      if self.notes[i] == Some(note) {
        self.notes[i] = None
        self.params[i].gain = 0.0 // smooth により 10 ms で減衰する
      }
    }
  }

  pub rt fn process(inout self, inout out: Span[F32], inout scratch: Span[F32]) {
    out.fill!(0.0)
    for i in 0 ..< MAX_VOICES {
      voice.process(inout self.voices[i], self.params[i], inout scratch)
      out.add_from!(scratch)
    }
  }
}
```

- `Poly` は Onsa のプログラムの中で使う形である。struct と関数は export できないので、プラグインの入口にはならない（プラグインでは、ボイスの割り当てを入口の flow のイベントの段に書く。下の最後の項、§14.3）。
- `Poly.new` は効果を持たない。`Poly` は固定サイズの値で、その大きさは `onsa interface` に出る。
- `self.voices[i]`（`inout`）と `self.params[i]`（借用）は異なるフィールドなので重ならない（§5.2）。
- `array.from_fn` に渡す無名関数は `sample_rate` をコピーで捕捉する。引数の位置だけで使うので、ヒープを使わない（§5.3）。
- `voice` に `@mem(bulk)` の遅延線があるとき、`memory.bulk = true` のターゲットでは、この `Poly` の書き方はできない（E0819、§12.4）。ボイスの列を flow の `par` で書き、発音の割り当ては、その flow のイベントの入力（`midi.Message at event`、§11.11）の段で書く。
  ボイスごとの頭出しは、`voice.reset` を外から呼ぶ代わりに、ゲートの入力として `voice` の中で受けるか、`reset_if~`（§11.10）で書く。

---

