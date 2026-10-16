## 16. 実行文脈

Onsa は **スレッドを作らない**。プログラムが走る文脈（オーディオコールバック、メインループ、割り込み、AudioWorklet、プラグインの GUI スレッド）はターゲットが与える。Onsa はそれぞれの文脈で呼ばれる関数を書き、文脈の間はロックフリーの同期型で値を受け渡す。

- 文脈が並列に走るか（デスクトップ、2 コアのマイコン）、割り込みで割り込むか（マイコン）、直列化されるか（協調スケジューラ、JavaScript）はターゲットの事情で、ソースの意味は変わらない。言語は並列性も、ブロックする合流も約束しない。
- データ競合は型で排除する。文脈の間を渡れるのは、同期型の要素としての Copy 値と、登録時に `move` した Affine 値だけである。Shared 値は渡らない（§12.6）。

### 16.1 文脈の登録

ターゲットは `target` 宣言（§15.2）で文脈を提供する。登録は「状態を `move`、同期型を `inout`、捕捉の無い関数を `move` で渡す」呼び出しで、**その呼び出しはプログラムが終わるまで戻らない**。

```onsa
use std.audio.device
use std.sync.{Swap}

pub fn main() -> Result[(), device.Error] {
  let st     = voice.init(voice.Config {}, 48000.0)
  var params = Swap.new(voice.params_default()) // 固定サイズの値。main のフレームに置かれる
  device.run(move st, inout params, move on_audio, move on_control)
}

rt fn on_audio(inout st: voice.State, params: Swap[voice.Params], inout out: Span[F32]) {
  voice.process(inout st, params.latest(), inout out)
}

fn on_control(inout params: Swap[voice.Params], ev: device.Event) {
  params.publish!(next_params(ev))
}
```

```onsa
// std.audio.device の登録関数の形（実装はターゲットの bind が与える）
target fn run[S: ?Dup, P: Copy](
  move st: S,
  inout params: Swap[P],
  move audio: rt fn(inout S, Swap[P], inout Span[F32]),
  move control: fn(inout Swap[P], Event),
) -> Result[(), Error]
```

- `audio` と `control` は `move` の関数型の引数なので、捕捉を持たない関数値（名前付き関数か、捕捉しない無名関数）だけを受ける（§5.2）。`run` は関数を文脈に登録して持ち続けるからである。状態は `move` で文脈へ渡り、登録した後はその文脈にしか無い（Affine）。
- `run` が戻らないので、`inout params` の借用は呼び出しの中に収まる。参照は第二級のまま（§5.3）で、ライフタイムは要らない。同じ同期型を二つの文脈に渡すのは `run` だけで、文脈の中からの同時アクセスは同期型のメソッドが原子的に扱う。
- 同期型は固定サイズの値なので、`main` のフレーム（`main_frame = "static"`、§12.5）や struct のフィールドに置ける。ヒープは要らない。
- プラグイン（`clap` / `vst3` / `au`）と `staticlib` では `main` が無く、状態と同期型はホストが持つ。C API（§14.2）はそのまま使う。
- 割り込みとメインループを持つファームウェアも同じ形で、`target` モジュールが「オーディオ割り込み」と「メインループ」の二つの文脈を提供する。

### 16.2 同期型（`std.sync`）

| 型 | 内容 | rt で使える操作 |
|---|---|---|
| `Spsc[T: Copy, const N: U32]` | 単一生産者・単一消費者の lock-free キュー（容量固定） | `push!`, `pop!` |
| `Atomic[T: Copy]` | 大きさはターゲットが lock-free で扱える幅まで（超えるとビルド時に E0650） | `load`, `store!`, `swap!` |
| `Swap[T: Copy]` | トリプルバッファで最新値を受け渡す | `latest`（受け側）。`publish!` は送り側（非 rt でも rt でもよい） |

- どれも Affine の固定サイズの値（`Swap[T]` は `[T; 3]` と原子的な添字、`Spsc[T, N]` は `[T; N]` と二つの添字）。生成（`Swap.new(init)` など）は `Alloc` を要しない。
- 要素は Copy に限る。Affine 値や Shared 値を文脈の間で受け渡す仕組みは無い（§19.1 のターゲット提供の後回しの仕事を参照）。

async / await と、Onsa からのスレッドやタスクの生成は無い（§19.2）。

---

