## 14. FFI

### 14.1 C 関数の呼び出し

```onsa
extern "C" lib "fastconv" {
  type FcRaw // 不透明型
  fn fc_new(ir: Span[F32], block: U32) -> Ptr[FcRaw] uses {Alloc}
  rt fn fc_process(h: Ptr[FcRaw], input: Span[F32], inout output: Span[F32])
  fn fc_free(h: Ptr[FcRaw]) uses {Alloc}
}
```

- extern ブロックの中の `type 名前`（`=` なし）は不透明型の宣言。
- extern 宣言の **効果行と `rt` は検証されない主張**。C 側がヒープを使うなら `uses {Alloc}`、ブロックするなら `uses {Block}` と宣言する。`onsa audit` が一覧にし、ポリシー（§15.4）で許可されたパッケージにしか書けない。
- `unsafe` を必要としない引数型は、スカラ、`CSize`、`@repr(c)` 構造体、`Span[T]`（ポインタ + 長さとして渡し、呼び出し中だけ有効）、借用した `Str`（読み取り専用）。
- `CSize` は C の `size_t` で、extern の宣言の中でだけ使える。Onsa 側では `U32` として見え、`U32` に収まらない値が返ると panic する。
- `Ptr[T]` を引数や返り値に含む extern 関数は、`unsafe { }` の中でしか呼べない。

安全なラッパの例:

```onsa
pub struct Conv {
  h: Ptr[FcRaw],
}

impl Drop for Conv {
  fn drop(move self) uses {Alloc} {
    unsafe { fc_free(self.h) }
  }
}

impl Conv {
  pub fn new(ir: Span[F32], block: U32) -> Conv uses {Alloc} {
    Conv { h: unsafe { fc_new(ir, block) } }
  }

  pub rt fn process(inout self, input: Span[F32], inout output: Span[F32]) {
    unsafe { fc_process(self.h, input, inout output) }
  }
}
```

`Conv` の破棄は `Alloc` を要し、rt でない。したがって `rt` 関数の中では `inout` でしか扱えず、解放は必ず非 rt の文脈で起こる。

### 14.2 export

関数と flow は、ソースではなくマニフェストの `[export]`（§15.3）で C の ABI に出す。export する場所を一つにし、エージェントに書き込み権限を与えないファイル（§15.4）で管理するためである。ソースに export の印は無い。

```onsa
// util.onsa
pub fn version() -> U32 { 2 }
```

```toml
[export]
prefix = "vc_"
fns = ["util.version"]
```

export される flow と関数は `pub` で（でなければ E0303）、関数の引数と返り値は FFI で `unsafe` を要しない型（§14.1）に限る。効果行は、そのターゲットの `provides` にある効果しか持てない（E0610）。ヘッダはパッケージに 1 つで、名前は `<prefix><package>.h`。export する全ての flow と関数を宣言する。
次はパッケージ `voice`（§15.3、`prefix = "vc_"`）の例で、`voice` は §17.4 の flow、数値は例である。

```c
/* vc_voice.h（onsa build が生成する） */
#ifndef VC_VOICE_H
#define VC_VOICE_H
#include "onsa.h"                 /* onsa_param_info などの共通定義 */
#if ONSA_ABI_VERSION != 1
#error "vc_voice.h needs ONSA_ABI_VERSION 1"
#endif
#ifdef __cplusplus
extern "C" {
#endif

#define VC_VOICE_SIZE       48      /* fast 領域のバイト数 */
#define VC_VOICE_BULK_SIZE  0       /* bulk 領域のバイト数 */
#define VC_VOICE_ALIGN      4       /* fast 領域の整列 */
#define VC_VOICE_BULK_ALIGN 1       /* bulk 領域の整列（BULK_SIZE が 0 なら 1） */
#define VC_VOICE_PARAM_COUNT 4      /* @param の数（vc_voice_param_info の長さ） */

typedef struct vc_voice vc_voice;
typedef struct { float f0; float vowel_f1; float vowel_f2; float gain; } vc_voice_params;
typedef struct { uint8_t _unused; } vc_voice_config;   /* Config が空なので予約のメンバだけ */

/* bulk は BULK_SIZE が 0 なら NULL でよい。cfg は Config が空なら NULL でよい */
int  vc_voice_init(vc_voice* s, void* bulk, const vc_voice_config* cfg, float sample_rate);
     /* 0: ok, 1: init が panic した, 2: 要るのに bulk か cfg が NULL。1 と 2 では状態は未初期化のまま（reset では復帰せず、init のやり直しが要る） */
void vc_voice_reset(vc_voice* s);
void vc_voice_params_default(vc_voice_params* params);
int  vc_voice_process(vc_voice* s, const vc_voice_params* params,
                      float* output, uint32_t frames);
     /* 0: ok, 1: poisoned か未初期化, 2: 許されない重なり（in-place の対でない重なり）。0 以外なら出力は全て 0。frames は U32（§4.1） */

extern const onsa_param_info vc_voice_param_info[];    /* @param のメタデータ。Params のフィールドの順。長さは VC_VOICE_PARAM_COUNT */
int vc_voice_param_index(uint32_t number);   /* 数値の ID（§11.7）から上の表の添字。無ければ -1 */

/* Alloc を提供するターゲットだけで生成される */
vc_voice* vc_voice_new(const vc_voice_config* cfg, float sample_rate);   /* 状態と bulk の領域を確保して init を呼ぶ。失敗したら NULL */
void      vc_voice_free(vc_voice* s);        /* 状態と bulk の領域を解放する */

/* dsp.echo（§17.4）も同じ形で VC_ECHO_SIZE、vc_echo_init などを宣言する（ここでは省略） */

/* export した関数（[export] の fns） */
int vc_version(uint32_t* out);   /* 0: ok, 1: panic。結果は out に書く */

#ifdef __cplusplus
}
#endif
#endif
```

- メモリは呼び出し側が用意する。`_new` / `_free` は、ヒープのあるターゲットでの便宜にすぎない。`SIZE` と `ALIGN`（bulk 領域は `BULK_SIZE` と `BULK_ALIGN`）を満たす記憶域なら、何でも状態に使える（静的な `uint8_t` の配列、リンカの節、`malloc`）。生成したコードは状態を別名を許す型で読み書きするので（§13.4）、`uint8_t` の配列として宣言した記憶域を状態に使っても、C の実効型の規則に反しない。
- export した関数は状態の `int`（0: ok、1: panic）を返し、返り値は最後の引数の出力ポインタに書く（`int vc_version(uint32_t* out)`。返り値の無い関数は状態だけを返す）。形はターゲットの `panic` 設定に依らない（`"trap"` などでは panic した呼び出しは戻らないので、常に 0 を返す）。
  `init` / `process` の状態の値と同じ考え方で、結果を出力ポインタで受け取るのは §12.7 の集成体の返り値と同じ形である。引数は §14.1 と同じ対応で、スカラは値、`inout` のスカラは `T*`、`Span[T]` は `const T* name, uint32_t name_len`（`inout` なら `T*`）になる。
  この版で export の引数と返り値に使えるのは、スカラとスカラの `Span` だけである（`@repr(c)` の構造体、借用した `Str`、集成体の返り値は E0200）。
- `init` の中の panic（`panic = "poison"` のとき）は `init` を中断して 1 を返し、状態をゼロで埋めて未初期化の印を付ける。未初期化のインスタンスに対する `process` は、出力を全て 0 で埋めて 1 を返し（poisoned のときと同じ、§9.2）、`reset` は何もしない。復帰は `init` のやり直しだけである。
  `reset` は `void` を返す。保存した `init` の値を戻すだけで panic しないので、知らせることが無い（未初期化のインスタンスに何もしなかったことは、次の `process` が 1 を返して知らせる）。
- `process` の入出力の引数は §11.6 と同じく数で形が決まり、名前は `input` / `output`。
  単一の `Span` はポインタ（`const T*` / `T*`）、`[Span[T]; N]` はポインタの配列、`In` / `Out` は `<prefix><name>_in` / `<prefix><name>_out`（各フィールドがポインタの struct）へのポインタになる。
  例: `vc_swap_process(s, &params, &(vc_swap_in){ inl, inr }, &(vc_swap_out){ outl, outr }, frames)`。
- 入力と出力のバッファは、入力と出力の組ごとに、要素の型が同じなら、完全に同じポインタ（in-place 処理）であってよい。意味は `process_inplace`（§11.6）と同じである。
  型の違う入力と出力の同じポインタ（`F32` の入力と `F64` や `I32` の出力。大きさが同じでも、C では違う型として読み書きするので許さない）、部分的な重なり（出力どうしを含む）、および二つの出力が同じポインタの場合は検出して 2 を返す。入力どうしは読むだけなので、重なってもよい。poisoned か未初期化のインスタンスは、重なりがあっても 1 を返す（判定は 1 が先）。
  2 を返す呼び出しも、全ての出力（全てのチャンネルと全てのフレーム。他の出力や入力と重なる所も含む）を 0 で埋め、状態を進めず、poisoned にせず、どの段も評価しない（1 の呼び出しと同じく、0 以外を返した `process` の出力は全て 0。出力に書き込まないと落ちるホストがあるためでもある）。
- `process` の入出力の各ポインタは、`frames` 個以上の要素を指していなければならない。これはホストの責務で、生成したコードは検査しない（C のポインタは長さを持たない）。全てのチャンネルが一つの `frames` を使うので、§11.6 の長さの不一致は C の境界では起こらない。
- `frames` が 0 の `process` は正しい呼び出しで、`block` の段だけを評価する（§11.6。poisoned か未初期化のインスタンスは、他の呼び出しと同じく評価せずに 1 を返す）。入出力のポインタ（`In` / `Out` の構造体へのポインタを含む）は読まないので NULL でよく、重なりの検査もしない（0 サンプルのバッファや 0 チャンネルのバスを渡すホストがある）。`s` と `params` は要る（`block` の段が読む）。
- C の名前は `prefix` と名前の最後の要素をつなげたもの（`dsp.voice` は `vc_voice`、`util.version` は `vc_version`）。export する flow は、その C の名前 `<p>`（大文字は `<P>`）を頭にした次の名前を生成する。これで全てである（閉じた一覧）。

| 種類 | 名前 | 意味 |
|---|---|---|
| 型 | `<p>` | 状態。中身は公開しない |
| | `<p>_params`、`<p>_config` | `block` の入力と `init` の入力。空なら予約のメンバ `uint8_t _unused` を一つだけ持つ（ISO C は空の構造体を書けないため。利用者のフィールドが無いときだけ置くので、名前は重ならない） |
| | `<p>_in`、`<p>_out` | `sample` の入力・出力が 2 つ以上のとき（§11.6） |
| 関数 | `<p>_init`、`<p>_reset`、`<p>_process`、`<p>_params_default`、`<p>_param_index` | 常に生成する |
| | `<p>_new`、`<p>_free` | `Alloc` を `provides` するターゲットだけ |
| データ | `<p>_param_info` | `@param` のメタデータ。長さを書かない配列として宣言し、長さは `<P>_PARAM_COUNT` |
| マクロ | `<P>_SIZE`、`<P>_ALIGN`、`<P>_BULK_SIZE`、`<P>_BULK_ALIGN`、`<P>_PARAM_COUNT` | 配置と `@param` の数（§12.4、§11.7） |

パッケージのヘッダは、インクルードガードに `<PREFIX><PACKAGE>_H` を使う。パッケージの中で、この表から作る全ての名前、export した関数の名前、インクルードガードのどれかが重なると、ビルドで E1011（両方の出どころを示す）。
別のモジュールの同名の flow や関数、flow どうしの生成する名前（flow `voice` の `vc_voice_params` と flow `voice_params` の `vc_voice_params`）、flow の生成する名前と関数の名前（flow `voice` の `vc_voice_init` と関数 `voice_init`）の重なりも含む。
- 関数と型の形は、flow の宣言にもターゲットにもよらず一定で、変わるのはフィールドと定数の値だけである（`process` の入出力の引数は §11.6 の数の規則に従う）。共通のラッパーを、どの flow にも同じ形で書ける。
  `block` の入力が無い flow でも `_params`、`_params_default`（何もしない）、`_param_index`（常に -1）、`_param_info`（長さ 0）を生成し、`_process` は `params` を取る。`init` の入力が無い flow でも `_config` を生成し、`_init` と `_new` は `cfg` を取る。
  `bulk` の引数は、ターゲットの設定によらず常に置く。
- Config は `const <p>_config* cfg` で受け取る（`params` と同じ形。ホストはフィールドを名前で設定するので、引数の取り違えが起きない）。Config が空なら NULL を渡してよく、`BULK_SIZE` が 0 なら `bulk` に NULL を渡してよい。
  どちらも、要るのに NULL なら `_init` は 2 を返し、状態をゼロで埋めて未初期化の印を付ける（`_new` は NULL を返す）。2 は `_process` の 2 と同じく呼び出し側の引数の誤りで、`init` の中の panic（1）と区別できる。
  Config にフィールドを足すと、構造体を組み立てるホストのコードはそのまま通り、新しいフィールドは 0 になるので、ホストのコードを見直す。
- `_new` は状態と bulk の領域（`<P>_BULK_ALIGN` に揃える）を確保して `_init` を呼び、`_free` は両方を解放する。`BULK_SIZE` が 0 なら `BULK_ALIGN` は 1 である。
- `prefix` は、`[export]` に flow か関数があれば必須で、既定は無い（書かなければ E1104 で、`<package>_` が下の規則を満たすときは、修正候補は `prefix = "<package>_"` の挿入）。C の名前は、ホストが依存した後は変えられない公開の ABI なので、export を決める場所で選ぶ。別々にビルドしたパッケージを一つのバイナリにリンクするとき、名前の重なりは `prefix` を変えて避ける（パッケージ名を変える必要は無い）。
- `prefix` の値は、小文字の英字・数字・`_` からなり、英字で始まって `_` で終わる（`vc_`、`my_synth_`）。空は書けない（C の名前が libc や他のライブラリの名前と重なり、ヘッダの名前が `onsa.h` や標準のヘッダを隠す）。`__` を含むもの（C++ では予約の名前）と、`onsa_` で始まるものも書けない。いずれも E1103 である。
- ランタイムは `onsa_` と `ONSA_` で始まる名前を全て持つ（公開の名前は `onsa.h` の型と列挙子、`ONSA_ABI_VERSION`、下の表。内部の記号は `onsa__` / `ONSA__` で始まる）。`prefix` は `onsa_` で始まれないので、生成する名前とランタイムの名前は重ならない。ランタイムに名前を足しても、既存のパッケージの名前とは重ならない。
- 生成するファイルの名前は `<prefix><package>` を幹にする: ヘッダ `<prefix><package>.h`、C のソース `<prefix><package>.c`、静的ライブラリ `lib<prefix><package>.a`。ランタイムのヘッダは固定の名前 `onsa.h` と `onsa__runtime.h` で、`prefix` の規則からパッケージのファイルとは重ならない。
- 公開ヘッダ（`onsa.h` と `<prefix><package>.h`）は、C99 以降と C++11 以降の両方から、`-pedantic` でも警告なしに取り込める。宣言は `extern "C"` で囲む。`onsa.h` に入るのは、ホストが使う型（`onsa_param_info` など）と、ホストやファームウェアが用意する関数の宣言だけである。
  生成したコードのための内部のランタイム（補助関数、`setjmp`、`FLT_EVAL_METHOD` の検査、C11 の構文）は `onsa__runtime.h` に分け、生成した `.c` だけが取り込む（`kind = "source"` では出力するが、ホストは取り込まない）。
  生成した `.c` は C11 を要求し、C の翻訳単位としてコンパイルする（C++ のコンパイラで C++ として読むことは対象外）。C++ から使うときは、公開ヘッダだけを取り込む。
  内部の名前（`dsp__voice__State`、状態のフィールドの `a__prev_0`）は C の規則で選び、`__` を含む（C は `__` で始まる名前だけを予約し、C++ は `__` を含む名前を全て予約する）。状態の型は公開ヘッダでは中身の見えない型なので、これらの名前は公開ヘッダに現れない。
- `onsa.h` の中身は、パッケージやターゲットの設定に依らない。`onsa.h` は ABI の版 `ONSA_ABI_VERSION`（整数。この版では 1）を定義し、パッケージのヘッダは `onsa.h` を取り込んだ直後に版を確かめて、違えば `#error` で止める。
  インクルードガードが同じなので一つの C ファイルには一つの `onsa.h` しか読まれず、違う版を前提にしたパッケージのヘッダを一緒に取り込むと、型の配置が黙って食い違うからである。版は、`onsa.h` の共有の部分（型、列挙子、下の表のフックとマクロの名前と形）を互換でなく変えたときに上げ、コンパイラの版とは結び付けない。
  ホストは `ONSA_ABI_VERSION` を読んで版ごとに書き分けられる。パッケージのヘッダと、別のビルドで作ったライブラリの組み合わせは検査しない（ヘッダとライブラリは一緒に生成される）。
- `onsa_param_info`（`onsa.h`）の値の欄は、入力の型（§11.7）で形が変わる。真偽を `1.0` / `0.0` のような数で表さない。

```c
typedef enum onsa_param_kind {
  ONSA_PARAM_F32, ONSA_PARAM_F64, ONSA_PARAM_I8, ONSA_PARAM_I16, ONSA_PARAM_I32,
  ONSA_PARAM_U8, ONSA_PARAM_U16, ONSA_PARAM_U32, ONSA_PARAM_BOOL
} onsa_param_kind;
typedef enum onsa_param_scale { ONSA_PARAM_LINEAR, ONSA_PARAM_LOG } onsa_param_scale;
typedef struct onsa_param_info {
  const char* name;
  const char* id;
  uint32_t number;     /* 数値の ID（§11.7）。ホストとプラグインのラッパーが使う */
  const char* unit;    /* 無ければ "" */
  const char* label;   /* 無ければ "" */
  onsa_param_kind kind;
  union {
    struct { double  min, max, def, step; onsa_param_scale scale; } f;  /* F32, F64 */
    struct { int64_t min, max, def, step; onsa_param_scale scale; } i;  /* 整数 */
    struct { bool def; } b;                                             /* Bool */
  } v;
} onsa_param_info;
```

- `double` と `int64_t` は、§11.7 の全ての型の値を正確に表す。書かれていない `min` / `max` / `step` は、制約が無いことを表す値で埋める（浮動小数は `-INFINITY` / `INFINITY` / `0`、整数は型の範囲の両端と `1`）。`@param` の値は有限で `step > 0` なので、書かれていないことも見分けられる。
- ホストやファームウェアが定義するマクロと関数は、次の表で全てである。

| 名前 | 定義する者 | 意味 |
|---|---|---|
| `void onsa_reset_hook(void)` | ファームウェア（`panic = "reset"` のとき） | 機器をリセットする。戻らない。名前は `prefix` に依らない |
| `ONSA_PANIC_HANDLER` | ホスト（任意） | 関数の名前を定義すると、panic のときに、ホストの浮動小数の状態に戻した上で（§15.5）`(const char* msg, const char* file, uint32_t line)` で呼ばれ、その後で `panic` 設定の動作をする。`panic_messages = false` では `msg` と `file` は空の文字列（NULL ではない） |
| `ONSA_NO_TLS` | `onsa build`（OS の無いプラットフォーム）、利用者（`kind = "source"` を自分でコンパイルするとき） | panic の飛び先をスレッドごとの記憶域ではなく静的な変数に置く。一つのパッケージの export の wrapper が並行に動かないことが前提 |
| `ONSA_FP_CONTRACT_OFF`、`ONSA_ALLOW_INEXACT_FP` | 利用者 | 浮動小数のビルドの検査（§13.4） |

- export した flow を、既存の C/C++ ホスト（JUCE, CLAP, VST3, AU, 組込み HAL）へ組み込む第一の経路とする。組込みでの使い方は §17.5。

---

