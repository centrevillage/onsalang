/* R-121: 既定の prefix（onsa_）で作った二つのパッケージ `pa` と `pb` を、一つのホストから使う。
 *
 * 手順（リポジトリのルートで。生成物はコミットしない）:
 *   onsa build --target host tests/review-phase1/parent/r121/pa
 *   onsa build --target host tests/review-phase1/parent/r121/pb
 *   cc -std=c11 -c tests/review-phase1/parent/r121/host.c \
 *      -Itests/review-phase1/parent/r121/pa/target/host -Itests/review-phase1/parent/r121/pb/target/host -o host.o
 *   cc host.o tests/review-phase1/parent/r121/pa/target/host/libonsa_pa.a \
 *      tests/review-phase1/parent/r121/pb/target/host/libonsa_pb.a -o host && ./host
 *
 * 期待（S-95）: `prefix` が無いので、`pa` も `pb` もマニフェストの誤りになる（既定の prefix は無い）。`prefix = "pa_"` と `"pb_"` を書けば、
 *   名前（`pa_version` と `pb_version`）もファイル（`pa_pa.h` と `pb_pb.h`）も重ならず、ホストは両方を呼べる（`#include "pa_pa.h"` などに書き換える）。
 *   各パッケージのヘッダは `onsa.h` を取り込んだ直後に `ONSA_ABI_VERSION` を確かめ、違う版を前提にしたヘッダは `#error` で止まる。
 *
 * 今（2026-10-05）: コンパイルもリンクも警告なしに通り、`pa=1 pb=1` と出る。`onsa_version` は両方のライブラリにあり、
 *   静的リンクは先に見つけた `libonsa_pa.a` の定義を使う（`pb` の定義は黙って捨てられる）。flow のヘッダも
 *   両方が `onsa_gain.h` でガードは `ONSA_GAIN_H` なので、後のものは読まれない。`onsa.h` のガードは `ONSA_H` だけで版を持たず、
 *   二つのパッケージが違う版の `onsa.h`（S-87 で `onsa_param_info` の配置が変わった）を前提にしても、先に読んだ方が黙って使われる。
 *   ここでは関数を `onsa_version` の一つの名前でしか呼べないので、`pb` の関数を呼ぶ手段が無い。
 */
#include "onsa_pa.h"
#include "onsa_pb.h"
#include <stdio.h>

int main(void) {
  printf("pa=%u pb=%u\n", (unsigned)onsa_version(), (unsigned)onsa_version());
  return 0;
}
