/* R-133: 生成した C で NaN のビット表現を出す。手順は m.onsa の先頭のコメント。今の実装の API（S-92 の前、値を直接返す形）で書いてある。 */
#include "t_r133.h"
#include <stdio.h>
int main(void) {
  printf("nan=0x%08X neg_nan=0x%08X\n", (unsigned)t_nan_bits(0.0f), (unsigned)t_neg_nan_bits(0.0f));
  return 0;
}
