#include "t_p1.h"
#include <stdio.h>
#include <inttypes.h>
int main(void) {
  printf("narrow_u32(5) = %d (expect 5)\n", t_narrow_u32(5));
  printf("shr_i8(-128,1) = %d (expect -64)\n", t_shr_i8(-128, 1));
  printf("shr_i16(-32768,1) = %d (expect -16384)\n", t_shr_i16(-32768, 1));
  printf("wmul_u16(65535,65535) = %u (expect 1)\n", t_wmul_u16(65535, 65535));
  printf("wmul_i16(-32768,-32768) = %d (expect 0)\n", t_wmul_i16(-32768, -32768));
  printf("cmul_u32(max,max) = %u (expect 7)\n", t_cmul_u32(4294967295u, 4294967295u));
  printf("sat_i64(1e30) = %" PRId64 " (expect 9223372036854775807)\n", t_sat_i64(1e30));
  printf("sat_u64(1e30) = %" PRIu64 " (expect 18446744073709551615)\n", t_sat_u64(1e30));
  printf("order() = %u (expect 10)\n", t_order());
  printf("cast_order() = %" PRId64 " (expect 1)\n", t_cast_order());
  printf("trunc_order() = %d (expect 1)\n", t_trunc_order());
  printf("take_panic = %d\n", t_take_panic());
  return 0;
}
