#include "t_boom.h"
#include "t_gainq.h"
#include <stdio.h>
int main(void) {
  static unsigned char mem[T_BOOM_SIZE] __attribute__((aligned(T_BOOM_ALIGN)));
  t_boom* s = (t_boom*)mem;
  t_boom_params p;
  float buf[8];
  t_boom_init(s, NULL, 48000.0f);
  p.k = 1e10f;
  for (int i = 0; i < 8; i++) buf[i] = 0.5f;
  printf("panic call: rc=%d buf[3]=%g\n", t_boom_process(s, &p, buf, buf, 8), buf[3]);
  p.k = 2.0f;
  for (int i = 0; i < 8; i++) buf[i] = 0.5f;   /* next block of input, in place */
  printf("poisoned call (in-place): rc=%d buf[3]=%g (spec §9.2: silence expected)\n", t_boom_process(s, &p, buf, buf, 8), buf[3]);
  float in[8], out[8];
  for (int i = 0; i < 8; i++) { in[i] = 0.5f; out[i] = 123.0f; }
  printf("poisoned call (separate): rc=%d out[3]=%g\n", t_boom_process(s, &p, in, out, 8), out[3]);

  static unsigned char gmem[T_GAINQ_SIZE] __attribute__((aligned(T_GAINQ_ALIGN)));
  t_gainq* g = (t_gainq*)gmem;
  t_gainq_params gp; gp.q = 100;
  t_gainq_init(g, NULL, 48000.0f);
  t_gainq_process(g, &gp, in, out, 8);
  printf("gainq q=100 (max 4): out[0]=%g (expect 2 if clamped)\n", out[0]);
  return 0;
}
