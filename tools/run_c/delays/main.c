/* The bench `delays` of `compare.py run-c` (bench.h): noise through the reverb at the default parameters. */
#define PASSES 256u
#include "../bench.h"
#include "delays_delays.h"

static _Alignas(DELAYS_DELAYS_ALIGN) uint8_t mem[DELAYS_DELAYS_SIZE];
static delays_delays_params params;

static void setup(void) { bench_noise(777u); }

static int start(void) {
  delays_delays_params_default(&params);
  return delays_delays_init((delays_delays*)mem, NULL, RATE);
}

static int step(uint32_t at, uint32_t n) {
  return delays_delays_process((delays_delays*)mem, &params, bench_in + at, bench_out + at, n);
}
