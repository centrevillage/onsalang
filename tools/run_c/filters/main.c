/* The bench `filters` of `compare.py run-c` (bench.h): noise through the cascade at the default parameters. */
#define PASSES 256u
#include "../bench.h"
#include "filters_filters.h"

static _Alignas(FILTERS_FILTERS_ALIGN) uint8_t mem[FILTERS_FILTERS_SIZE];
static filters_filters_params params;

static void setup(void) { bench_noise(12345u); }

static int start(void) {
  filters_filters_params_default(&params);
  return filters_filters_init((filters_filters*)mem, NULL, RATE);
}

static int step(uint32_t at, uint32_t n) {
  return filters_filters_process((filters_filters*)mem, &params, bench_in + at, bench_out + at, n);
}
