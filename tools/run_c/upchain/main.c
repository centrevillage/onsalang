/* The bench `upchain` of `compare.py run-c` (bench.h): a sine of 441 Hz (an integer number of periods in a pass)
 * through the oversampled shaper at the default drive. */
#include <math.h>
#define PASSES 128u
#include "../bench.h"
#include "upchain_upchain.h"

static _Alignas(UPCHAIN_UPCHAIN_ALIGN) uint8_t mem[UPCHAIN_UPCHAIN_SIZE];
static upchain_upchain_params params;

static void setup(void) {
  for (uint32_t i = 0; i < FRAMES; i++) bench_in[i] = 0.8f * (float)sin(2.0 * 3.14159265358979 * 441.0 * i / 48000.0);
}

static int start(void) {
  upchain_upchain_params_default(&params);
  return upchain_upchain_init((upchain_upchain*)mem, NULL, RATE);
}

static int step(uint32_t at, uint32_t n) {
  return upchain_upchain_process((upchain_upchain*)mem, &params, bench_in + at, bench_out + at, n);
}
