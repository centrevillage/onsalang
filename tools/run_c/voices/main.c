/* The bench `voices` of `compare.py run-c` (bench.h): eight voices at 110 Hz, no input, two channels. */
#define PASSES 256u
#define CHANNELS 2u
#include "../bench.h"
#include "voices_voices.h"

static _Alignas(VOICES_VOICES_ALIGN) uint8_t mem[VOICES_VOICES_SIZE];
static voices_voices_params params;

static void setup(void) {}

static int start(void) {
  voices_voices_params_default(&params);
  return voices_voices_init((voices_voices*)mem, NULL, RATE);
}

static int step(uint32_t at, uint32_t n) {
  return voices_voices_process((voices_voices*)mem, &params, bench_out + at, bench_out + FRAMES + at, n);
}
