/* The driver of the benches of `compare.py run-c` (tools/compare.py). A bench's main.c defines PASSES (and, when
 * not the defaults, BLOCK and CHANNELS), includes this, and defines `setup` (the input in `bench_in`, once),
 * `start` (a fresh instance: `init` and the parameters) and `step` (one call of `process` on the frames
 * [at, at + n) of `bench_in`, into `bench_out` + c * FRAMES + at for the channel c). A run is `start` and PASSES
 * passes over the FRAMES frames, a block of BLOCK at a time.
 * `main [reps]` times `reps` runs (default 5) with CLOCK_MONOTONIC and prints one line: the least nanoseconds,
 * then the value of the output of the last pass of the last run (the FNV-1a hash of the bits of every sample,
 * a slash, their sum). An error is an exit code, never an abort: 2 for the argument, 3 when `init` or `process`
 * did not return 0. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define RATE 48000.0f
#define FRAMES 16384u
#ifndef BLOCK
#define BLOCK 64u
#endif
#ifndef CHANNELS
#define CHANNELS 1u
#endif

static float bench_in[FRAMES];
static float bench_out[CHANNELS * FRAMES];

static void setup(void);
static int start(void);
static int step(uint32_t at, uint32_t n);

/* Noise in [-1, 1) from xorshift32 with the seed given. */
static inline void bench_noise(uint32_t seed) {
  for (uint32_t i = 0; i < FRAMES; i++) {
    seed ^= seed << 13;
    seed ^= seed >> 17;
    seed ^= seed << 5;
    bench_in[i] = (float)(seed >> 8) / 8388608.0f - 1.0f;
  }
}

static uint64_t bench_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

static int bench_run(void) {
  if (start() != 0) return 1;
  for (uint32_t pass = 0; pass < PASSES; pass++) {
    for (uint32_t at = 0; at < FRAMES; at += BLOCK) {
      if (step(at, BLOCK) != 0) return 1;
    }
  }
  return 0;
}

int main(int argc, char** argv) {
  long reps = argc > 1 ? strtol(argv[1], NULL, 10) : 5;
  if (argc > 2 || reps < 1 || reps > 1000) {
    fprintf(stderr, "usage: %s [reps: 1 to 1000]\n", argv[0]);
    return 2;
  }
  setup();
  uint64_t least = UINT64_MAX;
  for (long r = 0; r < reps; r++) {
    uint64_t t = bench_ns();
    if (bench_run() != 0) {
      fprintf(stderr, "%s: init or process did not return 0\n", argv[0]);
      return 3;
    }
    t = bench_ns() - t;
    least = t < least ? t : least;
  }
  uint64_t h = 1469598103934665603u;
  double sum = 0.0;
  for (uint32_t i = 0; i < CHANNELS * FRAMES; i++) {
    uint32_t b;
    memcpy(&b, &bench_out[i], sizeof b);
    for (int k = 0; k < 4; k++) h = (h ^ ((b >> (8 * k)) & 0xffu)) * 1099511628211u;
    sum += bench_out[i];
  }
  printf("%llu %016llx/%.9g\n", (unsigned long long)least, (unsigned long long)h, sum);
  return 0;
}
