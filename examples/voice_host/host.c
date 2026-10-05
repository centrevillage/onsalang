/* Spec §17.5: a C host using the exported voice flow. The firmware-style
 * `setup` / `audio_callback` pair is driven here by a loop that renders one
 * second at 48 kHz and writes it as a 16-bit WAV (out.wav). No heap, no
 * large stack values: the state lives in a static buffer sized by the
 * generated header. */
#include "onsa_voice.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static _Alignas(ONSA_VOICE_ALIGN) uint8_t voice_mem[ONSA_VOICE_SIZE];
static onsa_voice* voice;
static onsa_voice_params params;

void setup(void) {
  voice = (onsa_voice*)voice_mem;
  if (onsa_voice_init(voice, NULL, 48000.0f) != 0) { /* BULK_SIZE が 0 なので NULL */
    return;                                             /* init が panic した。使い始めない */
  }
  onsa_voice_params_default(&params);
}

void audio_callback(const float* const* in, float* const* out, size_t frames) {
  (void)in;
  onsa_voice_process(voice, &params, out[0], (uint32_t)frames);
}

static void put_u32(FILE* f, uint32_t v) {
  uint8_t b[4] = { (uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16), (uint8_t)(v >> 24) };
  fwrite(b, 1, 4, f);
}

static void put_u16(FILE* f, uint16_t v) {
  uint8_t b[2] = { (uint8_t)v, (uint8_t)(v >> 8) };
  fwrite(b, 1, 2, f);
}

int main(void) {
  enum { RATE = 48000, BLOCK = 256, SECONDS = 1 };
  static float block[BLOCK];
  float* outs[1] = { block };
  FILE* f = fopen("out.wav", "wb");
  if (!f) return 1;
  const uint32_t frames = RATE * SECONDS;
  fwrite("RIFF", 1, 4, f);
  put_u32(f, 36 + frames * 2);
  fwrite("WAVEfmt ", 1, 8, f);
  put_u32(f, 16);
  put_u16(f, 1);          /* PCM */
  put_u16(f, 1);          /* mono */
  put_u32(f, RATE);
  put_u32(f, RATE * 2);   /* byte rate */
  put_u16(f, 2);          /* block align */
  put_u16(f, 16);         /* bits */
  fwrite("data", 1, 4, f);
  put_u32(f, frames * 2);
  setup();
  for (uint32_t done = 0; done < frames; done += BLOCK) {
    uint32_t n = frames - done < BLOCK ? frames - done : BLOCK;
    audio_callback(NULL, outs, n);
    for (uint32_t i = 0; i < n; i++) {
      float x = block[i];
      if (x > 1.0f) x = 1.0f;
      if (x < -1.0f) x = -1.0f;
      put_u16(f, (uint16_t)(int16_t)(x * 32767.0f));
    }
  }
  fclose(f);
  return 0;
}
