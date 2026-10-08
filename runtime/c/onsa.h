/* onsa.h — the public definitions of the Onsa runtime (spec §14.2, S-53).
 *
 * A host reads this header through the header of a package (`<prefix><package>.h`):
 * the types the API uses and the version of the ABI. It is the same for every
 * package and every target, holds no definition of the runtime and no check of
 * the compiler flags, so a host compiles it with its own mode and its own
 * floating-point flags. The runtime that the generated `.c` uses is in the
 * internal header, which only the generated `.c` reads.
 */
#ifndef ONSA_H
#define ONSA_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* The version of the C ABI of the generated code (spec §14.2, R-121). */
#define ONSA_ABI_VERSION 1

/* ---- parameter metadata (spec §11.7, §14.2) ------------------------------ */
typedef struct onsa_param_info {
  const char* name;
  const char* id;
  float min;      /* NAN when not given */
  float max;      /* NAN when not given */
  float default_; /* NAN when not given */
  float step;     /* NAN when not given */
  const char* unit;  /* "" when not given */
  const char* scale; /* "linear" or "log" */
  const char* label; /* "" when not given */
} onsa_param_info;

#endif /* ONSA_H */
