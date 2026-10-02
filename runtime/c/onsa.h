/* onsa.h — runtime definitions included by every file `onsa build` generates.
 *
 * Everything here is `static inline`: the header is include-only and the
 * generated translation unit is self-contained. The numerics reproduce the
 * reference semantics of the Onsa interpreter bit for bit (spec §3.4, §13.4,
 * S-25): checked integer arithmetic panics, `round` is half-to-even, `min` /
 * `max` propagate NaN and order signed zeros, `fmod` is C `fmod`.
 *
 * Panic (spec §9.2): the generated file defines one of ONSA_PANIC_POISON,
 * ONSA_PANIC_TRAP, ONSA_PANIC_RESET or ONSA_PANIC_HALT before including this
 * header (the target's `panic` setting); the default is ONSA_PANIC_TRAP. A
 * host may define ONSA_PANIC_HANDLER to a function `void f(const char* msg,
 * const char* file, uint32_t line)` that is called first.
 */
#ifndef ONSA_H
#define ONSA_H

#include <float.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* ---- bit-exact floating point (spec §13.4) ------------------------------- */
#if defined(_MSC_VER)
#pragma fp_contract(off)
#else
#pragma STDC FP_CONTRACT OFF
#endif

#if defined(_MSC_VER) && !defined(__clang__)
#define ONSA_STATIC_ASSERT(cond, msg) typedef char onsa_static_assert_##__LINE__[(cond) ? 1 : -1]
#else
#define ONSA_STATIC_ASSERT(cond, msg) _Static_assert(cond, msg)
#endif

#if defined(FLT_EVAL_METHOD)
ONSA_STATIC_ASSERT(FLT_EVAL_METHOD == 0, "Onsa needs FLT_EVAL_METHOD == 0 (no extended precision; use SSE on x86-32)");
#endif

#if defined(_MSC_VER) && !defined(__clang__)
#define ONSA_NORETURN __declspec(noreturn)
#else
#define ONSA_NORETURN _Noreturn
#endif
#if defined(__GNUC__) || defined(__clang__)
#define ONSA_UNUSED __attribute__((unused))
#else
#define ONSA_UNUSED
#endif
/* Every helper and every generated internal function is `static inline`; the
 * unused attribute keeps instantiated-but-unused helpers warning-free. */
#define ONSA_INLINE static inline ONSA_UNUSED

#if defined(_MSC_VER) && !defined(__clang__)
#define ONSA_ALIGNOF(t) __alignof(t)
#else
#define ONSA_ALIGNOF(t) _Alignof(t)
#endif

/* Thread-local storage for the poison mechanism (T4-4). Define ONSA_NO_TLS on
 * targets without TLS (bare metal): the slot is then a plain static, which is
 * fine as long as export wrappers of one package never run concurrently. */
#if defined(ONSA_NO_TLS)
#define ONSA_THREAD_LOCAL
#elif defined(_MSC_VER) && !defined(__clang__)
#define ONSA_THREAD_LOCAL __declspec(thread)
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#define ONSA_THREAD_LOCAL _Thread_local
#else
#define ONSA_THREAD_LOCAL
#endif

/* The unit value `()`; functions returning it are `void`. */
typedef struct onsa_unit {
  uint8_t onsa_empty;
} onsa_unit;

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

/* ---- panic (spec §9.2) --------------------------------------------------- */
#ifdef ONSA_PANIC_HANDLER
void ONSA_PANIC_HANDLER(const char* msg, const char* file, uint32_t line);
#endif

#if defined(ONSA_PANIC_POISON)
/* poison (spec §9.2, T4-4): every export wrapper does `setjmp` into the
 * instance's `jmp_buf` (process; it lives at the end of the fast region) or
 * into a wrapper-local one (init, exported functions) and publishes it in
 * onsa_current_jmp; a panic `longjmp`s there, the wrapper zeroes its outputs
 * and poisons the instance (process returns 1). Outside any wrapper a panic
 * traps. The jmp_buf is a wrapper local (S-26), so state layouts do not
 * depend on the host's setjmp. The slot is per translation unit; wrappers
 * are never re-entered. */
#include <setjmp.h>
static ONSA_THREAD_LOCAL jmp_buf* onsa_current_jmp ONSA_UNUSED = NULL;
ONSA_NORETURN ONSA_INLINE void onsa_panic(const char* msg, const char* file, uint32_t line) {
#ifdef ONSA_PANIC_HANDLER
  ONSA_PANIC_HANDLER(msg, file, line);
#else
  (void)msg; (void)file; (void)line;
#endif
  if (onsa_current_jmp) longjmp(*onsa_current_jmp, 1);
#if defined(_MSC_VER) && !defined(__clang__)
  __debugbreak();
  for (;;) {
  }
#else
  __builtin_trap();
#endif
}
#elif defined(ONSA_PANIC_RESET)
ONSA_NORETURN void onsa_reset_hook(void); /* provided by the firmware */
ONSA_NORETURN ONSA_INLINE void onsa_panic(const char* msg, const char* file, uint32_t line) {
#ifdef ONSA_PANIC_HANDLER
  ONSA_PANIC_HANDLER(msg, file, line);
#else
  (void)msg; (void)file; (void)line;
#endif
  onsa_reset_hook();
}
#elif defined(ONSA_PANIC_HALT)
ONSA_NORETURN ONSA_INLINE void onsa_panic(const char* msg, const char* file, uint32_t line) {
#ifdef ONSA_PANIC_HANDLER
  ONSA_PANIC_HANDLER(msg, file, line);
#else
  (void)msg; (void)file; (void)line;
#endif
  for (;;) {
  }
}
#else /* ONSA_PANIC_TRAP (default) */
ONSA_NORETURN ONSA_INLINE void onsa_panic(const char* msg, const char* file, uint32_t line) {
#ifdef ONSA_PANIC_HANDLER
  ONSA_PANIC_HANDLER(msg, file, line);
#else
  (void)msg; (void)file; (void)line;
#endif
#if defined(_MSC_VER) && !defined(__clang__)
  __debugbreak();
  for (;;) {
  }
#else
  __builtin_trap();
#endif
}
#endif

/* ---- bounds checks (spec §9.2) ------------------------------------------- */
ONSA_INLINE uint32_t onsa_idx(uint32_t i, uint32_t n, const char* file, uint32_t line) {
  if (i >= n) onsa_panic("index out of range", file, line);
  return i;
}

/* ---- integer helpers (spec §3.4) ------------------------------------------
 * ONSA_INT_OPS instantiates, for an integer type T (name N, unsigned image UT,
 * bit width BITS, limits MIN / MAX, and a wider signed type WIDE that holds
 * every T product when BITS <= 32):
 *   onsa_add_N / sub / mul / div / rem / neg / abs / shl / shr   checked (panic)
 *   onsa_wadd_N / wsub / wmul                                    wrapping
 *   onsa_sadd_N / ssub / smul                                    saturating
 *   onsa_min_N / max                                             plain
 *   onsa_cadd_N / csub / cmul / cdiv                             checked, bool + out
 *   onsa_div_euclid_N / rem_euclid                               checked
 */
#if defined(__GNUC__) || defined(__clang__)
#define ONSA_HAS_BUILTIN_OVERFLOW 1
#else
#define ONSA_HAS_BUILTIN_OVERFLOW 0
#endif

#define ONSA_INT_OPS_NARROW(N, T, UT, BITS, MIN, MAX, WIDE, SIGNED)                                        \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a + (WIDE)b;                                                                           \
    if (w < (WIDE)(MIN) || w > (WIDE)(MAX)) return false;                                                 \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a - (WIDE)b;                                                                           \
    if (w < (WIDE)(MIN) || w > (WIDE)(MAX)) return false;                                                 \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a * (WIDE)b;                                                                           \
    if (w < (WIDE)(MIN) || w > (WIDE)(MAX)) return false;                                                 \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INT_OPS_COMMON(N, T, UT, BITS, MIN, MAX, SIGNED)

#if ONSA_HAS_BUILTIN_OVERFLOW
#define ONSA_INT_OPS_WIDE(N, T, UT, BITS, MIN, MAX, SIGNED)                                               \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) { return !__builtin_add_overflow(a, b, r); }             \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) { return !__builtin_sub_overflow(a, b, r); }             \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) { return !__builtin_mul_overflow(a, b, r); }             \
  ONSA_INT_OPS_COMMON(N, T, UT, BITS, MIN, MAX, SIGNED)
#else
#define ONSA_INT_OPS_WIDE(N, T, UT, BITS, MIN, MAX, SIGNED)                                               \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) {                                                        \
    if (SIGNED) {                                                                                         \
      if ((b > 0 && a > (T)((MAX) - b)) || (b < 0 && a < (T)((MIN) - b))) return false;                   \
    } else {                                                                                              \
      if ((UT)a > (UT)((MAX) - b)) return false;                                                          \
    }                                                                                                     \
    *r = (T)((UT)a + (UT)b);                                                                              \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) {                                                        \
    if (SIGNED) {                                                                                         \
      if ((b < 0 && a > (T)((MAX) + b)) || (b > 0 && a < (T)((MIN) + b))) return false;                   \
    } else {                                                                                              \
      if ((UT)a < (UT)b) return false;                                                                    \
    }                                                                                                     \
    *r = (T)((UT)a - (UT)b);                                                                              \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) {                                                        \
    if (a == 0 || b == 0) {                                                                               \
      *r = 0;                                                                                             \
      return true;                                                                                        \
    }                                                                                                     \
    T p = (T)((UT)a * (UT)b);                                                                             \
    if (SIGNED && ((a == (T)-1 && b == (MIN)) || (b == (T)-1 && a == (MIN)))) return false;               \
    if (p / b != a) return false;                                                                         \
    *r = p;                                                                                               \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INT_OPS_COMMON(N, T, UT, BITS, MIN, MAX, SIGNED)
#endif

#define ONSA_INT_OPS_COMMON(N, T, UT, BITS, MIN, MAX, SIGNED)                                             \
  ONSA_INLINE T onsa_add_##N(T a, T b, const char* f, uint32_t l) {                                       \
    T r;                                                                                                  \
    if (!onsa_cadd_##N(a, b, &r)) onsa_panic("integer overflow in `+`", f, l);                            \
    return r;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_sub_##N(T a, T b, const char* f, uint32_t l) {                                       \
    T r;                                                                                                  \
    if (!onsa_csub_##N(a, b, &r)) onsa_panic("integer overflow in `-`", f, l);                            \
    return r;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_mul_##N(T a, T b, const char* f, uint32_t l) {                                       \
    T r;                                                                                                  \
    if (!onsa_cmul_##N(a, b, &r)) onsa_panic("integer overflow in `*`", f, l);                            \
    return r;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cdiv_##N(T a, T b, T* r) {                                                        \
    if (b == 0) return false;                                                                             \
    if (SIGNED && a == (MIN) && b == (T)-1) return false;                                                 \
    *r = (T)(a / b);                                                                                      \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE T onsa_div_##N(T a, T b, const char* f, uint32_t l) {                                       \
    T r;                                                                                                  \
    if (b == 0) onsa_panic("division by zero", f, l);                                                     \
    if (!onsa_cdiv_##N(a, b, &r)) onsa_panic("integer overflow in `/`", f, l);                            \
    return r;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_rem_##N(T a, T b, const char* f, uint32_t l) {                                       \
    if (b == 0) onsa_panic("division by zero", f, l);                                                     \
    if (SIGNED && a == (MIN) && b == (T)-1) onsa_panic("integer overflow in `%`", f, l);                  \
    return (T)(a % b);                                                                                    \
  }                                                                                                       \
  ONSA_INLINE T onsa_neg_##N(T a, const char* f, uint32_t l) {                                            \
    if (SIGNED && a == (MIN)) onsa_panic("integer overflow in negation", f, l);                           \
    if (!SIGNED && a != 0) onsa_panic("negation of an unsigned value", f, l);                             \
    return (T)(0 - (UT)a);                                                                                \
  }                                                                                                       \
  ONSA_INLINE T onsa_abs_##N(T a, const char* f, uint32_t l) {                                            \
    if (SIGNED && a == (MIN)) onsa_panic("integer overflow in `abs`", f, l);                              \
    return a < 0 ? (T)(0 - (UT)a) : a;                                                                    \
  }                                                                                                       \
  ONSA_INLINE T onsa_shl_##N(T a, uint32_t n, const char* f, uint32_t l) {                                \
    if (n >= (BITS)) onsa_panic("shift amount exceeds the bit width", f, l);                              \
    return (T)((UT)a << n);                                                                               \
  }                                                                                                       \
  ONSA_INLINE T onsa_shr_##N(T a, uint32_t n, const char* f, uint32_t l) {                                \
    if (n >= (BITS)) onsa_panic("shift amount exceeds the bit width", f, l);                              \
    if (SIGNED && a < 0) return (T)~((~(UT)a) >> n); /* arithmetic shift, portably */                     \
    return (T)((UT)a >> n);                                                                               \
  }                                                                                                       \
  ONSA_INLINE T onsa_wadd_##N(T a, T b) { return (T)((UT)a + (UT)b); }                                    \
  ONSA_INLINE T onsa_wsub_##N(T a, T b) { return (T)((UT)a - (UT)b); }                                    \
  ONSA_INLINE T onsa_wmul_##N(T a, T b) { return (T)((UT)a * (UT)b); }                                    \
  ONSA_INLINE T onsa_sadd_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cadd_##N(a, b, &r)) return r;                                                                \
    return (SIGNED && b < 0) ? (MIN) : (MAX);                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_ssub_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_csub_##N(a, b, &r)) return r;                                                                \
    return (SIGNED && b > 0) || !SIGNED ? (MIN) : (MAX);                                                  \
  }                                                                                                       \
  ONSA_INLINE T onsa_smul_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cmul_##N(a, b, &r)) return r;                                                                \
    return (SIGNED && ((a < 0) != (b < 0))) ? (MIN) : (MAX);                                              \
  }                                                                                                       \
  ONSA_INLINE T onsa_min_##N(T a, T b) { return a < b ? a : b; }                                          \
  ONSA_INLINE T onsa_max_##N(T a, T b) { return a > b ? a : b; }                                          \
  ONSA_INLINE T onsa_div_euclid_##N(T a, T b, const char* f, uint32_t l) {                                \
    T q = onsa_div_##N(a, b, f, l);                                                                       \
    T r = (T)(a % b);                                                                                     \
    if (SIGNED && r < 0) q = (b > 0) ? onsa_sub_##N(q, (T)1, f, l) : onsa_add_##N(q, (T)1, f, l);         \
    return q;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_rem_euclid_##N(T a, T b, const char* f, uint32_t l) {                                \
    T r = onsa_rem_##N(a, b, f, l);                                                                       \
    if (SIGNED && r < 0) r = (b < 0) ? (T)(r - b) : (T)(r + b);                                           \
    return r;                                                                                             \
  }

ONSA_INT_OPS_NARROW(i8, int8_t, uint8_t, 8, INT8_MIN, INT8_MAX, int64_t, 1)
ONSA_INT_OPS_NARROW(i16, int16_t, uint16_t, 16, INT16_MIN, INT16_MAX, int64_t, 1)
ONSA_INT_OPS_NARROW(i32, int32_t, uint32_t, 32, INT32_MIN, INT32_MAX, int64_t, 1)
ONSA_INT_OPS_WIDE(i64, int64_t, uint64_t, 64, INT64_MIN, INT64_MAX, 1)
ONSA_INT_OPS_NARROW(u8, uint8_t, uint8_t, 8, 0, UINT8_MAX, int64_t, 0)
ONSA_INT_OPS_NARROW(u16, uint16_t, uint16_t, 16, 0, UINT16_MAX, int64_t, 0)
ONSA_INT_OPS_NARROW(u32, uint32_t, uint32_t, 32, 0, UINT32_MAX, int64_t, 0)
ONSA_INT_OPS_WIDE(u64, uint64_t, uint64_t, 64, 0, UINT64_MAX, 0)

/* ---- float helpers (spec §3.3, §13.4, S-25) ------------------------------ */
ONSA_INLINE float onsa_fmin_f32(float a, float b) {
  if (isnan(a) || isnan(b)) return NAN;
  if (a == 0.0f && b == 0.0f) return (signbit(a) || signbit(b)) ? -0.0f : 0.0f;
  return a < b ? a : b;
}
ONSA_INLINE float onsa_fmax_f32(float a, float b) {
  if (isnan(a) || isnan(b)) return NAN;
  if (a == 0.0f && b == 0.0f) return (signbit(a) && signbit(b)) ? -0.0f : 0.0f;
  return a > b ? a : b;
}
ONSA_INLINE double onsa_fmin_f64(double a, double b) {
  if (isnan(a) || isnan(b)) return NAN;
  if (a == 0.0 && b == 0.0) return (signbit(a) || signbit(b)) ? -0.0 : 0.0;
  return a < b ? a : b;
}
ONSA_INLINE double onsa_fmax_f64(double a, double b) {
  if (isnan(a) || isnan(b)) return NAN;
  if (a == 0.0 && b == 0.0) return (signbit(a) && signbit(b)) ? -0.0 : 0.0;
  return a > b ? a : b;
}
/* Round half to even. The generated code never changes the rounding mode,
 * so rint under the default FE_TONEAREST is exactly this. */
ONSA_INLINE float onsa_round_f32(float x) { return rintf(x); }
ONSA_INLINE double onsa_round_f64(double x) { return rint(x); }
ONSA_INLINE float onsa_fmod_f32(float a, float b) { return fmodf(a, b); }
ONSA_INLINE double onsa_fmod_f64(double a, double b) { return fmod(a, b); }
ONSA_INLINE uint32_t onsa_bits_f32(float x) {
  uint32_t b;
  memcpy(&b, &x, 4);
  return b;
}
ONSA_INLINE float onsa_from_bits_f32(uint32_t b) {
  float x;
  memcpy(&x, &b, 4);
  return x;
}
ONSA_INLINE uint64_t onsa_bits_f64(double x) {
  uint64_t b;
  memcpy(&b, &x, 8);
  return b;
}
ONSA_INLINE double onsa_from_bits_f64(uint64_t b) {
  double x;
  memcpy(&x, &b, 8);
  return x;
}
/* Parameter saturation (spec §11.7): NaN passes through. */
ONSA_INLINE float onsa_clamp_f32(float x, float lo, float hi) { return x < lo ? lo : (x > hi ? hi : x); }
ONSA_INLINE double onsa_clamp_f64(double x, double lo, double hi) { return x < lo ? lo : (x > hi ? hi : x); }

/* `x.trunc_i32()` panics out of range or on NaN; `x.trunc_i32_sat()`
 * saturates and maps NaN to 0 (spec §3.3). Comparisons are done in double
 * against exactly representable limits: MIN, and MAX + 1 (a power of two). */
#define ONSA_TRUNC(N, T, MIN, MAXP1, F, FT)                                                               \
  ONSA_INLINE T onsa_trunc_##N##_##F(FT x, const char* f, uint32_t l) {                                   \
    double t;                                                                                             \
    if (isnan(x)) onsa_panic("conversion of NaN to an integer", f, l);                                    \
    t = trunc((double)x);                                                                                 \
    if (t < (double)(MIN) || t >= (MAXP1)) onsa_panic("float out of range for the integer type", f, l);   \
    return (T)t;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE T onsa_trunc_sat_##N##_##F(FT x) {                                                          \
    double t;                                                                                             \
    if (isnan(x)) return 0;                                                                               \
    t = trunc((double)x);                                                                                 \
    if (t <= (double)(MIN)) return (MIN);                                                                 \
    if (t >= (MAXP1)) return (T)((MAXP1) - 1.0);                                                          \
    return (T)t;                                                                                          \
  }
#define ONSA_TRUNC_BOTH(N, T, MIN, MAXP1)                                                                 \
  ONSA_TRUNC(N, T, MIN, MAXP1, f32, float)                                                                \
  ONSA_TRUNC(N, T, MIN, MAXP1, f64, double)
ONSA_TRUNC_BOTH(i8, int8_t, INT8_MIN, 128.0)
ONSA_TRUNC_BOTH(i16, int16_t, INT16_MIN, 32768.0)
ONSA_TRUNC_BOTH(i32, int32_t, INT32_MIN, 2147483648.0)
ONSA_TRUNC_BOTH(i64, int64_t, INT64_MIN, 9223372036854775808.0)
ONSA_TRUNC_BOTH(u8, uint8_t, 0, 256.0)
ONSA_TRUNC_BOTH(u16, uint16_t, 0, 65536.0)
ONSA_TRUNC_BOTH(u32, uint32_t, 0, 4294967296.0)
ONSA_TRUNC_BOTH(u64, uint64_t, 0, 18446744073709551616.0)

/* ---- spans (spec §5.3, S-12) ----------------------------------------------
 * ONSA_DEFINE_SPAN(N, T) defines onsa_span_N { T* ptr; uint32_t len; } and
 * the sequence helpers over it. The generated file instantiates the element
 * types it uses. */
#define ONSA_DEFINE_SPAN(N, T)                                                                            \
  typedef struct onsa_span_##N {                                                                          \
    T* ptr;                                                                                               \
    uint32_t len;                                                                                         \
  } onsa_span_##N;                                                                                        \
  ONSA_INLINE onsa_span_##N onsa_span_##N##_of(T* ptr, uint32_t len) {                                    \
    onsa_span_##N s;                                                                                      \
    s.ptr = ptr;                                                                                          \
    s.len = len;                                                                                          \
    return s;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE onsa_span_##N onsa_slice_##N(onsa_span_##N s, uint32_t from, uint32_t to, const char* f,    \
                                           uint32_t l) {                                                  \
    if (from > to || to > s.len) onsa_panic("slice out of range", f, l);                                  \
    return onsa_span_##N##_of(s.ptr + from, to - from);                                                   \
  }                                                                                                       \
  ONSA_INLINE void onsa_fill_##N(onsa_span_##N s, T v) {                                                  \
    uint32_t i;                                                                                           \
    for (i = 0; i < s.len; i++) s.ptr[i] = v;                                                             \
  }                                                                                                       \
  ONSA_INLINE void onsa_copy_from_##N(onsa_span_##N d, onsa_span_##N s, const char* f, uint32_t l) {      \
    if (d.len != s.len) onsa_panic("span lengths differ", f, l);                                          \
    if (d.len) memmove(d.ptr, s.ptr, (size_t)d.len * sizeof(T));                                          \
  }

#define ONSA_DEFINE_SPAN_ADD_F32(N)                                                                       \
  ONSA_INLINE void onsa_add_from_##N(onsa_span_##N d, onsa_span_##N s, const char* f, uint32_t l) {       \
    uint32_t i;                                                                                           \
    if (d.len != s.len) onsa_panic("span lengths differ", f, l);                                          \
    for (i = 0; i < d.len; i++) d.ptr[i] = (float)(d.ptr[i] + s.ptr[i]);                                  \
  }
#define ONSA_DEFINE_SPAN_ADD_F64(N)                                                                       \
  ONSA_INLINE void onsa_add_from_##N(onsa_span_##N d, onsa_span_##N s, const char* f, uint32_t l) {       \
    uint32_t i;                                                                                           \
    if (d.len != s.len) onsa_panic("span lengths differ", f, l);                                          \
    for (i = 0; i < d.len; i++) d.ptr[i] = d.ptr[i] + s.ptr[i];                                           \
  }
#define ONSA_DEFINE_SPAN_ADD_INT(N, IN)                                                                   \
  ONSA_INLINE void onsa_add_from_##N(onsa_span_##N d, onsa_span_##N s, const char* f, uint32_t l) {       \
    uint32_t i;                                                                                           \
    if (d.len != s.len) onsa_panic("span lengths differ", f, l);                                          \
    for (i = 0; i < d.len; i++) d.ptr[i] = onsa_add_##IN(d.ptr[i], s.ptr[i], f, l);                       \
  }

/* ---- export wrappers (spec §14.2) ----------------------------------------- */
/* Partial overlap of two byte ranges (identical starts are in-place, allowed). */
ONSA_INLINE bool onsa_overlaps(const void* a, size_t an, const void* b, size_t bn) {
  const char* pa = (const char*)a;
  const char* pb = (const char*)b;
  if (pa == pb) return false;
  return pa < pb + bn && pb < pa + an;
}

#endif /* ONSA_H */
