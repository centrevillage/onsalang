/* onsa__runtime.h — the internal runtime of the code `onsa build` generates
 * (spec §13.4, §14.2, S-53, S-54).
 *
 * Only the generated `.c` reads this header; a host reads the public `onsa.h`
 * through the header of a package. Everything here is `static inline`: the
 * header is include-only and the generated translation unit is
 * self-contained. The numerics reproduce the reference semantics of the Onsa
 * interpreter bit for bit (spec §3.4, §13.4, S-25): checked integer
 * arithmetic panics, `round` is half-to-even, `min` / `max` propagate NaN and
 * order signed zeros, `fmod` is C `fmod`.
 *
 * Panic (spec §9.2): the generated file defines one of ONSA_PANIC_POISON,
 * ONSA_PANIC_TRAP, ONSA_PANIC_RESET or ONSA_PANIC_HALT before including this
 * header (the target's `panic` setting); the default is ONSA_PANIC_TRAP. A
 * host may define ONSA_PANIC_HANDLER to a function `void f(const char* msg,
 * const char* file, uint32_t line)` that is called first.
 *
 * The defines a host may give (spec §13.4): ONSA_FP_CONTRACT_OFF (GCC in a GNU
 * mode, with -ffp-contract=off), ONSA_ALLOW_INEXACT_FP (no check of the
 * floating-point flags, and no bit-exact result), ONSA_NO_TLS (no thread-local
 * storage), ONSA_PANIC_HANDLER, ONSA_HAS_BUILTIN_OVERFLOW (0: the portable
 * integer checks).
 */
#ifndef ONSA__RUNTIME_H
#define ONSA__RUNTIME_H

#include "onsa.h"

#include <float.h>
#include <math.h>
#include <string.h>

/* ---- constants of the compiler (plan D-15) -------------------------------
 * The values every backend shares live in onsa_core; the C backend writes
 * them in place of the marker line below when it writes this file. */
/* @onsa-core-constants@ */
#if !defined(ONSA_NAN_BITS_F32) || !defined(ONSA_NAN_BITS_F64)
#error "onsa__runtime.h is written by the Onsa compiler; include the file `onsa build` wrote"
#endif

/* ---- the floating-point flags (spec §13.4, S-54) --------------------------
 * The flags that the generated code needs and that a compiler can be seen not
 * to keep stop the compile. ONSA_ALLOW_INEXACT_FP removes every check: the
 * build then has no bit-exact result (spec §13.4). */
#if !defined(ONSA_ALLOW_INEXACT_FP)
#if defined(__GNUC__) && !defined(__clang__) && !defined(__STRICT_ANSI__) && !defined(ONSA_FP_CONTRACT_OFF)
#error "Onsa: GCC in a GNU mode contracts a * b + c into a fused multiply-add; compile in an ISO mode (-std=c11), or pass -ffp-contract=off and define ONSA_FP_CONTRACT_OFF (spec 13.4)"
#endif
#if defined(__FAST_MATH__)
#error "Onsa: -ffast-math (or -Ofast) changes the floating-point results; compile with -fno-fast-math (spec 13.4)"
#endif
#if defined(__FINITE_MATH_ONLY__) && __FINITE_MATH_ONLY__
#error "Onsa: -ffinite-math-only assumes that no value is a NaN or an infinity; compile with -fno-finite-math-only (spec 13.4)"
#endif
#if defined(_M_FP_FAST)
#error "Onsa: /fp:fast changes the floating-point results; compile with /fp:strict (spec 13.4)"
#endif
#if defined(FLT_EVAL_METHOD) && FLT_EVAL_METHOD != 0
#error "Onsa: FLT_EVAL_METHOD is not 0 (an extended precision, as on the x87); use the SSE registers (-msse2 -mfpmath=sse) (spec 13.4)"
#endif
#endif

/* No contraction (spec §13.4). The STDC form is written for the compilers
 * that know it: GCC ignores it (and warns), and the flags and the checks
 * above hold GCC. */
#if defined(_MSC_VER) && !defined(__clang__)
#pragma fp_contract(off)
#elif defined(__clang__) || !defined(__GNUC__)
#pragma STDC FP_CONTRACT OFF
#endif

/* `@fp(relaxed)` (spec §15.5, S-54, S-287): a function given it may contract,
 * and with Clang reassociate; nothing else. ONSA_FP_RELAXED_FN goes before its
 * definition and ONSA_FP_RELAXED_BODY opens its body. GCC is given the
 * contraction only (S-207). */
#if defined(__clang__)
#define ONSA_FP_RELAXED_FN
#define ONSA_FP_RELAXED_BODY _Pragma("clang fp contract(fast) reassociate(on)")
#elif defined(__GNUC__)
#define ONSA_FP_RELAXED_FN __attribute__((optimize("fp-contract=fast")))
#define ONSA_FP_RELAXED_BODY
#else
#define ONSA_FP_RELAXED_FN
#define ONSA_FP_RELAXED_BODY
#endif

/* ---- the C dialect ------------------------------------------------------- */
#if defined(_MSC_VER) && !defined(__clang__)
#define ONSA_STATIC_ASSERT(cond, msg) typedef char onsa_static_assert_##__LINE__[(cond) ? 1 : -1]
#else
#define ONSA_STATIC_ASSERT(cond, msg) _Static_assert(cond, msg)
#endif

#if defined(_MSC_VER) && !defined(__clang__)
#define ONSA_NORETURN __declspec(noreturn)
#define ONSA_NOINLINE __declspec(noinline)
#else
#define ONSA_NORETURN _Noreturn
#if defined(__GNUC__) || defined(__clang__)
#define ONSA_NOINLINE __attribute__((noinline))
#else
#define ONSA_NOINLINE
#endif
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

/* ---- panic (spec §9.2) --------------------------------------------------- */
#ifdef ONSA_PANIC_HANDLER
void ONSA_PANIC_HANDLER(const char* msg, const char* file, uint32_t line);
#endif

#if defined(ONSA_PANIC_POISON)
/* poison (spec §9.2, T4-4): every export wrapper does `setjmp` into a
 * wrapper-local `jmp_buf` (S-26) and publishes it in onsa_current_jmp; a
 * panic `longjmp`s there, the wrapper zeroes its outputs and poisons the
 * instance (process returns 1). Outside any wrapper a panic traps. The slot
 * is per translation unit; wrappers are never re-entered. */
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
 * ONSA_INT_TYPES is the one table of the integer types; every helper below is
 * instantiated from it. For a type T (name N, unsigned image UT, bit width
 * BITS, limits MIN / MAX, SIGNED 1 or 0, MAXP1 = MAX + 1 as a double):
 *   onsa_add_N / sub / mul / div / rem / neg / abs / shl / shr   checked (panic)
 *   onsa_wadd_N / wsub / wmul                                    wrapping
 *   onsa_sadd_N / ssub / smul                                    saturating
 *   onsa_min_N / max                                             plain
 *   onsa_cadd_N / csub / cmul / cdiv                             checked, bool + out
 *   onsa_div_euclid_N / rem_euclid                               checked
 *   onsa_trunc_N_F / onsa_trunc_sat_N_F                          float to integer
 *
 * No helper has undefined behaviour for any operands (R-10), and no helper
 * compares a value with a limit its type always meets (`-Wtype-limits`,
 * R-67): what depends on the sign is written once for each sign
 * (ONSA_INT_SIGNED_1 / _0). The checks of `+ - *` are the compiler's overflow
 * builtins, which compute the exact result (R-10); a check is a comparison
 * and a branch to `onsa_panic`, which under `panic = "trap"` / `"reset"` is
 * the trap or the reset hook and nothing else. Without the builtins
 * (ONSA_HAS_BUILTIN_OVERFLOW 0) the checks compute in a type that holds every
 * result (types of 32 bits or fewer) or test the operands before the
 * operation (64 bits). Wrapping arithmetic is done in unsigned types no
 * narrower than `unsigned int`, so the promotion of a narrow type to `int`
 * never overflows; a conversion back to a signed T keeps the low bits (two's
 * complement, which every compiler Onsa supports does). */
#define ONSA_INT_TYPES(X)                                                                                 \
  X(i8, int8_t, uint8_t, 8, INT8_MIN, INT8_MAX, 1, 128.0)                                                 \
  X(i16, int16_t, uint16_t, 16, INT16_MIN, INT16_MAX, 1, 32768.0)                                         \
  X(i32, int32_t, uint32_t, 32, INT32_MIN, INT32_MAX, 1, 2147483648.0)                                    \
  X(i64, int64_t, uint64_t, 64, INT64_MIN, INT64_MAX, 1, 9223372036854775808.0)                           \
  X(u8, uint8_t, uint8_t, 8, 0, UINT8_MAX, 0, 256.0)                                                      \
  X(u16, uint16_t, uint16_t, 16, 0, UINT16_MAX, 0, 65536.0)                                               \
  X(u32, uint32_t, uint32_t, 32, 0, UINT32_MAX, 0, 4294967296.0)                                          \
  X(u64, uint64_t, uint64_t, 64, 0, UINT64_MAX, 0, 18446744073709551616.0)

#ifndef ONSA_HAS_BUILTIN_OVERFLOW
#if defined(__has_builtin)
#if __has_builtin(__builtin_add_overflow) && __has_builtin(__builtin_sub_overflow) && __has_builtin(__builtin_mul_overflow)
#define ONSA_HAS_BUILTIN_OVERFLOW 1
#endif
#elif defined(__GNUC__) && __GNUC__ >= 5
#define ONSA_HAS_BUILTIN_OVERFLOW 1
#endif
#ifndef ONSA_HAS_BUILTIN_OVERFLOW
#define ONSA_HAS_BUILTIN_OVERFLOW 0
#endif
#endif

#if ONSA_HAS_BUILTIN_OVERFLOW
#define ONSA_INT_CHECKED(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1)                                         \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) { return !__builtin_add_overflow(a, b, r); }             \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) { return !__builtin_sub_overflow(a, b, r); }             \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) { return !__builtin_mul_overflow(a, b, r); }
#else
#define ONSA_INT_CHECKED(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1) ONSA_INT_CHECKED_##BITS(N, T, UT, MIN, MAX, SIGNED)
/* 32 bits or fewer: the exact result in a 64-bit type (int64_t for a signed
 * T, uint64_t for an unsigned one, where a difference below 0 wraps above MAX). */
#define ONSA_WIDE_1 int64_t
#define ONSA_WIDE_0 uint64_t
#define ONSA_IN_RANGE_1(w, WIDE, MIN, MAX) ((w) >= (WIDE)(MIN) && (w) <= (WIDE)(MAX))
#define ONSA_IN_RANGE_0(w, WIDE, MIN, MAX) ((w) <= (WIDE)(MAX))
#define ONSA_INT_CHECKED_WIDE(N, T, MIN, MAX, SIGNED, WIDE)                                               \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a + (WIDE)b;                                                                           \
    if (!ONSA_IN_RANGE_##SIGNED(w, WIDE, MIN, MAX)) return false;                                         \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a - (WIDE)b;                                                                           \
    if (!ONSA_IN_RANGE_##SIGNED(w, WIDE, MIN, MAX)) return false;                                         \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) {                                                        \
    WIDE w = (WIDE)a * (WIDE)b;                                                                           \
    if (!ONSA_IN_RANGE_##SIGNED(w, WIDE, MIN, MAX)) return false;                                         \
    *r = (T)w;                                                                                            \
    return true;                                                                                          \
  }
#define ONSA_INT_CHECKED_8(N, T, UT, MIN, MAX, SIGNED) ONSA_INT_CHECKED_WIDE(N, T, MIN, MAX, SIGNED, ONSA_WIDE_##SIGNED)
#define ONSA_INT_CHECKED_16 ONSA_INT_CHECKED_8
#define ONSA_INT_CHECKED_32 ONSA_INT_CHECKED_8
/* 64 bits: the operands are tested before the operation; the product is
 * formed in UT, then checked by dividing back (exact unless it wrapped). */
#define ONSA_INT_CHECKED_64(N, T, UT, MIN, MAX, SIGNED) ONSA_INT_CHECKED_64_##SIGNED(N, T, UT, MIN, MAX)
#define ONSA_INT_CHECKED_64_1(N, T, UT, MIN, MAX)                                                         \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) {                                                        \
    if ((b > 0 && a > (T)((MAX) - b)) || (b < 0 && a < (T)((MIN) - b))) return false;                     \
    *r = (T)((UT)a + (UT)b);                                                                              \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) {                                                        \
    if ((b < 0 && a > (T)((MAX) + b)) || (b > 0 && a < (T)((MIN) + b))) return false;                     \
    *r = (T)((UT)a - (UT)b);                                                                              \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) {                                                        \
    T p;                                                                                                  \
    if (a == 0 || b == 0) {                                                                               \
      *r = 0;                                                                                             \
      return true;                                                                                        \
    }                                                                                                     \
    if ((a == (T)-1 && b == (MIN)) || (b == (T)-1 && a == (MIN))) return false;                           \
    p = (T)((UT)a * (UT)b);                                                                               \
    if (p / b != a) return false;                                                                         \
    *r = p;                                                                                               \
    return true;                                                                                          \
  }
#define ONSA_INT_CHECKED_64_0(N, T, UT, MIN, MAX)                                                         \
  ONSA_INLINE bool onsa_cadd_##N(T a, T b, T* r) {                                                        \
    if (a > (T)((MAX) - b)) return false;                                                                 \
    *r = (T)(a + b);                                                                                      \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_csub_##N(T a, T b, T* r) {                                                        \
    if (a < b) return false;                                                                              \
    *r = (T)(a - b);                                                                                      \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE bool onsa_cmul_##N(T a, T b, T* r) {                                                        \
    T p;                                                                                                  \
    if (a == 0 || b == 0) {                                                                               \
      *r = 0;                                                                                             \
      return true;                                                                                        \
    }                                                                                                     \
    p = (T)(a * b);                                                                                       \
    if (p / b != a) return false;                                                                         \
    *r = p;                                                                                               \
    return true;                                                                                          \
  }
#endif

/* What every integer type has, whatever its sign. */
#define ONSA_INT_OPS(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1)                                             \
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
  ONSA_INLINE T onsa_div_##N(T a, T b, const char* f, uint32_t l) {                                       \
    T r;                                                                                                  \
    if (b == 0) onsa_panic("division by zero", f, l);                                                     \
    if (!onsa_cdiv_##N(a, b, &r)) onsa_panic("integer overflow in `/`", f, l);                            \
    return r;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_shl_##N(T a, uint32_t n, const char* f, uint32_t l) {                                \
    if (n >= (BITS)) onsa_panic("shift amount exceeds the bit width", f, l);                              \
    return (T)(UT)(1u * (UT)a << n);                                                                      \
  }                                                                                                       \
  ONSA_INLINE T onsa_wadd_##N(T a, T b) { return (T)(UT)(1u * (UT)a + (UT)b); }                           \
  ONSA_INLINE T onsa_wsub_##N(T a, T b) { return (T)(UT)(1u * (UT)a - (UT)b); }                           \
  ONSA_INLINE T onsa_wmul_##N(T a, T b) { return (T)(UT)(1u * (UT)a * (UT)b); }                           \
  ONSA_INLINE T onsa_min_##N(T a, T b) { return a < b ? a : b; }                                          \
  ONSA_INLINE T onsa_max_##N(T a, T b) { return a > b ? a : b; }

/* The division of each sign, which onsa_div_N uses. */
#define ONSA_INT_DIV(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1) ONSA_INT_DIV_##SIGNED(N, T, MIN)
#define ONSA_INT_DIV_1(N, T, MIN)                                                                         \
  ONSA_INLINE bool onsa_cdiv_##N(T a, T b, T* r) {                                                        \
    if (b == 0) return false;                                                                             \
    if (a == (MIN) && b == (T)-1) return false;                                                           \
    *r = (T)(a / b);                                                                                      \
    return true;                                                                                          \
  }                                                                                                       \
  /* `MIN % -1` is 0 (spec §3.4, R-19): every remainder by -1 is, and C's     \
   * `MIN % -1` is undefined, so -1 never reaches `%`. */                                                 \
  ONSA_INLINE T onsa_rem_##N(T a, T b, const char* f, uint32_t l) {                                       \
    if (b == 0) onsa_panic("division by zero", f, l);                                                     \
    if (b == (T)-1) return 0;                                                                             \
    return (T)(a % b);                                                                                    \
  }
#define ONSA_INT_DIV_0(N, T, MIN)                                                                         \
  ONSA_INLINE bool onsa_cdiv_##N(T a, T b, T* r) {                                                        \
    if (b == 0) return false;                                                                             \
    *r = (T)(a / b);                                                                                      \
    return true;                                                                                          \
  }                                                                                                       \
  ONSA_INLINE T onsa_rem_##N(T a, T b, const char* f, uint32_t l) {                                       \
    if (b == 0) onsa_panic("division by zero", f, l);                                                     \
    return (T)(a % b);                                                                                    \
  }

#define ONSA_INT_SIGNED(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1) ONSA_INT_SIGNED_##SIGNED(N, T, UT, MIN, MAX)

/* A signed type. */
#define ONSA_INT_SIGNED_1(N, T, UT, MIN, MAX)                                                             \
  ONSA_INLINE T onsa_neg_##N(T a, const char* f, uint32_t l) {                                            \
    if (a == (MIN)) onsa_panic("integer overflow in negation", f, l);                                     \
    return (T)(0u - (UT)a);                                                                               \
  }                                                                                                       \
  ONSA_INLINE T onsa_abs_##N(T a, const char* f, uint32_t l) {                                            \
    if (a == (MIN)) onsa_panic("integer overflow in `abs`", f, l);                                        \
    return a < 0 ? (T)(0u - (UT)a) : a;                                                                   \
  }                                                                                                       \
  /* Arithmetic for a negative `a` (spec §3.4): -1 - ((-1 - a) >> n), where   \
   * -1 - a is in [0, MAX], so nothing overflows or shifts a negative value,  \
   * and a narrow T promoted to int stays arithmetic. */                                                  \
  ONSA_INLINE T onsa_shr_##N(T a, uint32_t n, const char* f, uint32_t l) {                                \
    if (n >= 8u * sizeof(T)) onsa_panic("shift amount exceeds the bit width", f, l);                      \
    if (a < 0) return (T)((T)-1 - (T)((T)((T)-1 - a) >> n));                                              \
    return (T)((UT)a >> n);                                                                               \
  }                                                                                                       \
  ONSA_INLINE T onsa_sadd_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cadd_##N(a, b, &r)) return r;                                                                \
    return b < 0 ? (MIN) : (MAX);                                                                         \
  }                                                                                                       \
  ONSA_INLINE T onsa_ssub_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_csub_##N(a, b, &r)) return r;                                                                \
    return b > 0 ? (MIN) : (MAX);                                                                         \
  }                                                                                                       \
  ONSA_INLINE T onsa_smul_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cmul_##N(a, b, &r)) return r;                                                                \
    return (a < 0) != (b < 0) ? (MIN) : (MAX);                                                            \
  }                                                                                                       \
  ONSA_INLINE T onsa_div_euclid_##N(T a, T b, const char* f, uint32_t l) {                                \
    T q = onsa_div_##N(a, b, f, l);                                                                       \
    T r = (T)(a % b);                                                                                     \
    if (r < 0) q = (b > 0) ? onsa_sub_##N(q, (T)1, f, l) : onsa_add_##N(q, (T)1, f, l);                   \
    return q;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_rem_euclid_##N(T a, T b, const char* f, uint32_t l) {                                \
    T r = onsa_rem_##N(a, b, f, l);                                                                       \
    if (r < 0) r = (b < 0) ? (T)(r - b) : (T)(r + b);                                                     \
    return r;                                                                                             \
  }

/* An unsigned type: nothing is below 0. */
#define ONSA_INT_SIGNED_0(N, T, UT, MIN, MAX)                                                             \
  ONSA_INLINE T onsa_neg_##N(T a, const char* f, uint32_t l) {                                            \
    if (a != 0) onsa_panic("negation of an unsigned value", f, l);                                        \
    return a;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_abs_##N(T a, const char* f, uint32_t l) {                                            \
    (void)f;                                                                                              \
    (void)l;                                                                                              \
    return a;                                                                                             \
  }                                                                                                       \
  ONSA_INLINE T onsa_shr_##N(T a, uint32_t n, const char* f, uint32_t l) {                                \
    if (n >= 8u * sizeof(T)) onsa_panic("shift amount exceeds the bit width", f, l);                      \
    return (T)(a >> n);                                                                                   \
  }                                                                                                       \
  ONSA_INLINE T onsa_sadd_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cadd_##N(a, b, &r)) return r;                                                                \
    return (MAX);                                                                                         \
  }                                                                                                       \
  ONSA_INLINE T onsa_ssub_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_csub_##N(a, b, &r)) return r;                                                                \
    return (MIN);                                                                                         \
  }                                                                                                       \
  ONSA_INLINE T onsa_smul_##N(T a, T b) {                                                                 \
    T r;                                                                                                  \
    if (onsa_cmul_##N(a, b, &r)) return r;                                                                \
    return (MAX);                                                                                         \
  }                                                                                                       \
  ONSA_INLINE T onsa_div_euclid_##N(T a, T b, const char* f, uint32_t l) { return onsa_div_##N(a, b, f, l); } \
  ONSA_INLINE T onsa_rem_euclid_##N(T a, T b, const char* f, uint32_t l) { return onsa_rem_##N(a, b, f, l); }

/* `x.trunc_i32()` panics out of range or on NaN; `x.trunc_i32_sat()`
 * saturates and maps NaN to 0 (spec §3.3, §3.4). The value truncated toward
 * zero is compared in double against exactly representable limits: MIN, and
 * MAX + 1 (a power of two; MAX itself is not a double for 64 bits, R-19), so
 * `-0.9.trunc_u64()` is 0 (S-189). Above the range `_sat` returns the
 * constant MAX: converting MAXP1 - 1.0, which is MAXP1 again for 64 bits,
 * would be out of range (R-10). */
#define ONSA_TRUNC(N, T, MIN, MAX, MAXP1, F, FT)                                                          \
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
    if (t >= (MAXP1)) return (MAX);                                                                       \
    return (T)t;                                                                                          \
  }
#define ONSA_INT_TRUNC(N, T, UT, BITS, MIN, MAX, SIGNED, MAXP1)                                           \
  ONSA_TRUNC(N, T, MIN, MAX, MAXP1, f32, float)                                                           \
  ONSA_TRUNC(N, T, MIN, MAX, MAXP1, f64, double)

ONSA_INT_TYPES(ONSA_INT_CHECKED)
ONSA_INT_TYPES(ONSA_INT_DIV)
ONSA_INT_TYPES(ONSA_INT_OPS)
ONSA_INT_TYPES(ONSA_INT_SIGNED)
ONSA_INT_TYPES(ONSA_INT_TRUNC)

/* `x.narrow_<to>()` (spec §3.3): onsa_narrow_<from>_<to>(x, &r) is true and
 * stores the value when it is in the range of the target type. The generated
 * file instantiates the pairs it uses with ONSA_DEFINE_NARROW(from, its C
 * type, its sign, to, its C type, its sign). The test of each pair of signs
 * compares no value with a limit its type always meets, and no signed value
 * with an unsigned one (R-11, R-145): a value of the same sign is in range
 * when it converts back to itself; a signed one also needs to be 0 or more;
 * an unsigned one to a signed type needs to be below 2^(bits of the target - 1). */
#define ONSA_NARROW_TEST_11(FT, TT, x) ((FT)(TT)(x) == (x))
#define ONSA_NARROW_TEST_00(FT, TT, x) ((FT)(TT)(x) == (x))
#define ONSA_NARROW_TEST_10(FT, TT, x) ((x) >= 0 && (FT)(TT)(x) == (x))
#define ONSA_NARROW_TEST_01(FT, TT, x) (((uint64_t)(x) >> (8u * sizeof(TT) - 1u)) == 0u)
#define ONSA_NARROW_TEST(FS, TS) ONSA_NARROW_TEST_##FS##TS
#define ONSA_DEFINE_NARROW(F, FT, FS, T, TT, TS)                                                          \
  ONSA_INLINE bool onsa_narrow_##F##_##T(FT x, TT* r) {                                                   \
    if (!ONSA_NARROW_TEST(FS, TS)(FT, TT, x)) return false;                                               \
    *r = (TT)x;                                                                                           \
    return true;                                                                                          \
  }

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
/* `to_bits()` of a NaN is the positive quiet NaN (spec §3.4, S-106); the
 * values are onsa_core's, written above by the C backend. */
ONSA_INLINE uint32_t onsa_bits_f32(float x) {
  uint32_t b;
  if (isnan(x)) return ONSA_NAN_BITS_F32;
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
  if (isnan(x)) return ONSA_NAN_BITS_F64;
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
/* Partial overlap of two byte ranges [a, a + an) and [b, b + bn): the same range is in place
 * (allowed); the same start with lengths that differ is a partial overlap (S-403). Compared as
 * integers (the ranges may be distinct objects, which C's `<` on pointers does not order), by the
 * distance from the lower start, so that a range at the top of the address space does not wrap. */
ONSA_INLINE bool onsa_overlaps(const void* a, size_t an, const void* b, size_t bn) {
  uintptr_t pa = (uintptr_t)a;
  uintptr_t pb = (uintptr_t)b;
  if (pa == pb && an == bn) return false;
  return pa >= pb ? pa - pb < bn : pb - pa < an;
}

#endif /* ONSA__RUNTIME_H */
