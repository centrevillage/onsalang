/* Independent cross-check of tests/vectors in C (W2-01). NOT a norm: it computes nothing that goes into the data.
 *
 * Build (by tools/vectors/xcheck.py): cc -std=gnu11 -O2 -ffp-contract=off -fno-fast-math xcheck.c -lm
 * Run: ./xcheck FILE.tsv...      exit code 0: no mismatch, 1: mismatches, 2: bad input
 *
 * Nothing here can trap or abort: no integer division by 0 or of MIN by -1, no shift by the width or more,
 * no float -> integer cast outside the range, no signed overflow; every such case is decided before the
 * operation (and counted as `guarded`). Integer overflow is detected with __builtin_*_overflow. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <float.h>

typedef unsigned long long WU;

static uint32_t b32(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }
static uint64_t b64(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static float f32b(uint32_t u) { float x; memcpy(&x, &u, 4); return x; }
static double f64b(uint64_t u) { double x; memcpy(&x, &u, 8); return x; }

static long guarded = 0;

static void show_f32(float x, char *o) { if (x != x) strcpy(o, "nan"); else sprintf(o, "0x%08llx", (WU)b32(x)); }
static void show_f64(double x, char *o) { if (x != x) strcpy(o, "nan"); else sprintf(o, "0x%016llx", (WU)b64(x)); }
static const char *B(int v) { return v ? "true" : "false"; }

/* ------------------------------------------------------------------ floats */
#define FLOATOPS(T, N, FM, SQ, FL, CE, TR, RI, AB, BB, SHOW, NANBITS) \
static T min_##N(T a, T b) { if (a != a || b != b) return (T)NAN; if (a == b) return signbit(a) ? a : b; return a < b ? a : b; } \
static T max_##N(T a, T b) { if (a != a || b != b) return (T)NAN; if (a == b) return signbit(a) ? b : a; return a < b ? b : a; } \
static int feval_##N(const char *name, char **a, char *o) { \
  T x = BB(strtoull(a[0], 0, 16)); \
  if (!strcmp(name, "sqrt")) { SHOW(SQ(x), o); return 1; } \
  if (!strcmp(name, "floor")) { SHOW(FL(x), o); return 1; } \
  if (!strcmp(name, "ceil")) { SHOW(CE(x), o); return 1; } \
  if (!strcmp(name, "trunc")) { SHOW(TR(x), o); return 1; } \
  if (!strcmp(name, "round")) { SHOW(RI(x), o); return 1; } /* rint: nearest even in the default mode */ \
  if (!strcmp(name, "abs")) { SHOW(AB(x), o); return 1; } \
  if (!strcmp(name, "neg")) { SHOW(-x, o); return 1; } \
  if (!strcmp(name, "is_nan")) { strcpy(o, B(x != x)); return 1; } \
  if (!strcmp(name, "is_finite")) { strcpy(o, B(isfinite(x))); return 1; } \
  if (!a[1]) return 0; \
  T y = BB(strtoull(a[1], 0, 16)); \
  if (!strcmp(name, "add")) { SHOW(x + y, o); return 1; } \
  if (!strcmp(name, "sub")) { SHOW(x - y, o); return 1; } \
  if (!strcmp(name, "mul")) { SHOW(x * y, o); return 1; } \
  if (!strcmp(name, "div")) { SHOW(x / y, o); return 1; } \
  if (!strcmp(name, "rem")) { SHOW(FM(x, y), o); return 1; } \
  if (!strcmp(name, "eq")) { strcpy(o, B(x == y)); return 1; } \
  if (!strcmp(name, "ne")) { strcpy(o, B(x != y)); return 1; } \
  if (!strcmp(name, "lt")) { strcpy(o, B(x < y)); return 1; } \
  if (!strcmp(name, "le")) { strcpy(o, B(x <= y)); return 1; } \
  if (!strcmp(name, "gt")) { strcpy(o, B(x > y)); return 1; } \
  if (!strcmp(name, "ge")) { strcpy(o, B(x >= y)); return 1; } \
  if (!strcmp(name, "min")) { SHOW(min_##N(x, y), o); return 1; } \
  if (!strcmp(name, "max")) { SHOW(max_##N(x, y), o); return 1; } \
  if (!a[2]) return 0; \
  T z = BB(strtoull(a[2], 0, 16)); \
  /* each operation in its own statement, FP_CONTRACT off */ \
  if (!strcmp(name, "expr_muladd")) { T m = x * y; SHOW(m + z, o); return 1; } \
  if (!strcmp(name, "expr_mulsub")) { T m = x * y; SHOW(m - z, o); return 1; } \
  if (!strcmp(name, "expr_add3_l")) { T s = x + y; SHOW(s + z, o); return 1; } \
  if (!strcmp(name, "expr_add3_r")) { T s = y + z; SHOW(x + s, o); return 1; } \
  if (!strcmp(name, "expr_interp")) { T om = (T)1 - z; T l = om * x; T r = z * y; SHOW(l + r, o); return 1; } \
  return 0; }
FLOATOPS(float, f32, fmodf, sqrtf, floorf, ceilf, truncf, rintf, fabsf, f32b, show_f32, 0)
FLOATOPS(double, f64, fmod, sqrt, floor, ceil, trunc, rint, fabs, f64b, show_f64, 0)

/* float -> integer by the range of the target, decided before the cast */
static int conv_float(int is32, const char *name, char *arg, char *o) {
  double d = is32 ? (double)f32b((uint32_t)strtoull(arg, 0, 16)) : f64b(strtoull(arg, 0, 16));
  if (!strcmp(name, "to_bits")) {
    if (d != d) sprintf(o, "%llu", is32 ? 0x7FC00000ull : 0x7FF8000000000000ull);
    else sprintf(o, "%llu", is32 ? (WU)b32(f32b((uint32_t)strtoull(arg, 0, 16))) : (WU)b64(d));
    return 1;
  }
  if (!strcmp(name, "as_f64")) { show_f64(d, o); return 1; }
  if (!strcmp(name, "as_f32")) { show_f32((float)d, o); return 1; }   /* the same type (S-210) */
  if (!strcmp(name, "round_f32")) { show_f32((float)d, o); return 1; }
  if (strncmp(name, "trunc_", 6)) return 0;
  int sat = strstr(name, "_sat") != NULL;
  const char *ty = name + 6;
  int sgn = ty[0] == 'i', bits = atoi(ty + 1);
  double lo = sgn ? -ldexp(1.0, bits - 1) : 0.0, hi = sgn ? ldexp(1.0, bits - 1) : ldexp(1.0, bits); /* hi is excluded */
  if (d != d) { strcpy(o, sat ? "0" : "panic"); return 1; }
  double t = trunc(d);
  if (t >= lo && t < hi) {
    if (sgn) sprintf(o, "%lld", (long long)t); else sprintf(o, "%llu", (WU)t);
    return 1;
  }
  if (!sat) { strcpy(o, "panic"); return 1; }
  if (t < lo) {
    if (sgn) sprintf(o, "%lld", (long long)(-(((__int128)1) << (bits - 1)))); else strcpy(o, "0");
  } else {
    if (sgn) sprintf(o, "%lld", (long long)((((__int128)1) << (bits - 1)) - 1));
    else sprintf(o, "%llu", (WU)((((unsigned __int128)1) << bits) - 1));
  }
  return 1;
}

static int vdelay(int is32, const char *name, char **a, char *o) {
  WU maxv = strtoull(a[1], 0, 10);
  if (is32) {
    float d = f32b((uint32_t)strtoull(a[0], 0, 16)), M = (float)maxv;
    float m = M;
    float dc = (d >= 1.0f) ? ((d <= m) ? d : m) : 1.0f;
    uint32_t k = (uint32_t)dc; /* 1 <= dc <= MAX < 2^32 */
    float f = dc - (float)k;
    if (!strcmp(name, "vdelay_k")) sprintf(o, "%u", k); else show_f32(f, o);
  } else {
    double d = f64b(strtoull(a[0], 0, 16)), m = (double)maxv;
    double dc = (d >= 1.0) ? ((d <= m) ? d : m) : 1.0;
    uint32_t k = (uint32_t)dc;
    double f = dc - (double)k;
    if (!strcmp(name, "vdelay_k")) sprintf(o, "%u", k); else show_f64(f, o);
  }
  return 1;
}

static int const_float(int is32, const char *name, char *o) {
  if (!strcmp(name, "ZERO")) { if (is32) show_f32(0.0f, o); else show_f64(0.0, o); return 1; }
  if (!strcmp(name, "ONE")) { if (is32) show_f32(1.0f, o); else show_f64(1.0, o); return 1; }
  if (!strcmp(name, "PI")) { if (is32) show_f32(3.14159265358979323846264338327950288f, o); else show_f64(3.14159265358979323846264338327950288, o); return 1; }
  if (!strcmp(name, "MAX")) { if (is32) show_f32(FLT_MAX, o); else show_f64(DBL_MAX, o); return 1; }
  if (!strcmp(name, "EPSILON")) { if (is32) show_f32(FLT_EPSILON, o); else show_f64(DBL_EPSILON, o); return 1; }
  if (!strcmp(name, "INFINITY")) { if (is32) show_f32(INFINITY, o); else show_f64(INFINITY, o); return 1; }
  if (!strcmp(name, "NAN")) { strcpy(o, "nan"); return 1; }
  return 0;
}

/* ---------------------------------------------------------------- integers */
#define INTOPS(T, UT, N, BITS, SGN, MINV, MAXV) \
static void show_##N(T v, char *o) { if (SGN) sprintf(o, "%lld", (long long)v); else sprintf(o, "%llu", (WU)v); } \
static T parse_##N(const char *s) { return SGN ? (T)strtoll(s, 0, 10) : (T)strtoull(s, 0, 10); } \
/* returns 0 when the operation panics */ \
static int base_##N(const char *name, T x, const char *ys, T *r) { \
  T y = (ys && strcmp(name, "shl") && strcmp(name, "shr")) ? parse_##N(ys) : 0; \
  if (!strcmp(name, "add")) return !__builtin_add_overflow(x, y, r); \
  if (!strcmp(name, "sub")) return !__builtin_sub_overflow(x, y, r); \
  if (!strcmp(name, "mul")) return !__builtin_mul_overflow(x, y, r); \
  if (!strcmp(name, "div")) { if (y == 0) return 0; if (SGN && x == MINV && y == (T)-1) return 0; *r = x / y; return 1; } \
  if (!strcmp(name, "rem")) { if (y == 0) return 0; if (SGN && y == (T)-1) { guarded++; *r = 0; return 1; } *r = x % y; return 1; } \
  if (!strcmp(name, "neg")) { if (!SGN) return 0; if (x == MINV) return 0; *r = (T)-x; return 1; } \
  if (!strcmp(name, "abs")) { if (SGN && x == MINV) return 0; *r = (SGN && x < 0) ? (T)-x : x; return 1; } \
  if (!strcmp(name, "wadd")) { *r = (T)((WU)(UT)x + (WU)(UT)y); return 1; } \
  if (!strcmp(name, "wsub")) { *r = (T)((WU)(UT)x - (WU)(UT)y); return 1; } \
  if (!strcmp(name, "wmul")) { *r = (T)((WU)(UT)x * (WU)(UT)y); return 1; } \
  if (!strcmp(name, "sadd")) { if (!__builtin_add_overflow(x, y, r)) return 1; *r = SGN ? (y < 0 ? MINV : MAXV) : MAXV; return 1; } \
  if (!strcmp(name, "ssub")) { if (!__builtin_sub_overflow(x, y, r)) return 1; *r = SGN ? (y < 0 ? MAXV : MINV) : (T)0; return 1; } \
  if (!strcmp(name, "smul")) { if (!__builtin_mul_overflow(x, y, r)) return 1; *r = SGN ? ((x < 0) != (y < 0) ? MINV : MAXV) : MAXV; return 1; } \
  if (!strcmp(name, "div_euclid")) { \
    if (y == 0) return 0; if (SGN && x == MINV && y == (T)-1) return 0; \
    T q = x / y, rm = (SGN && y == (T)-1) ? 0 : x % y; \
    if (SGN && rm < 0) q = (T)(y > 0 ? q - 1 : q + 1); \
    *r = q; return 1; } \
  if (!strcmp(name, "rem_euclid")) { \
    if (y == 0) return 0; \
    T rm; if (SGN && y == (T)-1) { guarded++; rm = 0; } else rm = x % y; \
    if (SGN && rm < 0) rm = (T)((UT)rm + (y < 0 ? (UT)0 - (UT)y : (UT)y)); \
    *r = rm; return 1; } \
  if (!strcmp(name, "and")) { *r = (T)(x & y); return 1; } \
  if (!strcmp(name, "or")) { *r = (T)(x | y); return 1; } \
  if (!strcmp(name, "xor")) { *r = (T)(x ^ y); return 1; } \
  if (!strcmp(name, "not")) { *r = (T)~x; return 1; } \
  if (!strcmp(name, "min")) { *r = y < x ? y : x; return 1; } \
  if (!strcmp(name, "max")) { *r = x < y ? y : x; return 1; } \
  return -1; } \
static int shift_##N(const char *name, T x, const char *ns, T *r) { \
  WU n = strtoull(ns, 0, 10); \
  if (n >= BITS) return 0; \
  if (!strcmp(name, "shl")) { *r = (T)((WU)(UT)x << n); return 1; } \
  *r = (T)(x >> n); return 1; } \
static int ieval_##N(const char *name, char **a, char *o) { \
  T x = parse_##N(a[0]), r = 0; \
  if (!strncmp(name, "as_", 3) || !strncmp(name, "narrow_", 7) || !strncmp(name, "round_", 6)) { \
    __int128 v = SGN ? (__int128)strtoll(a[0], 0, 10) : (__int128)strtoull(a[0], 0, 10); \
    if (!strcmp(name, "as_f32") || !strcmp(name, "round_f32")) { show_f32((float)x, o); return 1; } \
    if (!strcmp(name, "as_f64") || !strcmp(name, "round_f64")) { show_f64((double)x, o); return 1; } \
    const char *dt = strchr(name, '_') + 1; int dsg = dt[0] == 'i', db = atoi(dt + 1); \
    __int128 lo = dsg ? -(((__int128)1) << (db - 1)) : 0, hi = dsg ? (((__int128)1) << (db - 1)) - 1 : (((__int128)1) << db) - 1; \
    int fits = v >= lo && v <= hi; \
    char tmp[64]; if (dsg) sprintf(tmp, "%lld", (long long)v); else sprintf(tmp, "%llu", (WU)v); \
    if (name[0] == 'n') { if (fits) sprintf(o, "some:%s", tmp); else strcpy(o, "none"); } \
    else { strcpy(o, tmp); if (!fits) return 0; } \
    return 1; } \
  int checked = !strncmp(name, "checked_", 8); \
  const char *bn = checked ? name + 8 : name; \
  int ok; \
  if (!strcmp(bn, "shl") || !strcmp(bn, "shr")) ok = shift_##N(bn, x, a[1], &r); \
  else if (!strcmp(bn, "eq") || !strcmp(bn, "ne") || !strcmp(bn, "lt") || !strcmp(bn, "le") || !strcmp(bn, "gt") || !strcmp(bn, "ge")) { \
    T y = parse_##N(a[1]); \
    int c = !strcmp(bn, "eq") ? x == y : !strcmp(bn, "ne") ? x != y : !strcmp(bn, "lt") ? x < y : !strcmp(bn, "le") ? x <= y : !strcmp(bn, "gt") ? x > y : x >= y; \
    strcpy(o, B(c)); return 1; } \
  else ok = base_##N(bn, x, a[1], &r); \
  if (ok < 0) return 0; \
  if (checked) { if (ok) { char t[64]; show_##N(r, t); sprintf(o, "some:%s", t); } else strcpy(o, "none"); return 1; } \
  if (!ok) { strcpy(o, "panic"); return 1; } \
  show_##N(r, o); return 1; } \
static int const_##N(const char *name, char *o) { \
  if (!strcmp(name, "ZERO")) { strcpy(o, "0"); return 1; } \
  if (!strcmp(name, "ONE")) { strcpy(o, "1"); return 1; } \
  if (!strcmp(name, "MIN")) { show_##N(MINV, o); return 1; } \
  if (!strcmp(name, "MAX")) { show_##N(MAXV, o); return 1; } \
  if (!strcmp(name, "BITS")) { sprintf(o, "%d", BITS); return 1; } \
  return 0; }
INTOPS(int8_t, uint8_t, i8, 8, 1, INT8_MIN, INT8_MAX)
INTOPS(int16_t, uint16_t, i16, 16, 1, INT16_MIN, INT16_MAX)
INTOPS(int32_t, uint32_t, i32, 32, 1, INT32_MIN, INT32_MAX)
INTOPS(int64_t, uint64_t, i64, 64, 1, INT64_MIN, INT64_MAX)
INTOPS(uint8_t, uint8_t, u8, 8, 0, 0, UINT8_MAX)
INTOPS(uint16_t, uint16_t, u16, 16, 0, 0, UINT16_MAX)
INTOPS(uint32_t, uint32_t, u32, 32, 0, 0, UINT32_MAX)
INTOPS(uint64_t, uint64_t, u64, 64, 0, 0, UINT64_MAX)

static int eval(const char *op, char **a, char *o) {
  char ty[8];
  const char *dot = strchr(op, '.');
  size_t tl = (size_t)(dot - op);
  memcpy(ty, op, tl); ty[tl] = 0;
  const char *name = dot + 1;
  int isconst = name[0] >= 'A' && name[0] <= 'Z';
  if (!strcmp(ty, "f32") || !strcmp(ty, "f64")) {
    int is32 = !strcmp(ty, "f32");
    if (isconst) return const_float(is32, name, o);
    if (!strncmp(name, "vdelay_", 7)) return vdelay(is32, name, a, o);
    if (!strcmp(name, "from_bits")) {
      if (is32) { show_f32(f32b((uint32_t)strtoull(a[0], 0, 10)), o); } else { show_f64(f64b(strtoull(a[0], 0, 10)), o); }
      return 1;
    }
    if (!strncmp(name, "trunc_", 6) || !strncmp(name, "round_", 6) || !strncmp(name, "as_", 3) || !strcmp(name, "to_bits"))
      return conv_float(is32, name, a[0], o);
    return is32 ? feval_f32(name, a, o) : feval_f64(name, a, o);
  }
#define DISPATCH(N) if (!strcmp(ty, #N)) return isconst ? const_##N(name, o) : ieval_##N(name, a, o)
  DISPATCH(i8); DISPATCH(i16); DISPATCH(i32); DISPATCH(i64); DISPATCH(u8); DISPATCH(u16); DISPATCH(u32); DISPATCH(u64);
  return 0;
}

int main(int argc, char **argv) {
  long rows = 0, bad = 0, held = 0, skipped = 0;
  char op[128] = "", tier[64] = "";
  for (int fi = 1; fi < argc; fi++) {
    FILE *f = fopen(argv[fi], "r");
    if (!f) { perror(argv[fi]); return 2; }
    char line[4096];
    int ln = 0;
    while (fgets(line, sizeof line, f)) {
      ln++;
      size_t n = strlen(line);
      if (n && line[n - 1] == '\n') line[n - 1] = 0;
      if (!line[0] || line[0] == '#') continue;
      if (line[0] == '@') { sscanf(line + 2, "%127s %63s", op, tier); continue; }
      char *tab = strchr(line, '\t');
      if (!tab) { fprintf(stderr, "%s:%d: no tab\n", argv[fi], ln); return 2; }
      *tab = 0;
      char *expect = tab + 1;
      char *t2 = strchr(expect, '\t');
      if (t2) *t2 = 0;
      if (!strcmp(expect, "?")) { held++; continue; }
      char *args[4] = {0, 0, 0, 0};
      int na = 0;
      if (strcmp(line, "()")) for (char *p = strtok(line, " "); p && na < 4; p = strtok(0, " ")) args[na++] = p;
      char out[96] = "";
      if (!eval(op, args, out)) { skipped++; if (skipped <= 5) fprintf(stderr, "skipped %s\n", op); continue; }
      rows++;
      int ok = !strncmp(expect, "panic:", 6) ? !strcmp(out, "panic") : !strcmp(out, expect);
      if (!ok) {
        bad++;
        if (bad <= 20) printf("MISMATCH %s %s %s:%d args=[%s%s%s] expect=%s got=%s\n", op, tier, argv[fi], ln,
                              args[0] ? args[0] : "", args[1] ? " " : "", args[1] ? args[1] : "", expect, out);
      }
    }
    fclose(f);
  }
  printf("rows %ld mismatches %ld held %ld skipped %ld guarded %ld\n", rows, bad, held, skipped, guarded);
  return (bad || skipped) ? 1 : 0;
}
