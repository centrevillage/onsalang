float floorf(float); double floor(double); float rintf(float); double rint(double); float fmodf(float,float); double fmod(double,double); double trunc(double);
#define NAN (__builtin_nanf(""))
#define INFINITY (__builtin_inff())
#define isnan(x) __builtin_isnan(x)
#define isfinite(x) __builtin_isfinite(x)
#define signbit(x) __builtin_signbit(x)
