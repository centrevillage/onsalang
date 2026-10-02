#include "t_p9.h"
#include <stdio.h>
#include <math.h>
int main(void){ volatile float n = NAN; printf("sat(NaN)=%d (expect 0) min(NaN,1)=%g (expect nan)\n", t_sat(n), t_mn(n, 1.0f)); return 0; }
