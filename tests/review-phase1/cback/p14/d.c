#include "t_p14.h"
#include <stdio.h>
int main(void){ unsigned r = t_mul(4294967295u, 4294967295u); printf("mul(max,max) = %u, take_panic = %d (expect 0, 1)\n", r, t_take_panic()); r = t_mul(65536u, 65537u); printf("mul(65536,65537) = %u, take_panic = %d (expect 0, 1)\n", r, t_take_panic()); return 0; }
