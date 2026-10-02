#include "t_p2.h"
#include <stdio.h>
int main(void) {
  printf("alias1 = %d (expect 21)\n", t_alias1());
  printf("alias2 = %d (expect 21)\n", t_alias2());
  printf("alias3 = %d (expect 312)\n", t_alias3());
  return 0;
}
