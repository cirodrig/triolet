
#include <stdio.h>
#include "mul_interface.h"

int main()
{
  float f = muls_float(1.5, 3.125);
  int i = muls_int(3, 9);
  printf("(%d)(%.4f)", i, f);
  return 0;
}
