
#include <stdio.h>
#include "poly_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

  float e = 2.71828;
  float p = 3.14159;
  int pick11 = pick_int(11, 13, 1);
  int pick13 = pick_int(11, 13, 0);
  float picke = pick_float(e, p, 1);
  float pickp = pick_float(e, p, 0);

  printf("(%d)(%d)(%.5f)(%.5f)", pick11, pick13, picke, pickp);
  return 0;
}
