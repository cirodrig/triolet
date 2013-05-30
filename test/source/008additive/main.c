
#include <stdio.h>
#include "add_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  float f = adds_float(1.5, 3.125, 0.25);
  int i = adds_int(3, 9, 27);
  printf("(%d)(%.3f)", i, f);
  return 0;
}
