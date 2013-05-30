
#include <stdio.h>
#include "function_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  int n = doubled(21);
  printf("%d", n);
  return 0;
}
