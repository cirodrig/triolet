
#include <stdio.h>
#include "function_interface.h"

int main()
{
  Triolet_init();
  int n = doubled(21);
  printf("%d", n);
  return 0;
}
