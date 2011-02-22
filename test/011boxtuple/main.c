
#include <stdio.h>
#include "boxed_interface.h"

int main()
{
  Pyon_init();
  int x = bar(9);
  printf("%d", x);
  return 0;
}
