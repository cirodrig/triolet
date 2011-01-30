
#include <stdio.h>
#include "remainder_interface.h"

int main()
{
  PyonInt n = remainder_int(667, 37);
  PyonFloat f = remainder_float(71.707, 32.45);

  if (n == 668 && 78.513 < f && f < 78.515) printf("ok");
  else printf("not ok");
  return 0;
}
