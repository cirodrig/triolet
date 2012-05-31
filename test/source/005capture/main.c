
#include <stdio.h>
#include "capture_interface.h"

int main()
{
  Triolet_init();
  float f = capture(1.75, 2, 3);
  if (f == 0.3125)
    printf("ok");
  else
    printf("unexpected %f\n", f);
  return 0;
}
