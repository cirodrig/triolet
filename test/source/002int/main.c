
#include "i_interface.h"

int main()
{
  Triolet_init();
  int result = int_math(8,9,10,11);
  if (result == 793)
    printf("ok");
  else
    printf("unexpected: %d\n", result);
  return 0;
}
