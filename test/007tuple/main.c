
#include <stdio.h>
#include "tuples_interface.h"

int main()
{
  int u = tuples(11,13,17,19, 0, 0);
  int v = tuples(23,29,31,37, 0, 1);
  int w = tuples(41,43,47,53, 1, 0);
  int x = tuples(59,61,67,71, 1, 1);
  printf("(%d)(%d)(%d)(%d)", u,v,w,x);

  return 0;
}
