
#include <stdio.h>
#include "tuples_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  int u = tuples(121, 77, 0);
  int v = tuples(121, 77, 1);
  printf("(%d)(%d)", u,v);

  return 0;
}
