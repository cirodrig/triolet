
#include <stdio.h>
#include "chain_cxx.h"

using namespace Triolet;

int main()
{
  Triolet_init();

  List<Int> l = f(121, 169);
  int i;
  for (i = 0; i < 2; i++)
    printf("%d,", (int)(Int)l.at(i));
  return 0;
}
