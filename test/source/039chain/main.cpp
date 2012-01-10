
#include <stdio.h>
#include "chain_cxx.h"
#include <pyon.h>
#include <PyonData.h>

using namespace Pyon;

int main()
{
  GC_INIT();

  List<Int> l = f(121, 169);
  int i;
  for (i = 0; i < 2; i++)
    printf("%d,", (int)(Int)l.at(i));
  return 0;
}
