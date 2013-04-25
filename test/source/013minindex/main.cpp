
#include <stdio.h>
#include "minindex_cxx.h"
using namespace Triolet;

// The test kernel looks for the least element of this list
float input_array[] =
  {0.75, 2.0, 2.5, 1.3, -0.1,
   0, 3, 0.4, 1, 2};

int main()
{
  Triolet_init();
  List<Float> l = CreateFloatList(10, input_array);
  Int ix = min_float(l);

  printf("%d", (int)ix);

  return 0;
}
