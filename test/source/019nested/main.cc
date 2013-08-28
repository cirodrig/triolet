
#include <stdio.h>
#include "nested_cxx.h"

using namespace Triolet;

// Some random numbers.
float xs[] = {5.7, 0.5, 0.8, 2.4, 2.2, 3.4};
float ys[] = {5.9, 2.3, 4.3, 3.8, 3.4, 2.3};

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  List<Float> pxs = CreateFloatList(6, xs);
  List<Float> pys = CreateFloatList(6, ys);

  // Compute sum [sin(x) * sin(y) | x <- xs, y <- ys]
  float f = nred(pxs, pys);

  if (f >= -1.24849 && f <= -1.24848)
    printf("ok");
  else
    printf("not ok");
  
  return 0;
}
