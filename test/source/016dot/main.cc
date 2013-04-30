
#include <stdio.h>
#include "dot_cxx.h"

using namespace Triolet;

float vec1_array[] = {0.5326, -0.6400, -0.4722, 0.7948, 0.0813, -0.4773};
float vec2_array[] = {-0.1246, -0.5272, 0.1423, 0.5318, -0.2551, 0.8277};

int main()
{
  Triolet_init();
  List<Float> vec1 = CreateFloatList(6, vec1_array);
  List<Float> vec2 = CreateFloatList(6, vec2_array);
  Float prod = dotproduct(vec1, vec2);

  if (prod >= 0.2107 && prod <= 0.2108)
    printf("ok");
  else
    printf("not ok %f\n", prod);

  return 0;
}
