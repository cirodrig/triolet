
#include <stdio.h>
#include "nearest_cxx.h"

float ref_array[] = {-0.798, 0.554, -0.198, 0.127, -0.689};
float inp_array[] = {0.764, -0.07, -0.972, 0.993, -0.447, 0.221};

using namespace Triolet;

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  List<Float> ref_list = CreateFloatList(5, ref_array);
  List<Float> inp_list = CreateFloatList(6, inp_array);
  List<Int> nn_list = nearest(ref_list, inp_list);
  int nn_list_data[6];

  FromIntList(nn_list_data, nn_list);

  int i;
  for (i = 0; i < 6; i++) {
    printf("%d,", nn_list_data[i]);
  }
  return 0;
}
