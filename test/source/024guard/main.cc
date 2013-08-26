
#include <stdio.h>
#include "sumpos_cxx.h"

using namespace Triolet;

int values[] = {-5, 3, 21, -18, -40, 9, 0, 14};
int main(int argc, char **argv) {
  Triolet_init(&argc, &argv);
  List<Int> l = CreateIntList(8, values);
  Int sum = sumpos(l);
  printf("%d", (int)sum);
  return 0;
}
