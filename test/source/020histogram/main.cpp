
#include <stdio.h>
#include "histo_cxx.h"

#define SIZE 21

using namespace Triolet;

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  List<Int> lst = histo(100);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", (int)(Int)lst.at(i));
  }

  return 0;
}
