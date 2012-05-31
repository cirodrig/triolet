
#include <stdio.h>
#include "histo_cxx.h"

#define SIZE 21

using namespace Triolet;

int main()
{
  Triolet_init();
  Array1<Int> arr = histo(100);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", (int)(Int)arr.at(i));
  }

  return 0;
}
