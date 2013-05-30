
#include <stdio.h>
#include "fib_cxx.h"

#define SIZE 20

using namespace Triolet;

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  List<Int> l = fibs(SIZE);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", (int)l.at(i));
  }

  return 0;
}
