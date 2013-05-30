
#include <stdio.h>
#include <stdlib.h>
#include "downsample_cxx.h"

#define SIZE_Y 4
#define SIZE_X 6

int arr[] = {
  255, 212, 86, 81, 77, 112,
  255, 253, 145, 90, 88, 91,
  255, 255, 180, 102, 86, 98,
  253, 219, 154, 160, 85, 88
};

using namespace Triolet;

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

  Array2<Int> mat;
  {
    Incomplete<Array2<Int> > mk_arr;
    mk_arr.create(0, SIZE_Y, 0, SIZE_X);
    for (int y = 0; y < SIZE_Y; y++) {
      for (int x = 0; x < SIZE_X; x++) {
        mk_arr.at(y,x) = arr[y*SIZE_X + x];
      }
    }
    mat = mk_arr.freeze();
  }

  Array2<Int> mat2 = downsample(mat);

  int y, x;
  for (y = 0; y < SIZE_Y; y += 2) {
    for (x = 0; x < SIZE_X; x += 2) {
      printf("%d ", (int)mat2.at(y,x));
    }
  }
  return 0;
}
