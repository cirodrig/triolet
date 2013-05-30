
#include <stdio.h>
#include <stdlib.h>
#include <TrioletData.h>
#include <math.h>
#include "stencil_cxx.h"

#define DIMY 5
#define DIMX 4

float arr[] = {
  0.4,   0, 0,   0.4,
  0,   0, 0.8,   0,
  0,   0, 0,   0,
  0,   0, 0,   0,
  0.4,   0, 0,   0.4
};

float expected_result[] = {
  0.2, 0.1, 0.3, 0.2,
  0.1, 0.2, 0,   0.3,
  0,   0,   0.2, 0,
  0.1, 0,   0,   0.1,
  0.2, 0.1, 0.1, 0.2
};

using namespace Triolet;

Array2<Float> make_array2(int height, int width, float *data)
{
  Incomplete<Array2<Float> > arr;
  arr.create(0, height, 0, width);
  int y, x;
  for (y = 0; y < height; y++) {
    for (x = 0; x < width; x++) {
      arr.at(y, x) = (Float) data[y * width + x];
    }
  }
  return arr.freeze();
}

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

  Array2<Float> mat1 = make_array2(DIMY, DIMX, arr);
  Array2<Float> mat2 = heat(mat1);

  // Verify size of output
  //if (pyon_Matrix_PyonFloat_Height(mat2) != DIMY) return -1;
  //if (pyon_Matrix_PyonFloat_Width(mat2) != DIMX) return -1;

  // Compare against expected output
  int y, x;
  for (y = 0; y < DIMY; y++) {
    for (x = 0; x < DIMX; x++) {
      if (fabs((float)(Float)mat2.at(y, x) - expected_result[y * DIMX + x]) > 1e-5) {
        printf("Not OK");
        return 0;
      }
    }
  }
  printf("OK");
  return 0;
}
