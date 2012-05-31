
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "matmul_cxx.h"

using namespace Triolet;

#define DIM1 2
#define DIM2 3
#define DIM3 4

// DIM2 by DIM1 array
float arr1[] = {
  0.3, 0.6, 0.2,
  -0.1, 0.1, 1
};

// DIM3 by DIM2 array
float arr2[] = {
  0.2, 0.3, 1.2, 1.3,
  0.6, 0.7, 0.8, 0.9,
  1.0, 1.1, 0.4, 0.5
};

// DIM3 by DIM1 array
float arr3[] = {
  0.62, 0.73, 0.92, 1.03,
  1.04, 1.14, 0.36, 0.46
};

BArray2<Float> make_matrix(int height, int width, float *data) {
  Incomplete<BArray2<Float> >arr;
  arr.create(0, height, 0, width);
  int y, x;
  for (y = 0; y < height; y++)
    for (x = 0; x < width; x++)
      arr.at(y, x) = (Boxed<Stored<Float> >)(Float)*data++;
  return arr.freeze();
}

void from_matrix(int height, int width, float *data, BArray2<Float> mat) {
  int y, x;
  for (y = 0; y < height; y++)
    for (x = 0; x < width; x++)
      *data++ = (Float) mat.at(y, x);
}

int main()
{
  Triolet_init();

  BArray2<Float> mat1 = make_matrix(DIM1, DIM2, arr1);
  BArray2<Float> mat2 = make_matrix(DIM2, DIM3, arr2);
  BArray2<Float> mat3 = mm(mat1, mat2);

  // Get matrix data
  float *data = (float *)malloc(DIM1 * DIM3 * sizeof(int));
  from_matrix(DIM1, DIM3, data, mat3);

  // Compare against expected output
  int y, x;
  for (y = 0; y < DIM1; y++) {
    for (x = 0; x < DIM3; x++) {
      if (fabs(data[y * DIM3 + x] - arr3[y * DIM3 + x]) > 1e-5) {
        printf("Not OK");
        return 0;
      }
    }
  }
  printf("OK");
  return 0;
}
