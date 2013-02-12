
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "matmul_cxx.h"

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

using namespace Triolet;

Array2<Float> marshalArray(int ysize, int xsize, float *arr)
{
  Incomplete<Array2<Float> > mk_arr;
  mk_arr.create(0, ysize, 0, xsize);
  for (int y = 0; y < ysize; y++) {
    for (int x = 0; x < xsize; x++) {
      mk_arr.at(y,x) = arr[y*xsize + x];
    }
  }
  return mk_arr.freeze();
}

int main()
{
  Triolet_init();

  Array2<Float> mat1 = marshalArray(DIM1, DIM2, arr1);
  Array2<Float> mat2 = marshalArray(DIM2, DIM3, arr2);
  Array2<Float> mat3 = mm(mat1, mat2);

  // Verify height of matrix product
  //if (triolet_Matrix_Float_Height(mat3) != DIM1) return -1;
  //if (triolet_Matrix_Float_Width(mat3) != DIM3) return -1;

  // Compare against expected output
  int y, x;
  for (y = 0; y < DIM1; y++) {
    for (x = 0; x < DIM3; x++) {
      float computed = mat3.at(y,x);
      float expected = arr3[y*DIM3+x];
      if (fabs(computed - expected) > 1e-5) {
        printf("Not OK");
        return 0;
      }
    }
  }
  printf("OK");
  return 0;
}
