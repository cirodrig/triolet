
#include <stdio.h>
#include <stdlib.h>
#include <pyon.h>
#include "matmul_interface.h"

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

int main()
{
  Pyon_init();

  PyonMatrix *mat1 = pyon_Matrix_PyonFloat_FromArray(DIM1, DIM2, arr1);
  PyonMatrix *mat2 = pyon_Matrix_PyonFloat_FromArray(DIM2, DIM3, arr2);
  PyonMatrix *mat3 = mm(mat1, mat2);
  pyon_Matrix_PyonFloat_Free(mat1);
  pyon_Matrix_PyonFloat_Free(mat2);

  // Verify height of matrix product
  if (pyon_Matrix_PyonFloat_Height(mat3) != DIM1) return -1;
  if (pyon_Matrix_PyonFloat_Width(mat3) != DIM3) return -1;

  // Get matrix data
  float *data = malloc(DIM1 * DIM3 * sizeof(int));
  pyon_Matrix_PyonFloat_ToArray(mat3, data);
  pyon_Matrix_PyonFloat_Free(mat3);

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
