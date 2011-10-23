
#include <stdio.h>
#include <stdlib.h>
#include <pyon.h>
#include <math.h>
#include "stencil_interface.h"

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

int main()
{
  Pyon_init();

  PyonMatrix *mat1 = pyon_Matrix_PyonFloat_FromArray(0, DIMY, 0, DIMX, arr);
  PyonMatrix *mat2 = heat(mat1);
  pyon_Matrix_PyonFloat_Free(mat1);

  // Verify size of output
  if (pyon_Matrix_PyonFloat_Height(mat2) != DIMY) return -1;
  if (pyon_Matrix_PyonFloat_Width(mat2) != DIMX) return -1;

  // Get matrix data
  float *data = malloc(DIMY * DIMX * sizeof(int));
  pyon_Matrix_PyonFloat_ToArray(mat2, data);
  pyon_Matrix_PyonFloat_Free(mat2);

  // Compare against expected output
  int y, x;
  for (y = 0; y < DIMY; y++) {
    for (x = 0; x < DIMX; x++) {
      if (fabs(data[y * DIMX + x] - expected_result[y * DIMX + x]) > 1e-5) {
        printf("Not OK");
        return 0;
      }
    }
  }
  printf("OK");
  return 0;
}
