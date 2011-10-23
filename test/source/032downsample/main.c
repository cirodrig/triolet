
#include <stdio.h>
#include <stdlib.h>
#include <pyon.h>
#include "downsample_interface.h"

int arr[] = {
  255, 212, 86, 81, 77, 112,
  255, 253, 145, 90, 88, 91,
  255, 255, 180, 102, 86, 98,
  253, 219, 154, 160, 85, 88
};

int main()
{
  Pyon_init();

  PyonMatrix *mat = pyon_Matrix_PyonInt_FromArray(0, 4, 0, 6, arr);
  PyonMatrix *mat2 = downsample(mat);

  int w, h;
  int *data;
  h = pyon_Matrix_PyonInt_Height(mat2);
  w = pyon_Matrix_PyonInt_Width(mat2);
  data = malloc(w * h * sizeof(int));
  pyon_Matrix_PyonInt_ToArray(mat2, data);

  int y, x;
  for (y = 0; y < h; y++) {
    for (x = 0; x < w; x++) {
      printf("%d ", data[y * w + x]);
    }
  }
  return 0;
}
