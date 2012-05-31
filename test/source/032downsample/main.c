
#include <stdio.h>
#include <stdlib.h>
#include <triolet.h>
#include "downsample_interface.h"

int arr[] = {
  255, 212, 86, 81, 77, 112,
  255, 253, 145, 90, 88, 91,
  255, 255, 180, 102, 86, 98,
  253, 219, 154, 160, 85, 88
};

int main()
{
  Triolet_init();

  TrioletMatrix *mat = triolet_Matrix_Int_FromArray(0, 4, 0, 6, arr);
  TrioletMatrix *mat2 = downsample(mat);

  int w, h;
  int *data;
  h = triolet_Matrix_Int_Height(mat2);
  w = triolet_Matrix_Int_Width(mat2);
  data = malloc(w * h * sizeof(int));
  triolet_Matrix_Int_ToArray(mat2, data);

  int y, x;
  for (y = 0; y < h; y++) {
    for (x = 0; x < w; x++) {
      printf("%d ", data[y * w + x]);
    }
  }
  return 0;
}
