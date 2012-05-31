
#include <triolet.h>
#include <stdio.h>

#include "test_interface.h"

float data[] = {
  3.0, 4.0, 5.0,
  1.5, 2.5, 3.5,
  0.0, 1.0, 2.0};

int main()
{
  float data2[9];
  Triolet_init();

  TrioletMatrix *mat = triolet_Matrix_Float_FromArray(0, 3, 0, 3, data);
  TrioletMatrix *mat2 = test(mat);
  triolet_Matrix_Float_ToArray(mat2, data2);
  triolet_Matrix_Float_Free(mat);
  triolet_Matrix_Float_Free(mat2);

  // Check output
  int i;
  int ok = 1;
  for (i = 0; i < 9; i++) {
    if (data2[i] != data[i] + 1.0f) ok = 0;
  }

  fputs(ok ? "yes" : "no", stdout);

  return 0;
}
