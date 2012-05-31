
#include <triolet.h>
#include <stdio.h>

#include "test_interface.h"

int data[] = {
  3, 4, 5,
  0, 1, 2,
  -3, -2, -1};

int main()
{
  Triolet_init();

  TrioletMatrix *mat = triolet_Matrix_Int_FromArray(0, 3, 0, 3, data);
  int sum = test(mat);
  triolet_Matrix_Int_Free(mat);

  // Check output
  printf("%d", sum);

  return 0;
}
