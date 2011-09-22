
#include <pyon.h>
#include <stdio.h>

#include "test_interface.h"

int data[] = {
  3, 4, 5,
  0, 1, 2,
  -3, -2, -1};

int main()
{
  Pyon_init();

  PyonMatrix *mat = pyon_Matrix_PyonInt_FromArray(0, 3, 0, 3, data);
  int sum = test(mat);
  pyon_Matrix_PyonInt_Free(mat);

  // Check output
  printf("%d", sum);

  return 0;
}
