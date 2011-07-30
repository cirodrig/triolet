
#include <pyon.h>
#include <stdio.h>

#include "slice_interface.h"

int data[] = {30, 47, 31, 33, 2, 41, 25};

int main()
{
  Pyon_init();

  PyonList *lst = pyon_List_PyonInt_FromArray(7, data);
  int sum = parity(lst);
  pyon_Matrix_PyonInt_Free(lst);

  // Check output
  printf("%d", sum);

  return 0;
}
