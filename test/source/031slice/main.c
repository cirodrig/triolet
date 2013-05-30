
#include <triolet.h>
#include <stdio.h>

#include "slice_interface.h"

int data[] = {30, 47, 31, 33, 2, 41, 25};

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

  TrioletList *lst = triolet_List_Int_FromArray(7, data);
  int sum = parity(lst);
  triolet_Matrix_Int_Free(lst);

  // Check output
  printf("%d", sum);

  return 0;
}
