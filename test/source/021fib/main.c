
#include <stdio.h>
#include "fib_interface.h"

#define SIZE 20

int main()
{
  Triolet_init();
  TrioletList *l = fibs(SIZE);
  TrioletInt data[SIZE];

  triolet_List_Int_ToArray(l, data);
  triolet_List_Int_Free(l);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", data[i]);
  }

  return 0;
}
