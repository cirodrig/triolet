
#include <stdio.h>
#include "fib_interface.h"

#define SIZE 20

int main()
{
  Pyon_init();
  PyonList *l = fibs(SIZE);
  PyonInt data[SIZE];

  pyon_List_PyonInt_ToArray(l, data);
  pyon_List_PyonInt_Free(l);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", data[i]);
  }

  return 0;
}
