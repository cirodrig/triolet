
#include <stdio.h>
#include "histo_interface.h"

#define SIZE 21

int main()
{
  Pyon_init();
  PyonList *l = histo(100);
  PyonInt data[SIZE];

  pyon_List_PyonInt_ToArray(l, data);
  pyon_List_PyonInt_Free(l);

  int i;
  for (i = 0; i < SIZE; i++) {
    printf("%d,", data[i]);
  }

  return 0;
}
