
#include <stdio.h>
#include "mapint_interface.h"

PyonInt input_array[] = {2,0,3,0,4,8,1,5,4,2,4,7,8,6,8};

int main()
{
  int i;
  PyonList *l = pyon_List_PyonInt_FromArray(15, input_array);
  PyonList *l2 = listadd1(l);
  PyonInt data[15];
  pyon_List_PyonInt_ToArray(l2, data);

  for (i = 0; i < 15; i++) printf("%d,", data[i]);

  return 0;
}
