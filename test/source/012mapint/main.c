
#include <stdio.h>
#include "mapint_interface.h"

TrioletInt input_array[] = {2,0,3,0,4,8,1,5,4,2,4,7,8,6,8};

int main()
{
  Triolet_init();
  int i;
  TrioletList *l = triolet_List_Int_FromArray(15, input_array);
  TrioletList *l2 = listadd1(l);
  TrioletInt data[15];
  triolet_List_Int_ToArray(l2, data);

  for (i = 0; i < 15; i++) printf("%d,", data[i]);

  return 0;
}
