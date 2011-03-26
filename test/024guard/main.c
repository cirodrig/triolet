
#include <stdio.h>
#include "sumpos_interface.h"

PyonInt values[] = {-5, 3, 21, -18, -40, 9, 0, 14};
int main() {
  Pyon_init();
  PyonList *l = pyon_List_PyonInt_FromArray(8, values);
  PyonInt sum = sumpos(l);
  pyon_List_PyonInt_Free(l);
  printf("%d", sum);
  return 0;
}
