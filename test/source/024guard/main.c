
#include <stdio.h>
#include "sumpos_interface.h"

TrioletInt values[] = {-5, 3, 21, -18, -40, 9, 0, 14};
int main() {
  Triolet_init();
  TrioletList *l = triolet_List_Int_FromArray(8, values);
  TrioletInt sum = sumpos(l);
  triolet_List_Int_Free(l);
  printf("%d", sum);
  return 0;
}
