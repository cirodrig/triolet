
#include <stdio.h>
#include "minindex_interface.h"

// The test kernel looks for the least element of this list
TrioletFloat input_array[] =
  {0.75, 2.0, 2.5, 1.3, -0.1,
   0, 3, 0.4, 1, 2};

int main()
{
  Triolet_init();
  TrioletList *l = triolet_List_Int_FromArray(10, input_array);
  TrioletInt ix = min_float(l);
  triolet_List_Int_Free(l);

  printf("%d", ix);

  return 0;
}
