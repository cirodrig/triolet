
#include <stdio.h>
#include "nested_interface.h"

// Some random numbers.
TrioletFloat xs[] = {5.7, 0.5, 0.8, 2.4, 2.2, 3.4};
TrioletFloat ys[] = {5.9, 2.3, 4.3, 3.8, 3.4, 2.3};

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  TrioletList *pxs = triolet_List_Float_FromArray(6, xs);
  TrioletList *pys = triolet_List_Float_FromArray(6, ys);

  // Compute sum [sin(x) * sin(y) | x <- xs, y <- ys]
  TrioletFloat f = nred(pxs, pys);

  triolet_List_Int_Free(pxs);
  triolet_List_Int_Free(pys);

  if (f >= -1.24849 && f <= -1.24848)
    printf("ok");
  else
    printf("not ok");
  
  return 0;
}
