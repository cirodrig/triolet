
#include <stdio.h>
#include "nested_interface.h"

// Some random numbers.
PyonFloat xs[] = {5.7, 0.5, 0.8, 2.4, 2.2, 3.4};
PyonFloat ys[] = {5.9, 2.3, 4.3, 3.8, 3.4, 2.3};

int main()
{
  Pyon_init();
  PyonList *pxs = pyon_List_PyonFloat_FromArray(6, xs);
  PyonList *pys = pyon_List_PyonFloat_FromArray(6, ys);

  // Compute sum [sin(x) * sin(y) | x <- xs, y <- ys]
  PyonFloat f = nred(pxs, pys);

  pyon_List_PyonInt_Free(pxs);
  pyon_List_PyonInt_Free(pys);

  if (f >= -1.24849 && f <= -1.24848)
    printf("ok");
  else
    printf("not ok");
  
  return 0;
}