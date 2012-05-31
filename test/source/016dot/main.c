
#include <stdio.h>
#include "dot_interface.h"

TrioletFloat vec1_array[] = {0.5326, -0.6400, -0.4722, 0.7948, 0.0813, -0.4773};
TrioletFloat vec2_array[] = {-0.1246, -0.5272, 0.1423, 0.5318, -0.2551, 0.8277};

int main()
{
  Triolet_init();
  TrioletList *vec1 = triolet_List_Float_FromArray(6, vec1_array);
  TrioletList *vec2 = triolet_List_Float_FromArray(6, vec2_array);
  TrioletFloat prod = dotproduct(vec1, vec2);

  triolet_List_Float_Free(vec1);
  triolet_List_Float_Free(vec2);

  if (prod >= 0.2107 && prod <= 0.2108)
    printf("ok");
  else
    printf("not ok %f\n", prod);

  return 0;
}
