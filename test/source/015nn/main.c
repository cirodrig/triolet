
#include <stdio.h>
#include "nearest_interface.h"

TrioletFloat ref_array[] = {-0.798, 0.554, -0.198, 0.127, -0.689};
TrioletFloat inp_array[] = {0.764, -0.07, -0.972, 0.993, -0.447, 0.221};

int main()
{
  Triolet_init();
  TrioletList *ref_list = triolet_List_Float_FromArray(5, ref_array);
  TrioletList *inp_list = triolet_List_Float_FromArray(6, inp_array);
  TrioletList *nn_list = nearest(ref_list, inp_list);
  TrioletInt nn_list_data[6];

  triolet_List_Int_ToArray(nn_list, nn_list_data);

  triolet_List_Float_Free(ref_list);
  triolet_List_Float_Free(inp_list);
  triolet_List_Int_Free(nn_list);

  int i;
  for (i = 0; i < 6; i++) {
    printf("%d,", nn_list_data[i]);
  }
  return 0;
}
