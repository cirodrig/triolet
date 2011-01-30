
#include <stdio.h>
#include "nearest_interface.h"

PyonFloat ref_array[] = {-0.798, 0.554, -0.198, 0.127, -0.689};
PyonFloat inp_array[] = {0.764, -0.07, -0.972, 0.993, -0.447, 0.221};

int main()
{
  PyonList *ref_list = pyon_List_PyonFloat_FromArray(5, ref_array);
  PyonList *inp_list = pyon_List_PyonFloat_FromArray(6, inp_array);
  PyonList *nn_list = nearest(ref_list, inp_list);
  PyonInt nn_list_data[6];

  pyon_List_PyonInt_ToArray(nn_list, nn_list_data);

  pyon_List_PyonFloat_Free(ref_list);
  pyon_List_PyonFloat_Free(inp_list);
  pyon_List_PyonInt_Free(nn_list);

  int i;
  for (i = 0; i < 6; i++) {
    printf("%d,", nn_list_data[i]);
  }
  return 0;
}
