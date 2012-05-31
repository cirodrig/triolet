
#include <stdio.h>
#include "pairwise_interface.h"

// Random points in a unit 3-ball
TrioletFloat x_coords[10] = {
  8.860380111462525e-2,
  -7.77867287578496e-2,
  0.547480095305359,
  9.957931286179911e-2,
  -0.3601525822561589,
  -9.411760561496894e-2,
  -0.748423282696964,
  0.14766362685422962,
  0.7937266921609936,
  -0.373228905809398
};

TrioletFloat y_coords[10] = {
  -0.4240137931015375,
  -9.498282803571383e-3,
  0.6771305842970337,
  0.4516891814888663,
  -0.7275522660295368,
  -0.2252140963043119,
  -1.5683518726304993e-4,
  -0.24412661330870505,
  0.28657486389544207,
  0.46424868573999234
};

TrioletFloat z_coords[10] = {
  -0.29495616450322704,
  0.2366519985340191,
  0.20904609193304696,
  0.6872986002562798,
  -3.0957500923182234e-2,
  -0.5759434617534148,
  -7.419078985093878e-2,
  0.9431492134330676,
  -0.24337809631679627,
  0.6533732220189118
};

int main() {
  Triolet_init();
  TrioletList *x_list = triolet_List_Float_FromArray(10, x_coords);
  TrioletList *y_list = triolet_List_Float_FromArray(10, y_coords);
  TrioletList *z_list = triolet_List_Float_FromArray(10, z_coords);

  TrioletFloat energy = compute_energy(x_list, y_list, z_list);
  triolet_List_Float_Free(x_list);
  triolet_List_Float_Free(y_list);
  triolet_List_Float_Free(z_list);

  if (energy < 56.59 || energy > 56.60)
    printf("not ok");
  else
    printf("ok");
  return 0;
}
