
#include <stdio.h>
#include "zips_interface.h"

// Some random numbers.  'xs' has 5 values, other lists have 6.
PyonInt xs[] = {58, 95, 6, 11, 44};
PyonInt ys[] = {57, 85, 8, 84, 82, 94};
PyonInt zs[] = {59, 23, 43, 38, 34, 23};
PyonInt ws[] = {55, 100, 64, 36, 98, 75};

PyonInt expect_outs1[] = {4,1,-1,0,6};
PyonInt expect_outs2[] = {-1, 0, -1, 1, -3};
PyonInt expect_outs3[] = {28, -3, -1, 47, -2};
PyonInt expect_outs4[] = {-39, 21, 0, 4, 2};

int main()
{
  Pyon_init();
  PyonList *pxs = pyon_List_PyonInt_FromArray(5, xs);
  PyonList *pys = pyon_List_PyonInt_FromArray(6, ys);
  PyonList *pzs = pyon_List_PyonInt_FromArray(6, zs);
  PyonList *pws = pyon_List_PyonInt_FromArray(6, ws);

  // Compute values.  Put 'xs' in different positions to test the
  // termination check inside the zip functions.
  PyonList *outs1 = zips3(pws, pxs, pzs);
  PyonList *outs2 = zips3(pxs, pws, pys);
  PyonList *outs3 = zips4(pxs, pys, pzs, pws);
  PyonList *outs4 = zips4(pys, pzs, pws, pxs);

  pyon_List_PyonInt_Free(pxs);
  pyon_List_PyonInt_Free(pys);
  pyon_List_PyonInt_Free(pzs);
  pyon_List_PyonInt_Free(pws);

  int i;
  PyonInt tmp[5];

  // Check results
  pyon_List_PyonInt_ToArray(outs1, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs1[i] != tmp[i]) {
      printf("Error in part 1\n");
      break;
    }
  }

  pyon_List_PyonInt_ToArray(outs2, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs2[i] != tmp[i]) {
      printf("Error in part 2\n");
      break;
    }
  }

  pyon_List_PyonInt_ToArray(outs3, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs3[i] != tmp[i]) {
      printf("Error in part 3\n");
      break;
    }
  }

  pyon_List_PyonInt_ToArray(outs4, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs4[i] != tmp[i]) {
      printf("Error in part 4\n");
      break;
    }
  }

  pyon_List_PyonInt_Free(outs1);
  pyon_List_PyonInt_Free(outs2);
  pyon_List_PyonInt_Free(outs3);
  pyon_List_PyonInt_Free(outs4);

  printf("done");

  return 0;
}
