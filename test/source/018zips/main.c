
#include <stdio.h>
#include "zips_interface.h"

// Some random numbers.  'xs' has 5 values, other lists have 6.
TrioletInt xs[] = {58, 95, 6, 11, 44};
TrioletInt ys[] = {57, 85, 8, 84, 82, 94};
TrioletInt zs[] = {59, 23, 43, 38, 34, 23};
TrioletInt ws[] = {55, 100, 64, 36, 98, 75};

TrioletInt expect_outs1[] = {4,1,-1,0,6};
TrioletInt expect_outs2[] = {-1, 0, -1, 1, -3};
TrioletInt expect_outs3[] = {28, -3, -1, 47, -2};
TrioletInt expect_outs4[] = {-39, 21, 0, 4, 2};

int main()
{
  Triolet_init();
  TrioletList *pxs = triolet_List_Int_FromArray(5, xs);
  TrioletList *pys = triolet_List_Int_FromArray(6, ys);
  TrioletList *pzs = triolet_List_Int_FromArray(6, zs);
  TrioletList *pws = triolet_List_Int_FromArray(6, ws);

  // Compute values.  Put 'xs' in different positions to test the
  // termination check inside the zip functions.
  TrioletList *outs1 = zips3(pws, pxs, pzs);
  TrioletList *outs2 = zips3(pxs, pws, pys);
  TrioletList *outs3 = zips4(pxs, pys, pzs, pws);
  TrioletList *outs4 = zips4(pys, pzs, pws, pxs);

  triolet_List_Int_Free(pxs);
  triolet_List_Int_Free(pys);
  triolet_List_Int_Free(pzs);
  triolet_List_Int_Free(pws);

  int i;
  TrioletInt tmp[5];

  // Check results
  triolet_List_Int_ToArray(outs1, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs1[i] != tmp[i]) {
      printf("Error in part 1\n");
      break;
    }
  }

  triolet_List_Int_ToArray(outs2, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs2[i] != tmp[i]) {
      printf("Error in part 2\n");
      break;
    }
  }

  triolet_List_Int_ToArray(outs3, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs3[i] != tmp[i]) {
      printf("Error in part 3\n");
      break;
    }
  }

  triolet_List_Int_ToArray(outs4, tmp);
  for (i = 0; i < 5; i++) {
    if (expect_outs4[i] != tmp[i]) {
      printf("Error in part 4\n");
      break;
    }
  }

  triolet_List_Int_Free(outs1);
  triolet_List_Int_Free(outs2);
  triolet_List_Int_Free(outs3);
  triolet_List_Int_Free(outs4);

  printf("done");

  return 0;
}
