
#include <stdio.h>
#include "zips_cxx.h"

// Some random numbers.  'xs' has 5 values, other lists have 6.
int xs[] = {58, 95, 6, 11, 44};
int ys[] = {57, 85, 8, 84, 82, 94};
int zs[] = {59, 23, 43, 38, 34, 23};
int ws[] = {55, 100, 64, 36, 98, 75};

int expect_outs1[] = {4,1,-1,0,6};
int expect_outs2[] = {-1, 0, -1, 1, -3};
int expect_outs3[] = {28, -3, -1, 47, -2};
int expect_outs4[] = {-39, 21, 0, 4, 2};

using namespace Triolet;

int main()
{
  Triolet_init();
  List<Int> pxs = CreateIntList(5, xs);
  List<Int> pys = CreateIntList(6, ys);
  List<Int> pzs = CreateIntList(6, zs);
  List<Int> pws = CreateIntList(6, ws);

  // Compute values.  Put 'xs' in different positions to test the
  // termination check inside the zip functions.
  List<Int> outs1 = zips3(pws, pxs, pzs);
  List<Int> outs2 = zips3(pxs, pws, pys);
  List<Int> outs3 = zips4(pxs, pys, pzs, pws);
  List<Int> outs4 = zips4(pys, pzs, pws, pxs);

  int i;
  TrioletInt tmp[5];

  // Check results
  FromIntList(tmp, outs1);
  for (i = 0; i < 5; i++) {
    if (expect_outs1[i] != tmp[i]) {
      printf("Error in part 1\n");
      break;
    }
  }

  FromIntList(tmp, outs2);
  for (i = 0; i < 5; i++) {
    if (expect_outs2[i] != tmp[i]) {
      printf("Error in part 2\n");
      break;
    }
  }

  FromIntList(tmp, outs3);
  for (i = 0; i < 5; i++) {
    if (expect_outs3[i] != tmp[i]) {
      printf("Error in part 3\n");
      break;
    }
  }

  FromIntList(tmp, outs4);
  for (i = 0; i < 5; i++) {
    if (expect_outs4[i] != tmp[i]) {
      printf("Error in part 4\n");
      break;
    }
  }

  printf("done");

  return 0;
}
