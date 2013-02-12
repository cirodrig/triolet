
#include <triolet.h>
#include <stdio.h>

#include "test_cxx.h"

using namespace Triolet;

int data[] = {
  3, 4, 5,
  0, 1, 2,
  -3, -2, -1};

int main()
{
  Triolet_init();

  Array2<Int> mat;
  {
    Incomplete<Array2<Int> > mk_mat;
    mk_mat.create(0, 3, 0, 3);
    for (int y = 0; y < 3; y++) {
      for (int x = 0; x < 3; x++) {
        mk_mat.at(y,x) = data[3*y+x];
      }
    }
    mat = mk_mat.freeze();
  }
  int sum = test(mat);

  // Check output
  printf("%d", sum);

  return 0;
}
