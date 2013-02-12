
#include <triolet.h>
#include <stdio.h>

#include "test_cxx.h"

using namespace Triolet;

float data[] = {
  3.0, 4.0, 5.0,
  1.5, 2.5, 3.5,
  0.0, 1.0, 2.0};

int main()
{
  float data2[9];
  Triolet_init();

  Array2<Float> mat;
  {
    Incomplete<Array2<Float> > mk_mat;
    mk_mat.create(0, 3, 0, 3);
    for (int y = 0; y < 3; y++) {
      for (int x = 0; x < 3; x++) {
        mk_mat.at(y, x) = data[3*y + x];
      }
    }
    mat = mk_mat.freeze();
  }
  Array2<Float> mat2 = test(mat);

  // Check output
  int ok = 1;
  {
    for (int y = 0; y < 3; y++) {
      for (int x = 0; x < 3; x++) {
        if (mat2.at(y,x) != data[3*y+x] + 1.0f) ok = 0;
      }
    }
  }

  fputs(ok ? "yes" : "no", stdout);

  return 0;
}
