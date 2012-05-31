
#include <stdio.h>
#include "fhist_cxx.h"

using namespace Triolet;

// Each input is a coordinate and a value
struct Input {
  int y;
  int x;
  float value;
};

typedef Tuple<Tuple<Int, Int>, Float> TriInput;

#define N_INPUTS 10

const Input inputs[N_INPUTS] = {
  {0, 2, 0.75},
  {1, 0, 0.25},
  {0, 0, 0.5},
  {1, 2, -1},
  {1, 1, 0.0625},
  {1, 0, -0.125},
  {0, 0, 6},
  {1, 1, 3},
  {1, 0, -0.5},
  {0, 2, -0.125}
};

// Expected output at each (y, x) index.
// The output is the sum of the inputs at that index.
// These floating-point values are exact.
float outputs[2][3] = {
  {6.5, 0, 0.625},
  {-0.375, 3.0625, -1}
};

List<TriInput> make_inputs(void) {
  Incomplete<List<TriInput> > mk_list;
  mk_list.create(N_INPUTS);
  int i;
  for (i = 0; i < N_INPUTS; i++) {
    mk_list.at(i).get<0>().get<0>() = inputs[i].y;
    mk_list.at(i).get<0>().get<1>() = inputs[i].x;
    mk_list.at(i).get<1>() = inputs[i].value;
  }
  return mk_list.freeze();
}

int main()
{
  Triolet_init();
  List<TriInput> arr = make_inputs();
  Array2<Float> result = f(arr);

  // Check output
  int y, x;
  bool ok = true;
  for (y = 0; y < 2; y++) {
    for (x = 0; x < 3; x++) {
      float result_val = (Float)result.at(y, x);
      if (result_val != outputs[y][x]) ok = false;
    }
  }

  if (ok) {
    fputs("ok", stdout);
    return 0;
  } else {
    // Result does not match; print all outputs
    for (y = 0; y < 2; y++) {
      for (x = 0; x < 3; x++) {
        printf("%6f\t%6f\n", outputs[y][x], (float)(Float)result.at(y, x));
      }
    }
    return 1;
  }
}
