
#include <stdio.h>
#include "hist_cxx.h"
#include <pyon.h>
#include <PyonData.h>

using namespace Pyon;

struct Input {
  int z;
  int y;
  int x;
  float value;
};

typedef Tuple<Int, Int, Int, Float> PyonInput;

#define NUM_INPUTS 10

const Input inputs[NUM_INPUTS] = {
  { 0, -1, -2, 0.5 },
  { 0, 1, -1, 0.5 },
  { 3, 1, 0, -2.5 },
  { 2, 1, 1, -0.25 },
  { 1, -2, -2, -3 },
  { 2, 2, 0, -1 },
  { 1, 0, -1, 0.25 },
  { 2, -2, -2, -1 },
  { 0, -1, 1, 1.25 },
  { 2, 1, 1, 0.5 }
};

// Expected output values.
// expected_outputs[z][y][x] == outputs.at(z, y-2, x-2)

float expected_outputs[4][5][5] = {
  { { 0,    0,    0,    0,    0 },
    { 0.5,  0,    0,    1.25, 0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0.5,  0,    0,    0 },
    { 0,    0,    0,    0,    0 } },
  { { -3,   0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0.25, 0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 } },
  { { -1,   0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0,    0,    0.25, 0 },
    { 0,    0,    -1,   0,    0 } },
  { { 0,    0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0,    0,    0,    0 },
    { 0,    0,    -2.5, 0,    0 },
    { 0,    0,    0,    0,    0 } }
};

List<PyonInput> make_inputs(void) {
  Incomplete<List<PyonInput> > a;
  a.create(NUM_INPUTS);
  int i;
  for (i = 0; i < NUM_INPUTS; i++) {
    Incomplete<PyonInput> e = a.at(i);
    e.get<0>() = (Int)inputs[i].z;
    e.get<1>() = (Int)inputs[i].y;
    e.get<2>() = (Int)inputs[i].x;
    e.get<3>() = (Float)inputs[i].value;
  }
  return a.freeze();
}

int main()
{
  GC_INIT();

  List<PyonInput> a = make_inputs();
  Array3<Float> outputs = f(a);

  int z, y, x;
  for (z = 0; z < 4; z++) {
    for (y = -2; y < 3; y++) {
      for (x = -2; x < 3; x++) {
        float o = (Float)outputs.at(z, y, x);
        if (expected_outputs[z][y+2][x+2] != o) {
          // Print the incorrect value
          printf("%d, %d, %d: %f\n", z, y, x, o);
          return 1;
          }
      }
    }
  }
  printf("Ok");
  return 0;
}
