
#include <stdio.h>
#include <math.h>
#include "callc_interface.h"

// Create a list containing
// [exp(offset + exponent * 0) .. exp(offfset + exponent * 5)]
TrioletList *init_list(void *closure, float exponent) {
  float data[6];
  int i;
  float offset = *(float *)closure;
  for (i = 0; i < 6; i++) data[i] = exp(offset + exponent * i);
  return triolet_List_Float_FromArray(6, data);
}

// Test whether two floats are equal with 0.1% tolerance
int equal_tol(float f, float g) {
  return g > 0.999 * f && g < 1.001 * f;
}

int main() {
  Triolet_init();

  float output[6];

  // Create a list [init_list(0), init_list(1/6) .. init_list(5/6)]
  {
    float offset = -1.5f;
    TrioletClosure cb = {&init_list, &offset};
    TrioletList *out_list = f(cb);
    Triolet_List_Float_ToArray(out_list, output);
  }
  
  // Check outputs
  if (equal_tol(1.3388, output[0]) &&
      equal_tol(2.1140, output[1]) &&
      equal_tol(3.6035, output[2]) &&
      equal_tol(6.5645, output[3]) &&
      equal_tol(12.619, output[4]) &&
      equal_tol(25.283, output[5]))
    printf("ok");
  else
    printf("not ok");

  return 0;
}
  
