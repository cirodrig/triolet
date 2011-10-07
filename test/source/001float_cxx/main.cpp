
#include <iostream>
#include "f_cxx.h"

int main()
{
  Pyon_init();
  float result = float_math(0.5, 0.6, 0.7, 0.8);
  if (result > -0.1111 && result < -0.1109)
    cout<<"ok";
  else
    cout<<"unexpected: "<< result <<"\n";
  return 0;

}
