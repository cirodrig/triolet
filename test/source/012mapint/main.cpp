
#include <stdio.h>
#include "mapint_cxx.h"

using namespace Triolet;

TrioletInt input_array[] = {2,0,3,0,4,8,1,5,4,2,4,7,8,6,8};

int main()
{
  Triolet_init();
  int i;
  List<Int> l = CreateIntList(15, input_array);
  List<Int> l2 = listadd1(l);
  TrioletInt data[15];
  FromIntList(data, l2);

  for (i = 0; i < 15; i++) printf("%d,", data[i]);

  return 0;
}
