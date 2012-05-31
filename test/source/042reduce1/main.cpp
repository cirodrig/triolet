
#include "seqreduce_cxx.h"
using namespace Triolet;

int main() {
  Triolet_init();
  Tuple<Int, Int> t = foo(NoneType());
  printf("%d, %d", (int)t.get<0>(), (int)t.get<1>());

  return 0;
}
