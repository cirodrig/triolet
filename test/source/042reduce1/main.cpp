
#include "seqreduce_cxx.h"
using namespace Triolet;

int main(int argc, char **argv) {
  Triolet_init(&argc, &argv);
  Tuple<Int, Int> t = foo(NoneType());
  printf("%d, %d", (int)t.get<0>(), (int)t.get<1>());

  return 0;
}
