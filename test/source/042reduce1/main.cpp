
#include <PyonData.h>
#include "seqreduce_cxx.h"
using namespace Pyon;

int main() {
  Pyon_init();
  Tuple<Int, Int> t = foo(NoneType());
  printf("%d, %d", (int)t.get<0>(), (int)t.get<1>());

  return 0;
}
