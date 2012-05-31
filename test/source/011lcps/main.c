
#include <inttypes.h>
#include "triolet.h"

int32_t testfoo(int32_t, int32_t, int32_t);

int main() {
  Triolet_init();
  testfoo(0, 1, 2);
  return 0;
}
