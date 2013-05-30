
#include <inttypes.h>
#include "triolet.h"

int32_t testfoo_wrapper(int32_t, int32_t, int32_t);

int main(int argc, char **argv) {
  Triolet_init(&argc, &argv);
  testfoo_wrapper(0, 1, 2);
  return 0;
}
