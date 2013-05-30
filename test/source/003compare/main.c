
#include "compare_interface.h"

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);
  int x1_true  = compare(1, 1, 0.5, 0.5);
  int x2_false = compare(1, 1, 0.5, 1.5);
  int x3_false = compare(1, 1, 0.5, -0.5);
  int x4_false = compare(1, 3, 0.5, 0.5);
  int x5_true  = compare(1, 3, 0.5, 1.5);
  int x6_false = compare(1, 3, 0.5, -0.5);
  int x7_false = compare(4, 2, 0.5, 0.5);
  int x8_false = compare(4, 2, 0.5, 1.5);
  int x9_true  = compare(4, 2, 0.5, -0.5);

  if (x1_true && !x2_false && !x3_false && !x4_false && x5_true &&
      !x6_false && !x7_false && !x8_false && x9_true)
    printf("ok");
  else
    printf("not ok");
  return 0;
}
