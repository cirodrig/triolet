
#include "divtest_cxx.h"
using namespace Triolet;

// Each column will be tested for divisibility by another number.
// The columns will be tested against [2,3,5,7].
// All numbers in the first and third columns pass their divisibility test.
// The second and fourth columns contain some non-divisible numbers.
int numbers[] = {
  26, 60, 50, 41,
  50, 31, 40, 49,
  32, 72, 10, 14
  };

// Column indices associated with numbers[]
int indices[] =
  {0,1,2,3,0,1,2,3,0,1,2,3};

int main(int argc, char **argv) {
  Triolet_init(&argc, &argv);
  List<Int> t_numbers = CreateIntList(12, numbers);
  List<Int> t_columns = CreateIntList(12, indices);
  List<Bool> divs = divisibility_check(t_numbers, t_columns);

  int i;
  for (i = 0; i < divs.len(); i++) {
    printf("%d,", (int)divs.at(i));
  }

  return 0;
}
