
#include "ser_cxx.h"
using namespace Triolet;

int testlist_in[3] = {-7, -11, -13};
int testlist_out[3];

float testarray_in[2][3] = { {0.5, 1, 1.5}, {2, 2.5, 3} };
float testarray_out[2][3];

int main(int argc, char **argv) {
  Triolet_init(&argc, &argv);

  // Int
  {
    int n = f_int(121);
    printf("%d\n", n);
  }

  // Tuples
  {
    Incomplete<Tuple<Tuple<Float, Bool>, Tuple<Int, Int, Int>, NoneType, Int> > mk_t;
    mk_t.allocate();
    mk_t.get<0>().get<0>() = 1.5;
    mk_t.get<0>().get<1>() = 1;
    mk_t.get<1>().get<0>() = -17;
    mk_t.get<1>().get<1>() = -19;
    mk_t.get<1>().get<2>() = -23;
    mk_t.get<2>() = NoneType();
    mk_t.get<3>() = 30;
    Tuple<Tuple<Float, Bool>, Tuple<Int, Int, Int>, NoneType, Int> t = mk_t.freeze();
    Tuple<Tuple<Float, Bool>, Tuple<Int, Int, Int>, NoneType, Int> t2 = f_tuple(t);

    printf("%.1f %d %d %d %d %d\n",
           (float)t2.get<0>().get<0>(),
           (int)t2.get<0>().get<1>(),
           (int)t2.get<1>().get<0>(),
           (int)t2.get<1>().get<1>(),
           (int)t2.get<1>().get<2>(),
           (int)t2.get<3>());
  }

  // List
  {
    List<Int> l = CreateIntList(3, testlist_in);
    FromIntList(testlist_out, f_list(l));
    printf("%d %d %d\n", testlist_out[0], testlist_out[1], testlist_out[2]);
  }

  // Array
  {
    Incomplete<Array2<Float> > mk_arr;
    mk_arr.create(0, 2, 0, 3);
    int y, x;
    for (y = 0; y < 2; y++)
      for (x = 0; x < 3; x++)
        mk_arr.at(y, x) = testarray_in[y][x];
    Array2<Float> arr = mk_arr.freeze();

    Array2<Float> arr2 = f_array(arr);

    for (y = 0; y < 2; y++)
      for (x = 0; x < 3; x++)
        printf("%.1f%s", (float)arr2.at(y, x), (y == 1 && x == 2) ? "\n" : " ");
  }

  return 0;
}
