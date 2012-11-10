
#include "permute_cxx.h"
using namespace Triolet;

/* For each (k, v), write value v into index k.
 * Result should be [4, 3, 1, 6, 2, 5]
 * */
struct {int k; int v;} data[] =
  { {5, 5}, {2, 1}, {4, 2}, {3, 6}, {1, 3}, {0, 4} };

List<Tuple<Int, Int> >
make_list(void)
{
  Incomplete<List<Tuple<Int, Int> > > mk_list;
  mk_list.create(6);
  int i;
  for (i = 0; i < 6; i++) {
    mk_list.at(i).get<0>() = data[i].k;
    mk_list.at(i).get<1>() = data[i].v;
  }
  return mk_list.freeze();
}

int main() {
  Triolet_init();
  List<Tuple<Int, Int> > l = make_list();
  Array1<Int> a = foo(l);

  int i;
  for (i = 0; i < 6; i++) printf("%d", (int)a.at(i));

  return 0;
}
