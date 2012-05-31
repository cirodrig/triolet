
#include <iostream>
#include <math.h>
#include "smvm_cxx.h"

using namespace Triolet;

typedef Array1<List<Tuple<Int, Float> > > SparseMatrix;

struct RowItem
{
  int index;
  float value;
};

void InitializeRow(Incomplete<List<Tuple<Int, Float> > > row,
                   int n_items,
                   RowItem *items)
{
  int i;
  row.initialize(n_items);
  for (i = 0; i < n_items; i++) {
    row.at(i).get<0>() = items[i].index;
    row.at(i).get<1>() = items[i].value;
  };
}

int main()
{
  Triolet_init();

  Incomplete<SparseMatrix> i_sparse_matrix;
  Incomplete<Array1<Float> > i_vector;

  i_sparse_matrix.create(0, 4);
  {
    RowItem row0[] = {};
    RowItem row1[] = {{0, 0.5}};
    RowItem row2[] = {{0, -0.5}, {2, 2.5}};
    RowItem row3[] = {{1, 1.5}};
    InitializeRow(i_sparse_matrix.at(0), 0, row0);
    InitializeRow(i_sparse_matrix.at(1), 1, row1);
    InitializeRow(i_sparse_matrix.at(2), 2, row2);
    InitializeRow(i_sparse_matrix.at(3), 1, row3);
  }

  SparseMatrix sparse_matrix = i_sparse_matrix.freeze();

  i_vector.create(0, 3);
  i_vector.at(0) = 0.75;
  i_vector.at(1) = -1.333;
  i_vector.at(2) = 0.6;

  Array1<Float> vector = i_vector.freeze();

  // Compute
  Array1<Float> product = smvm(sparse_matrix, vector);

  // Read results
  {
    int i;
    for (i = 0; i < 4; i++) {
      // All outputs are integers after multiplying by 8
      int n = rintf((float)(Float)product.at(i) * 8);
      printf("%d,", n);
    }
  }
  return 0;
}
