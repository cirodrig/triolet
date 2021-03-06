
#include <iostream>
#include <math.h>
#include "smvm_cxx.h"

using namespace Triolet;

typedef Tuple<List<Tuple<Int, Float> >, Array1<Int> > SparseMatrix;

struct RowItem
{
  int index;
  float value;
};

SparseMatrix CreateMatrix(void)
{
  // Constant data to put in the matrix
  static RowItem matrix_values[] = {
    {0, 0.5},
    {0, -0.5}, {2, 2.5},
    {1, 1.5}
  };

  // Index of first element of each row.
  static int matrix_row_indices[] = {0, 0, 1, 3, 4};

  Incomplete<SparseMatrix> matrix;
  matrix.create(SparseMatrix::initializer(4, Array1<Int>::initializer(0, 5)));

  {
    Incomplete<List<Tuple<Int, Float> > > values = matrix.get<0>();
    int i;
    for (i = 0; i < 4; i++) {
      values.at(i).get<0>() = matrix_values[i].index;
      values.at(i).get<1>() = matrix_values[i].value;
    }
  }

  {
    Incomplete<Array1<Int> > indices = matrix.get<1>();
    int i;
    for (i = 0; i < 5; i++) {
      indices.at(i) = matrix_row_indices[i];
    }
  }
  return matrix.freeze();
 }

int main(int argc, char **argv)
{
  Triolet_init(&argc, &argv);

  SparseMatrix sparse_matrix = CreateMatrix();
  Incomplete<Array1<Float> > i_vector;

  i_vector.create(0, 3);
  i_vector.at(0) = 0.75;
  i_vector.at(1) = -1.333;
  i_vector.at(2) = 0.6;

  Array1<Float> vector = i_vector.freeze();

  // Compute
  Array1<Float> product = smvm2(sparse_matrix, vector);

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
