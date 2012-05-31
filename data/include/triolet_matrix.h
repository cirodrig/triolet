
/* Pyon matrices are an opaque structure type */
typedef struct {} TrioletMatrix;

#define DECLARE_MATRIX(T)						\
									\
  TrioletMatrix *								\
  triolet_Matrix_ ## T ## _FromArray(int ymin, int yend, int xmin, int xend, Triolet ## T *data); \
									\
  void									\
  triolet_Matrix_ ## T ## _ToArray(TrioletMatrix *list, Triolet ## T *data); \
									\
  int									\
  triolet_Matrix_ ## T ## _Height(TrioletMatrix *list);			\
									\
  int									\
  triolet_Matrix_ ## T ## _Height(TrioletMatrix *list);			\
									\
  TrioletMatrix *							\
  triolet_Matrix_ ## T ## _Copy(TrioletMatrix *);				\
									\
  void									\
  triolet_Matrix_ ## T ## _Free(TrioletMatrix *);

DECLARE_MATRIX(Float)

DECLARE_MATRIX(Int)

#undef DECLARE_MATRIX
