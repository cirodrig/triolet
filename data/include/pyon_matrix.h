
/* Pyon matrices are an opaque structure type */
typedef struct {} PyonMatrix;

#define DECLARE_MATRIX(T)						\
									\
  PyonMatrix *								\
  pyon_Matrix_ ## T ## _FromArray(int height, int width, T *data);	\
									\
  void									\
  pyon_Matrix_ ## T ## _ToArray(PyonMatrix *list, T *data);		\
									\
  int									\
  pyon_Matrix_ ## T ## _Height(PyonMatrix *list);			\
									\
  int									\
  pyon_Matrix_ ## T ## _Height(PyonMatrix *list);			\
									\
  PyonMatrix *								\
  pyon_Matrix_ ## T ## _Copy(PyonMatrix *);				\
									\
  void									\
  pyon_Matrix_ ## T ## _Free(PyonMatrix *);

DECLARE_MATRIX(PyonFloat)

DECLARE_MATRIX(PyonInt)

#undef DECLARE_MATRIX
