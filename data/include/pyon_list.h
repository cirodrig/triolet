
/* Pyon lists are an opaque structure type */
typedef struct {} PyonList;

#define DECLARE_LIST(T)						\
								\
  PyonList *							\
  pyon_List_ ## T ## _FromArray(int length, T *data);		\
								\
  void								\
  pyon_List_ ## T ## _ToArray(PyonList *list, T *data);		\
								\
  int								\
  pyon_List_ ## T ## _Length(PyonList *list);			\
								\
  PyonList *							\
  pyon_List_ ## T ## _Copy(PyonList *);				\
								\
  void								\
  pyon_List_ ## T ## _Free(PyonList *);

DECLARE_LIST(PyonFloat)

DECLARE_LIST(PyonInt)

#undef DECLARE_LIST
