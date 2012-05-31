
/* Pyon lists are an opaque structure type */
typedef struct {} TrioletList;

#define DECLARE_LIST(T)						\
								\
  TrioletList *							\
  triolet_List_ ## T ## _FromArray(int length, Triolet ## T *data);        \
								\
  void								\
  triolet_List_ ## T ## _ToArray(TrioletList *list, Triolet ## T *data);	\
								\
  int								\
  triolet_List_ ## T ## _Length(TrioletList *list);		\
								\
  TrioletList *							\
  triolet_List_ ## T ## _Copy(TrioletList *);			\
								\
  void								\
  triolet_List_ ## T ## _Free(TrioletList *);

DECLARE_LIST(Float)

DECLARE_LIST(Int)

#undef DECLARE_LIST
