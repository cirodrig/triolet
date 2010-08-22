
// For testing the low-level code directly
extern pointer pyon.internal.list.list_test "list_test";

extern owned pyon.internal.list.list_copy;
extern owned pyon.internal.list.list_finalize;

// Create the parameter passing convention of a list
#define PASSCONV_LIST(elem)				\
  (PassConv {sizeof PyonList,				\
             alignof PyonList,				\
             owned call list_copy(elem),		\
             owned call list_finalize(elem)})
