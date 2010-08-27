
// For testing the low-level code directly
extern pointer pyon.internal.list.list_test "list_test";

// Exported to C
extern pointer pyon.internal.list.pyon_list_from_array "pyon_list_from_array";
extern pointer pyon.internal.list.pyon_list_to_array_POD "pyon_list_to_array_POD";
extern pointer pyon.internal.list.pyon_list_length "pyon_list_length";
extern pointer pyon.internal.list.pyon_list_copy_POD "pyon_list_copy_POD";
extern pointer pyon.internal.list.pyon_list_free_POD "pyon_list_free_POD";

extern owned pyon.internal.list.list_db;
extern owned pyon.internal.list.list_copy;
extern owned pyon.internal.list.list_finalize;
extern owned pyon.internal.list.list_build;
extern owned pyon.internal.list.list_traverse;

extern pointer pyon.internal.list.list_peek;


// Create the parameter passing convention of a list
#define PASSCONV_LIST(elem)				\
  (PassConv {sizeof PyonList,				\
             alignof PyonList,				\
             owned call list_copy(elem),		\
             owned call list_finalize(elem)})
