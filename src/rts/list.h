
// For testing the low-level code directly
extern procedure pyon.internal.list.list_test "list_test" () -> ();

// Exported to C
extern procedure pyon.internal.list.pyon_list_from_array "pyon_list_from_array"
  (word, pointer) -> pointer;
extern procedure pyon.internal.list.pyon_list_to_array_POD "pyon_list_to_array_POD"
  (pointer, pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_list_length "pyon_list_length"
  (pointer) -> word;
extern procedure pyon.internal.list.pyon_list_copy_POD "pyon_list_copy_POD"
  (pointer, pointer) -> pointer;
extern procedure pyon.internal.list.pyon_list_free_POD "pyon_list_free_POD"
  (pointer) -> ();

extern function pyon.internal.list.list_db (pointer) -> ();
extern function pyon.internal.list.list_copy (pointer, pointer, pointer) -> ();
extern function pyon.internal.list.list_finalize (pointer, pointer) -> ();
extern function pyon.internal.list.list_build (unit, unit, pointer, owned, pointer) -> ();
extern function pyon.internal.list.list_traverse
  (unit, pointer, pointer) -> owned;
extern function pyon.internal.list.list_generate
  (unit, unit, pointer, int, owned, pointer) -> ();

extern function pyon.internal.list.subscript
  (unit, pointer, pointer, int) -> pointer;

extern procedure pyon.internal.list.list_peek
  (pointer, pointer, word, pointer) -> ();
// Create the parameter passing convention of a list
#define PASSCONV_LIST(elem)				\
  (PassConv {sizeof PyonList,				\
             alignof PyonList,				\
             owned call list_copy(elem),		\
             owned call list_finalize(elem)})
