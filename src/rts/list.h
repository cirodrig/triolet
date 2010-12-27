
// For testing the low-level code directly
extern procedure pyon.internal.list.list_test "list_test" () -> ();

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

extern function pyon.internal.list.passConv_list
  (unit, pointer, pointer) -> ();

extern procedure pyon.internal.list.list_peek
  (pointer, pointer, word, pointer) -> ();

// Exported to C
extern procedure pyon.internal.list.pyon_List_PyonInt_FromArray "pyon_List_PyonInt_FromArray"
  (cint, pointer) -> pointer;

extern procedure pyon.internal.list.pyon_List_PyonInt_ToArray "pyon_List_PyonInt_ToArray"
  (pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_List_PyonInt_Length "pyon_List_PyonInt_Length"
  (pointer) -> cint;
extern procedure pyon.internal.list.pyon_List_PyonInt_Copy "pyon_List_PyonInt_Copy"
  (pointer) -> pointer;
extern procedure pyon.internal.list.pyon_List_PyonInt_Free "pyon_List_PyonInt_Free"
  (pointer) -> ();

