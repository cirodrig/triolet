
extern function pyon.internal.list.repr_list (unit, owned) -> owned;

extern function pyon.internal.list.list_build
  (unit, owned, owned, pointer) -> ();
extern function pyon.internal.list.list_traverse
  (unit, owned, pointer) -> owned;
extern function pyon.internal.list.list_generate
  (unit, unit, owned, int, owned, pointer) -> ();
extern function pyon.internal.list.list_vGenerate
  (unit, unit, pointer, int, owned, pointer) -> ();

extern function pyon.internal.list.subscript
  (unit, owned, pointer, int) -> pointer;

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

