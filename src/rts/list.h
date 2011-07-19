
extern function pyon.internal.list.repr_list (owned) -> owned;

extern function pyon.internal.list.list_len
  (pointer) -> int;
extern function pyon.internal.list.list_build
  (owned, owned, pointer) -> ();
extern function pyon.internal.list.list_traverse
  (owned, pointer) -> owned;
extern function pyon.internal.list.safeSubscript
  (owned, pointer, int, pointer) -> ();
extern function pyon.internal.list.list_generate
  (owned, IndInt, owned, pointer) -> ();
extern function pyon.internal.list.list_vGenerate
  (pointer, int, owned, pointer) -> ();

// Exported to C
extern procedure pyon.internal.list.pyon_List_PyonInt_FromArray "pyon_List_PyonInt_FromArray"
  (int, pointer) -> pointer;

extern procedure pyon.internal.list.pyon_List_PyonInt_ToArray "pyon_List_PyonInt_ToArray"
  (pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_List_PyonInt_Length "pyon_List_PyonInt_Length"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_List_PyonInt_Copy "pyon_List_PyonInt_Copy"
  (pointer) -> pointer;
extern procedure pyon.internal.list.pyon_List_PyonInt_Free "pyon_List_PyonInt_Free"
  (pointer) -> ();

extern procedure pyon.internal.list.pyon_List_PyonFloat_FromArray "pyon_List_PyonFloat_FromArray"
  (int, pointer) -> pointer;

extern procedure pyon.internal.list.pyon_List_PyonFloat_ToArray "pyon_List_PyonFloat_ToArray"
  (pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_List_PyonFloat_Length "pyon_List_PyonFloat_Length"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_List_PyonFloat_Copy "pyon_List_PyonFloat_Copy"
  (pointer) -> pointer;
extern procedure pyon.internal.list.pyon_List_PyonFloat_Free "pyon_List_PyonFloat_Free"
  (pointer) -> ();

extern procedure pyon.internal.list.pyon_Matrix_PyonInt_FromArray "pyon_Matrix_PyonInt_FromArray"
  (int, int, pointer) -> pointer;
extern procedure pyon.internal.list.pyon_Matrix_PyonInt_ToArray "pyon_Matrix_PyonInt_ToArray"
  (pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_Matrix_PyonInt_Height "pyon_Matrix_PyonInt_Height"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_Matrix_PyonInt_Width "pyon_Matrix_PyonInt_Width"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_Matrix_PyonInt_Copy "pyon_Matrix_PyonInt_Copy"
  (pointer) -> pointer;
extern procedure pyon.internal.list.pyon_Matrix_PyonInt_Free "pyon_Matrix_PyonInt_Free"
  (pointer) -> ();

extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_FromArray "pyon_Matrix_PyonFloat_FromArray"
  (int, int, pointer) -> pointer;
extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_ToArray "pyon_Matrix_PyonFloat_ToArray"
  (pointer, pointer) -> ();
extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_Height "pyon_Matrix_PyonFloat_Height"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_Width "pyon_Matrix_PyonFloat_Width"
  (pointer) -> int;
extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_Copy "pyon_Matrix_PyonFloat_Copy"
  (pointer) -> pointer;
extern procedure pyon.internal.list.pyon_Matrix_PyonFloat_Free "pyon_Matrix_PyonFloat_Free"
  (pointer) -> ();

