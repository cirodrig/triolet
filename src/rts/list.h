
extern function pyon.internal.list.repr_list (owned) -> owned;

extern function pyon.internal.list.repr_array2 (owned) -> owned;

extern function pyon.internal.list.list_build
  (owned, owned, pointer) -> ();

// Exported to C
extern data pointer pyon.internal.list.pyon_List_size "pyon_List_size";
extern data pointer pyon.internal.list.pyon_List_alignment "pyon_List_alignment";

extern procedure pyon.internal.list.pyon_List_initialize "pyon_List_initialize"
  (int, uint, uint, pointer) -> ();

extern procedure pyon.internal.list.pyon_List_get_contents "pyon_List_get_contents"
  (pointer) -> pointer;

extern procedure pyon.internal.list.pyon_List_get_length "pyon_List_get_length"
  (pointer) -> uint;

extern procedure pyon.internal.list.pyon_Array0_size "pyon_Array0_size"
  (uint, uint) -> uint;
extern procedure pyon.internal.list.pyon_Array0_alignment "pyon_Array0_alignment"
  (uint, uint) -> uint;

extern procedure pyon.internal.list.pyon_Array0_get_contents "pyon_Array0_get_contents"
  (pointer, uint, uint) -> pointer;

extern data pointer pyon.internal.list.pyon_Array1_size "pyon_Array1_size";
extern data pointer pyon.internal.list.pyon_Array1_alignment "pyon_Array1_alignment";

extern procedure pyon.internal.list.pyon_Array1_initialize "pyon_Array1_initialize"
  (int, int, int, uint, uint, pointer) -> ();

extern procedure pyon.internal.list.pyon_Array1_get_contents "pyon_Array1_get_contents"
  (pointer) -> pointer;

extern procedure pyon.internal.list.pyon_Array1_get_bounds "pyon_Array1_get_bounds"
  (pointer) -> PyonTuple3(int, int, int);

extern data pointer pyon.internal.list.pyon_Array2_size "pyon_Array2_size";
extern data pointer pyon.internal.list.pyon_Array2_alignment "pyon_Array2_alignment";

extern procedure pyon.internal.list.pyon_Array2_initialize "pyon_Array2_initialize"
  (int, int, int, int, int, int, uint, uint, pointer) -> ();

extern procedure pyon.internal.list.pyon_Array2_get_contents "pyon_Array2_get_contents"
  (pointer) -> pointer;

extern procedure pyon.internal.list.pyon_Array2_get_bounds "pyon_Array2_get_bounds"
  (pointer) -> PyonTuple6(int, int, int, int, int, int);

extern data pointer pyon.internal.list.pyon_Array3_size "pyon_Array3_size";
extern data pointer pyon.internal.list.pyon_Array3_alignment "pyon_Array3_alignment";

extern procedure pyon.internal.list.pyon_Array3_initialize "pyon_Array3_initialize"
  (int, int, int, int, int, int, int, int, int, uint, uint, pointer) -> ();

extern procedure pyon.internal.list.pyon_Array3_get_contents "pyon_Array3_get_contents"
  (pointer) -> pointer;

extern procedure pyon.internal.list.pyon_Array3_get_bounds "pyon_Array3_get_bounds"
  (pointer) -> PyonTuple3(PyonTuple3(int, int, int),
                          PyonTuple3(int, int, int),
                          PyonTuple3(int, int, int));


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
  (int, int, int, int, pointer) -> pointer;
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
  (int, int, int, int, pointer) -> pointer;
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

