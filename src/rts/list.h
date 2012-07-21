
extern function core.internal.list.repr_list (owned) -> owned;

extern function core.internal.list.repr_array2 (owned) -> owned;

// Exported to C
extern data pointer core.internal.list.triolet_List_size "triolet_List_size";
extern data pointer core.internal.list.triolet_List_alignment "triolet_List_alignment";

extern procedure core.internal.list.triolet_List_initialize "triolet_List_initialize"
  (int, uint, uint, pointer) -> ();

extern procedure core.internal.list.triolet_List_get_contents "triolet_List_get_contents"
  (pointer, uint, uint) -> pointer;

extern procedure core.internal.list.triolet_List_get_length "triolet_List_get_length"
  (pointer) -> uint;

extern procedure core.internal.list.triolet_Array0_size "triolet_Array0_size"
  (uint, uint) -> uint;
extern procedure core.internal.list.triolet_Array0_alignment "triolet_Array0_alignment"
  (uint, uint) -> uint;

extern procedure core.internal.list.triolet_Array0_get_contents "triolet_Array0_get_contents"
  (pointer, uint, uint) -> pointer;

extern data pointer core.internal.list.triolet_Array1_size "triolet_Array1_size";
extern data pointer core.internal.list.triolet_Array1_alignment "triolet_Array1_alignment";

extern procedure core.internal.list.triolet_Array1_initialize "triolet_Array1_initialize"
  (int, int, int, uint, uint, pointer) -> ();

extern procedure core.internal.list.triolet_Array1_get_contents "triolet_Array1_get_contents"
  (pointer, uint, uint) -> pointer;

extern procedure core.internal.list.triolet_Array1_get_bounds "triolet_Array1_get_bounds"
  (pointer) -> Tuple3(int, int, int);

extern data pointer core.internal.list.triolet_Array2_size "triolet_Array2_size";
extern data pointer core.internal.list.triolet_Array2_alignment "triolet_Array2_alignment";

extern procedure core.internal.list.triolet_Array2_initialize "triolet_Array2_initialize"
  (int, int, int, int, int, int, uint, uint, pointer) -> ();

extern procedure core.internal.list.triolet_Array2_get_contents "triolet_Array2_get_contents"
  (pointer, uint, uint) -> pointer;

extern procedure core.internal.list.triolet_Array2_get_bounds "triolet_Array2_get_bounds"
  (pointer) -> Tuple6(int, int, int, int, int, int);

extern data pointer core.internal.list.triolet_Array3_size "triolet_Array3_size";
extern data pointer core.internal.list.triolet_Array3_alignment "triolet_Array3_alignment";

extern procedure core.internal.list.triolet_Array3_initialize "triolet_Array3_initialize"
  (int, int, int, int, int, int, int, int, int, uint, uint, pointer) -> ();

extern procedure core.internal.list.triolet_Array3_get_contents "triolet_Array3_get_contents"
  (pointer, uint, uint) -> pointer;

extern procedure core.internal.list.triolet_Array3_get_bounds "triolet_Array3_get_bounds"
  (pointer) -> Tuple3(Tuple3(int, int, int),
                      Tuple3(int, int, int),
                      Tuple3(int, int, int));


extern procedure core.internal.list.triolet_List_Int_FromArray "triolet_List_Int_FromArray"
  (int, pointer) -> pointer;

extern procedure core.internal.list.triolet_List_Int_ToArray "triolet_List_Int_ToArray"
  (pointer, pointer) -> ();
extern procedure core.internal.list.triolet_List_Int_Length "triolet_List_Int_Length"
  (pointer) -> int;
extern procedure core.internal.list.triolet_List_Int_Copy "triolet_List_Int_Copy"
  (pointer) -> pointer;
extern procedure core.internal.list.triolet_List_Int_Free "triolet_List_Int_Free"
  (pointer) -> ();

extern procedure core.internal.list.triolet_List_Float_FromArray "triolet_List_Float_FromArray"
  (int, pointer) -> pointer;

extern procedure core.internal.list.triolet_List_Float_ToArray "triolet_List_Float_ToArray"
  (pointer, pointer) -> ();
extern procedure core.internal.list.triolet_List_Float_Length "triolet_List_Float_Length"
  (pointer) -> int;
extern procedure core.internal.list.triolet_List_Float_Copy "triolet_List_Float_Copy"
  (pointer) -> pointer;
extern procedure core.internal.list.triolet_List_Float_Free "triolet_List_Float_Free"
  (pointer) -> ();

extern procedure core.internal.list.triolet_Matrix_Int_FromArray "triolet_Matrix_Int_FromArray"
  (int, int, int, int, pointer) -> pointer;
extern procedure core.internal.list.triolet_Matrix_Int_ToArray "triolet_Matrix_Int_ToArray"
  (pointer, pointer) -> ();
extern procedure core.internal.list.triolet_Matrix_Int_Height "triolet_Matrix_Int_Height"
  (pointer) -> int;
extern procedure core.internal.list.triolet_Matrix_Int_Width "triolet_Matrix_Int_Width"
  (pointer) -> int;
extern procedure core.internal.list.triolet_Matrix_Int_Copy "triolet_Matrix_Int_Copy"
  (pointer) -> pointer;
extern procedure core.internal.list.triolet_Matrix_Int_Free "triolet_Matrix_Int_Free"
  (pointer) -> ();

extern procedure core.internal.list.triolet_Matrix_Float_FromArray "triolet_Matrix_Float_FromArray"
  (int, int, int, int, pointer) -> pointer;
extern procedure core.internal.list.triolet_Matrix_Float_ToArray "triolet_Matrix_Float_ToArray"
  (pointer, pointer) -> ();
extern procedure core.internal.list.triolet_Matrix_Float_Height "triolet_Matrix_Float_Height"
  (pointer) -> int;
extern procedure core.internal.list.triolet_Matrix_Float_Width "triolet_Matrix_Float_Width"
  (pointer) -> int;
extern procedure core.internal.list.triolet_Matrix_Float_Copy "triolet_Matrix_Float_Copy"
  (pointer) -> pointer;
extern procedure core.internal.list.triolet_Matrix_Float_Free "triolet_Matrix_Float_Free"
  (pointer) -> ();

