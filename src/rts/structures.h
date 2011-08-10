
extern function pyon.internal.structures.copy_PyonTuple2
  (owned, owned, uint, uint, uint, uint, pointer, pointer) -> ();

extern function pyon.internal.structures.copy_Repr
  (pointer, pointer) -> ();

extern function pyon.internal.structures.complex_pass_conv
  (pointer, pointer) -> ();

extern function pyon.internal.structures.additiveDict_complex
  (pointer, pointer) -> ();

extern function pyon.internal.structures.makeComplex
  (float, float, pointer) -> ();

extern function pyon.internal.structures.repr_Referenced
  (owned) -> owned;

extern function pyon.internal.structures.repr_array
  (FinIndInt, owned) -> owned;

extern function pyon.internal.structures.repr_Maybe
  (owned) -> owned;

extern function pyon.internal.structures.repr_PyonTuple2
  (owned, owned) -> owned;

extern function pyon.internal.structures.repr_PyonTuple3
  (owned, owned, owned) -> owned;

extern function pyon.internal.structures.repr_PyonTuple4
  (owned, owned, owned, owned) -> owned;

extern data owned pyon.internal.structures.repr_EffTok;
extern data owned pyon.internal.structures.repr_Box;
extern data owned pyon.internal.structures.repr_Stream;
extern data owned pyon.internal.structures.repr_EmptyReference;
extern data owned pyon.internal.structures.repr_int;
extern data owned pyon.internal.structures.repr_float;
extern data owned pyon.internal.structures.repr_bool;
extern data owned pyon.internal.structures.OpaqueTraversableDict_list;

extern data pointer pyon.internal.structures.int_info;
