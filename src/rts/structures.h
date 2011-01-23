
extern function pyon.internal.structures.copy_PyonTuple2
  (owned, owned, word, word, word, word, pointer, pointer) -> ();

extern function pyon.internal.structures.complex_pass_conv
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.additiveDict_complex
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.makeComplex
  (float, float, pointer) -> ();

extern function pyon.internal.structures.repr_Repr (unit) -> pointer;
extern function pyon.internal.structures.repr_AdditiveDict
  (unit, pointer, pointer) -> ();
extern function pyon.internal.structures.repr_MultiplicativeDict
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.repr_PyonTuple2
  (unit, unit, pointer, pointer, pointer) -> ();

extern data pointer pyon.internal.structures.repr_Repr_value;
extern data pointer pyon.internal.structures.repr_int;
extern data pointer pyon.internal.structures.repr_float;
extern data pointer pyon.internal.structures.repr_bool;
extern data pointer pyon.internal.structures.OpaqueTraversableDict_list;
