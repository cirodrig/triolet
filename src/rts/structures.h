
extern function pyon.internal.structures.copy_PyonTuple2
  (owned, owned, word, word, word, word, pointer, pointer) -> ();

extern function pyon.internal.structures.copy_Repr
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.complex_pass_conv
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.additiveDict_complex
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.makeComplex
  (float, float, pointer) -> ();

extern function pyon.internal.structures.repr_Box (unit) -> owned;
extern function pyon.internal.structures.repr_Boxed (unit) -> owned;
extern function pyon.internal.structures.repr_Stream (unit) -> owned;

extern function pyon.internal.structures.repr_PyonTuple2
  (unit, unit, owned, owned) -> owned;

extern data owned pyon.internal.structures.repr_Box_value;
extern data owned pyon.internal.structures.repr_int;
extern data owned pyon.internal.structures.repr_float;
extern data owned pyon.internal.structures.repr_bool;
extern data owned pyon.internal.structures.OpaqueTraversableDict_list;
