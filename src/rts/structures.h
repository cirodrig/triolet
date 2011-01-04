
extern function pyon.internal.structures.additiveDict
  (unit, pointer, owned, owned, owned, pointer, pointer) -> ();
extern function pyon.internal.structures.multiplicativeDict
  (unit, pointer, owned, owned, pointer, pointer) -> ();

extern function pyon.internal.structures.complex_pass_conv
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.AdditiveDict_pass_conv
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.MultiplicativeDict_pass_conv
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.additiveDict_complex
  (unit, pointer, pointer) -> ();

extern function pyon.internal.structures.makeComplex
  (float, float, pointer) -> ();

extern data pointer pyon.internal.structures.passConv_int;
extern data pointer pyon.internal.structures.float_pass_conv "float_pass_conv";
extern data pointer pyon.internal.structures.bool_pass_conv "bool_pass_conv";
extern data pointer pyon.internal.structures.PassConv_pass_conv "PassConv_pass_conv";
extern data pointer pyon.internal.structures.OpaqueTraversableDict_list;
