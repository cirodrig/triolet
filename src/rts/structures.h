
extern function pyon.internal.structures.copy_PyonTuple2
  (owned, owned, uint, uint, uint, uint, pointer, pointer) -> unit;

extern function pyon.internal.structures.makeComplex
  (float, float, pointer) -> unit;

extern function pyon.internal.structures.repr_Referenced
  (owned) -> owned;

extern function pyon.internal.structures.repr_arr
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
extern data owned pyon.internal.structures.repr_StoredBox;
extern data owned pyon.internal.structures.repr_StuckRef;
extern data owned pyon.internal.structures.repr_Box;
extern data owned pyon.internal.structures.repr_Stream;
extern data owned pyon.internal.structures.repr_EmptyReference;
extern data owned pyon.internal.structures.repr_int;
extern data owned pyon.internal.structures.repr_float;
extern data owned pyon.internal.structures.repr_bool;
extern data owned pyon.internal.structures.OpaqueTraversableDict_list;

extern data pointer pyon.internal.structures.int_info;
