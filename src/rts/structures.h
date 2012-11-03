
extern function core.internal.structures.copy_Tuple2
  (owned, owned, uint, uint, uint, uint, pointer, pointer) -> unit;

extern function core.internal.structures.makeComplex
  (float, float, pointer) -> unit;

extern function core.internal.structures.repr_Referenced
  (owned) -> owned;

extern function core.internal.structures.repr_arr
  (FinIndInt, owned) -> owned;

extern function core.internal.structures.repr_Maybe
  (owned) -> owned;

extern function core.internal.structures.repr_Tuple1
  (owned) -> owned;

extern function core.internal.structures.repr_Tuple2
  (owned, owned) -> owned;

extern function core.internal.structures.repr_Tuple3
  (owned, owned, owned) -> owned;

extern function core.internal.structures.repr_Tuple4
  (owned, owned, owned, owned) -> owned;

extern function core.internal.structures.sizealign_Tuple2
  (SA, SA) -> SA;
extern function core.internal.structures.sizealign_Tuple3
  (SA, SA, SA) -> SA;
extern function core.internal.structures.sizealign_Tuple4
  (SA, SA, SA, SA) -> SA;

extern data owned core.internal.structures.repr_EffTok;
extern data owned core.internal.structures.repr_Ref;
extern data owned core.internal.structures.repr_StuckRef;
extern data owned core.internal.structures.repr_Box;
extern data owned core.internal.structures.repr_Stream;
extern data owned core.internal.structures.repr_EmptyReference;
extern data owned core.internal.structures.repr_int;
extern data owned core.internal.structures.repr_uint;
extern data owned core.internal.structures.repr_float;
extern data owned core.internal.structures.repr_bool;
extern data owned core.internal.structures.repr_NoneType;
extern data owned core.internal.structures.repr_MaybeVal_int;
extern data owned core.internal.structures.repr_MaybeVal_MaybeVal_int;
extern data owned core.internal.structures.OpaqueTraversableDict_list;

extern data pointer core.internal.structures.int_info;
