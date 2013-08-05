
extern function core.internal.structures.copy_Tuple2
  (owned, owned, uint, uint, uint, uint, pointer, pointer) -> unit;

extern function core.internal.structures.makeComplex
  (float, float, pointer) -> unit;

#if 0
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
extern function core.internal.structures.sizealign_arr
  (FinIndInt, SA) -> SA;

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
#endif

// Prebuilt representations for stored values.
// These are lazy globals.
extern data pointer coremodule.repr_int;
extern data pointer coremodule.repr_float;
extern data pointer coremodule.repr_bool;
extern data pointer coremodule.repr_NoneType;

extern function Builtin.repr_arr (FinIndInt, owned) -> owned;

// Auto-generated functions or lazy globals
extern function coremodule.Tuple2'T (owned, owned) -> owned;
extern function coremodule.Tuple3'T (owned, owned, owned) -> owned;
extern function coremodule.Tuple4'T (owned, owned, owned, owned) -> owned;
extern data pointer coremodule.StuckRef'T;
extern data pointer coremodule.list'T;
extern data pointer coremodule.array1'T;
extern data pointer coremodule.array2'T;
extern data pointer coremodule.array3'T;
extern data pointer coremodule.blist'T;
extern data pointer coremodule.barray1'T;
extern data pointer coremodule.barray2'T;
extern data pointer coremodule.barray3'T;
extern function coremodule.boxed'T (owned) -> owned;
extern function Builtin.ListSection'R (cursor, owned, unit) -> unit;

extern procedure core.internal.structures.triolet_typeObject_Stored_int
  "triolet_typeObject_Stored_int" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_Stored_float
  "triolet_typeObject_Stored_float" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_Stored_bool
  "triolet_typeObject_Stored_bool" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_Stored_NoneType
  "triolet_typeObject_Stored_NoneType" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_Tuple2
  "triolet_typeObject_Tuple2" (owned, owned) -> owned;
extern procedure core.internal.structures.triolet_typeObject_Tuple3
  "triolet_typeObject_Tuple3" (owned, owned, owned) -> owned;
extern procedure core.internal.structures.triolet_typeObject_Tuple4
  "triolet_typeObject_Tuple4" (owned, owned, owned, owned) -> owned;
extern procedure core.internal.structures.triolet_typeObject_StuckRef
  "triolet_typeObject_StuckRef" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_list
  "triolet_typeObject_list" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_array1
  "triolet_typeObject_array1" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_array2
  "triolet_typeObject_array2" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_array3
  "triolet_typeObject_array3" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_blist
  "triolet_typeObject_blist" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_barray1
  "triolet_typeObject_barray1" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_barray2
  "triolet_typeObject_barray2" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_barray3
  "triolet_typeObject_barray3" () -> owned;
extern procedure core.internal.structures.triolet_typeObject_boxed
  "triolet_typeObject_boxed" (owned) -> owned;

extern function core.internal.structures.typeObject_serialize
  (owned, owned, unit) -> unit;

extern function core.internal.structures.typeObject_deserialize
  (owned, cursor) -> ReadResult(owned);

extern data owned core.internal.structures.typeObject_typeObject;
#if 0
extern data owned core.internal.structures.typeObject_repr;
#endif
extern data owned core.internal.structures.triolet_typeObject_function "triolet_typeObject_function";

extern data owned core.internal.structures.OpaqueTraversableDict_list;

extern data pointer core.internal.structures.int_info;
