
extern function core.internal.inplace.append_build_list
    (owned, owned, pointer) -> unit;

extern function core.internal.inplace.repr_append_list
    (owned) -> owned;

extern function core.internal.inplace.intSumScatter_make_init
    (unit) -> int;
extern function core.internal.inplace.countingScatter_make_init
    (unit) -> int;
extern function core.internal.inplace.intUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function core.internal.inplace.intUpdateInPlace_updater
    (owned, unit, pointer) -> unit;
extern function core.internal.inplace.floatSumScatter_make_init
    (unit) -> float;
extern function core.internal.inplace.floatUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function core.internal.inplace.floatUpdateInPlace_updater
    (owned, unit, pointer) -> unit;
extern function core.internal.inplace.boolUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function core.internal.inplace.boolUpdateInPlace_updater
    (owned, unit, pointer) -> unit;

extern function core.internal.inplace.boxedScatter_updater
    (owned, unit, pointer) -> unit;

extern function core.internal.inplace.appendScatter_initializer
    (SA, owned, pointer) -> unit;
extern function core.internal.inplace.appendScatter_update_real
    (owned, owned, unit, pointer) -> unit;

extern function core.internal.inplace.compute_hash_table_size
    (FinIndInt) -> int;
extern function core.internal.inplace.build_hash_table
    (FinIndInt, FinIndInt, pointer, pointer) -> unit;
extern function core.internal.inplace.lookup_hash_table
    (FinIndInt, pointer, pointer, int) -> int;

import procedure triolet_hash_build
  (int, pointer, pointer, int, pointer) -> ();

import procedure triolet_hash_lookup
  (int, pointer, pointer, int) -> int;

import procedure triolet_hash_size
  (int) -> int;
