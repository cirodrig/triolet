
extern function pyon.internal.inplace.repr_append_list
    (owned) -> owned;

extern function pyon.internal.inplace.intSumScatter_make_init
    (unit) -> int;
extern function pyon.internal.inplace.countingScatter_make_init
    (unit) -> int;
extern function pyon.internal.inplace.intUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function pyon.internal.inplace.intUpdateInPlace_updater
    (owned, unit, pointer) -> unit;
extern function pyon.internal.inplace.floatSumScatter_make_init
    (unit) -> float;
extern function pyon.internal.inplace.floatUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function pyon.internal.inplace.floatUpdateInPlace_updater
    (owned, unit, pointer) -> unit;

extern function pyon.internal.inplace.boxedScatter_updater
    (owned, unit, pointer) -> unit;

extern function pyon.internal.inplace.appendScatter_initializer
    (SA, owned, pointer) -> unit;
extern function pyon.internal.inplace.appendScatter_update_real
    (owned, owned, unit, pointer) -> unit;
