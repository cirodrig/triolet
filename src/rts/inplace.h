
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

extern function core.internal.inplace.boxedScatter_updater
    (owned, unit, pointer) -> unit;

extern function core.internal.inplace.appendScatter_initializer
    (SA, owned, pointer) -> unit;
extern function core.internal.inplace.appendScatter_update_real
    (owned, owned, unit, pointer) -> unit;
