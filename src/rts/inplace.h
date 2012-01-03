
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

