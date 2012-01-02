
extern function pyon.internal.inplace.intSumScatterReduction_make_init
    (unit) -> int;
extern function pyon.internal.inplace.countingScatterReduction_make_init
    (unit) -> int;
extern function pyon.internal.inplace.intUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function pyon.internal.inplace.intUpdateInPlace_updater
    (owned, unit, pointer) -> unit;
extern function pyon.internal.inplace.floatSumScatterReduction_make_init
    (unit) -> float;
extern function pyon.internal.inplace.floatUpdateInPlace_initializer
    (owned, pointer) -> unit;
extern function pyon.internal.inplace.floatUpdateInPlace_updater
    (owned, unit, pointer) -> unit;

