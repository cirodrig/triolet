
extern procedure core.internal.prim.finite_IndInt (int) -> IndInt;
extern procedure core.internal.prim.from_finite_IndInt (IndInt) -> int;

extern function core.internal.prim.convertToBoxed
  (owned, owned) -> owned;

extern function core.internal.prim.convertToBare
  (owned, owned, pointer) -> unit;

extern function core.internal.prim.make_Boxed (uint, uint, owned) -> owned;
extern function core.internal.prim.from_Boxed (uint, uint, owned, owned, pointer) -> unit;

extern function core.internal.prim.make_Boxed_0 (owned) -> owned;
extern function core.internal.prim.make_Boxed_1 (owned) -> owned;
extern function core.internal.prim.make_Boxed_4 (owned) -> owned;

extern function core.internal.prim.from_Boxed_0 (owned, pointer) -> unit;
extern function core.internal.prim.from_Boxed_1 (owned, pointer) -> unit;
extern function core.internal.prim.from_Boxed_4 (owned, pointer) -> unit;

extern function core.internal.prim.storeBox (owned, pointer) -> unit;
extern function core.internal.prim.loadBox (pointer) -> owned;

extern function core.internal.prim.ptrToBox (pointer) -> owned;
extern function core.internal.prim.boxToPtr (owned) -> pointer;

extern function core.internal.prim.eq_int (int, int) -> bool;
extern function core.internal.prim.ne_int (int, int) -> bool;
extern function core.internal.prim.lt_int (int, int) -> bool;
extern function core.internal.prim.le_int (int, int) -> bool;
extern function core.internal.prim.gt_int (int, int) -> bool;
extern function core.internal.prim.ge_int (int, int) -> bool;

extern function core.internal.prim.eq_float (float, float) -> bool;
extern function core.internal.prim.ne_float (float, float) -> bool;
extern function core.internal.prim.lt_float (float, float) -> bool;
extern function core.internal.prim.le_float (float, float) -> bool;
extern function core.internal.prim.gt_float (float, float) -> bool;
extern function core.internal.prim.ge_float (float, float) -> bool;

extern function core.internal.prim.negate_int (int) -> int;
extern function core.internal.prim.floordiv_int (int, int) -> int;
extern function core.internal.prim.mod_int (int, int) -> int;

extern function core.internal.prim.negate_float (float) -> float;
extern function core.internal.prim.fromint_float (int) -> float;
extern function core.internal.prim.floordiv_float (float, float) -> int;
extern function core.internal.prim.mod_float (float, float) -> float;
extern function core.internal.prim.div_float (float, float) -> float;

extern function core.internal.prim.defineIntIndex (int) -> SomeIndInt;

extern function core.internal.prim.subscript
  (SA, pointer, int) -> pointer;

extern function core.internal.prim.subscript_out
  (SA, pointer, int) -> pointer;

extern function core.internal.prim.min_ii
  (IndInt, IndInt) -> IndInt;

extern function core.internal.prim.minus_ii
  (IndInt, IndInt) -> IndInt;

extern procedure core.internal.prim.min_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern procedure core.internal.prim.minus_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern function core.internal.prim.not (bool) -> bool;

extern function core.internal.prim.gcd (int, int) -> int;

extern function core.internal.prim.extgcd_x (int, int) -> int;

extern function core.internal.prim.doall
  (FinIndInt, owned) -> unit;

extern function core.internal.prim.for
  (owned, FinIndInt, pointer, owned, pointer) -> unit;

extern function core.internal.prim.blocked_1d_reduce
  (FinIndInt, owned, owned, owned) -> owned;

// C implementation of blocked_reduce
import procedure triolet_C_blocked_reduce
  (owned, owned, owned, int) -> pointer;

// Functions called from the C side of the library
extern procedure core.internal.prim.blocked_reduce_accumulate_range
  "blocked_reduce_accumulate_range" (pointer, owned, int, int) -> owned;
extern procedure core.internal.prim.blocked_reduce_reduce
  "blocked_reduce_reduce" (pointer, owned, owned) -> owned;

extern function core.internal.prim.blocked_2d_reduce
  (FinIndInt, FinIndInt, owned, owned, owned) -> owned;

// C implementation of blocked_reduce
import procedure triolet_C_blocked_reduce2
  (owned, owned, owned, int, int) -> pointer;

// Functions called from the C side of the library
extern procedure core.internal.prim.blocked_reduce2_accumulate_range
  "blocked_reduce2_accumulate_range" (pointer, owned, int, int, int, int) -> owned;
extern procedure core.internal.prim.blocked_reduce2_reduce
  "blocked_reduce2_reduce" (pointer, owned, owned) -> owned;

extern function core.internal.prim.blocked_doall
  (FinIndInt, owned) -> unit;

// C implementation of blocked_doall
import procedure triolet_C_blocked_doall
  (owned, int) -> ();

extern procedure core.internal.prim.blocked_doall_worker
  "blocked_doall_worker" (owned, int, int) -> ();

extern function core.internal.prim.blocked_doall2
  (FinIndInt, FinIndInt, owned) -> unit;

// C implementation of blocked_doall2
import procedure triolet_C_blocked_doall2
  (owned, int, int) -> ();

extern procedure core.internal.prim.blocked_doall2_worker
  "blocked_doall2_worker" (owned, int, int, int, int) -> ();
