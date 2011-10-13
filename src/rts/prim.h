
extern procedure pyon.internal.prim.finite_IndInt (int) -> IndInt;
extern procedure pyon.internal.prim.from_finite_IndInt (IndInt) -> int;

extern function pyon.internal.prim.convertToBoxed
  (owned, owned) -> owned;

extern function pyon.internal.prim.convertToBare
  (owned, owned, pointer) -> ();

extern function pyon.internal.prim.make_Boxed (uint, uint, owned) -> owned;
extern function pyon.internal.prim.from_Boxed (uint, uint, owned, owned, pointer) -> ();

extern function pyon.internal.prim.make_Boxed_0 (owned) -> owned;
extern function pyon.internal.prim.make_Boxed_1 (owned) -> owned;
extern function pyon.internal.prim.make_Boxed_4 (owned) -> owned;

extern function pyon.internal.prim.from_Boxed_0 (owned, pointer) -> ();
extern function pyon.internal.prim.from_Boxed_1 (owned, pointer) -> ();
extern function pyon.internal.prim.from_Boxed_4 (owned, pointer) -> ();

extern function pyon.internal.prim.storeBox (owned, pointer) -> ();
extern function pyon.internal.prim.loadBox (pointer) -> owned;

extern function pyon.internal.prim.ptrToBox (pointer) -> owned;
extern function pyon.internal.prim.boxToPtr (owned) -> pointer;

extern function pyon.internal.prim.eq_int (int, int) -> bool;
extern function pyon.internal.prim.ne_int (int, int) -> bool;
extern function pyon.internal.prim.lt_int (int, int) -> bool;
extern function pyon.internal.prim.le_int (int, int) -> bool;
extern function pyon.internal.prim.gt_int (int, int) -> bool;
extern function pyon.internal.prim.ge_int (int, int) -> bool;

extern function pyon.internal.prim.eq_float (float, float) -> bool;
extern function pyon.internal.prim.ne_float (float, float) -> bool;
extern function pyon.internal.prim.lt_float (float, float) -> bool;
extern function pyon.internal.prim.le_float (float, float) -> bool;
extern function pyon.internal.prim.gt_float (float, float) -> bool;
extern function pyon.internal.prim.ge_float (float, float) -> bool;

extern function pyon.internal.prim.negate_int (int) -> int;
extern function pyon.internal.prim.floordiv_int (int, int) -> int;
extern function pyon.internal.prim.mod_int (int, int) -> int;

extern function pyon.internal.prim.negate_float (float) -> float;
extern function pyon.internal.prim.fromint_float (int) -> float;
extern function pyon.internal.prim.floordiv_float (float, float) -> int;
extern function pyon.internal.prim.mod_float (float, float) -> float;
extern function pyon.internal.prim.div_float (float, float) -> float;

extern function pyon.internal.prim.defineIntIndex (int) -> SomeIndInt;

extern function pyon.internal.prim.subscript
  (owned, pointer, int) -> pointer;

extern function pyon.internal.prim.subscript_out
  (owned, pointer, int) -> pointer;

extern function pyon.internal.prim.min_ii
  (IndInt, IndInt) -> IndInt;

extern function pyon.internal.prim.minus_ii
  (IndInt, IndInt) -> IndInt;

extern procedure pyon.internal.prim.min_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern procedure pyon.internal.prim.minus_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern function pyon.internal.prim.doall
  (FinIndInt, owned) -> ();

extern function pyon.internal.prim.for
  (owned, IndInt, pointer, owned, pointer) -> ();

extern function pyon.internal.prim.blocked_reduce
  (owned, FinIndInt, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.prim.blocked_reduce1
  (owned, FinIndInt, owned, owned, pointer) -> ();

// C implementation of blocked_reduce
import procedure pyon_C_blocked_reduce
  (owned, owned, owned, pointer, int, int) -> pointer;

// Functions called from the C side of the library
extern procedure pyon.internal.prim.blocked_reduce_copy
  "blocked_reduce_copy" (owned, pointer, pointer) -> ();
extern procedure pyon.internal.prim.blocked_reduce_accumulate_range
  "blocked_reduce_accumulate_range" (owned, pointer, int, int) -> pointer;
extern procedure pyon.internal.prim.blocked_reduce_reducer
  "blocked_reduce_reducer" (owned, pointer, pointer) -> pointer;

extern function pyon.internal.prim.blocked_doall
  (FinIndInt, int, owned) -> ();

// C implementation of blocked_doall
import procedure pyon_C_blocked_doall
  (owned, int, int) -> ();

extern procedure pyon.internal.prim.blocked_doall_worker
  "blocked_doall_worker" (owned, int, int) -> ();
