
extern function core.internal.prim.seqStore (unit, unit) -> (unit);
extern function core.internal.prim.read_int (pointer, unit) -> U2Tuple(int, unit);
extern function core.internal.prim.write_int (int, pointer, unit) -> unit;
extern function core.internal.prim.read_float (pointer, unit) -> U2Tuple(float, unit);
extern function core.internal.prim.write_float (float, pointer, unit) -> unit;

extern function core.internal.prim.makeIdCoercion (unit) -> unit;
extern function core.internal.prim.makeIdBareCoercion (unit) -> unit;

extern function core.internal.prim.preserve (owned) -> owned;

extern function core.internal.prim.traceInt_int (int, int) -> int;
extern function core.internal.prim.traceInt_box (int, owned) -> owned;

extern procedure core.internal.prim.finite_IndInt (int) -> IndInt;
extern procedure core.internal.prim.from_finite_IndInt (IndInt) -> int;

#if 0
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
#endif

extern function core.internal.prim.ptrToBox (pointer) -> owned;
extern function core.internal.prim.boxToPtr (owned) -> pointer;

extern function core.internal.prim.eq_int (int, int) -> uint;
extern function core.internal.prim.ne_int (int, int) -> uint;
extern function core.internal.prim.lt_int (int, int) -> uint;
extern function core.internal.prim.le_int (int, int) -> uint;
extern function core.internal.prim.gt_int (int, int) -> uint;
extern function core.internal.prim.ge_int (int, int) -> uint;

extern function core.internal.prim.eq_float (float, float) -> uint;
extern function core.internal.prim.ne_float (float, float) -> uint;
extern function core.internal.prim.lt_float (float, float) -> uint;
extern function core.internal.prim.le_float (float, float) -> uint;
extern function core.internal.prim.gt_float (float, float) -> uint;
extern function core.internal.prim.ge_float (float, float) -> uint;

extern function core.internal.prim.negate_int (int) -> int;
extern function core.internal.prim.floordiv_int (int, int) -> int;
extern function core.internal.prim.mod_int (int, int) -> int;

extern function core.internal.prim.negate_float (float) -> float;
extern function core.internal.prim.fromint_float (int) -> float;
extern function core.internal.prim.floordiv_float (float, float) -> int;
extern function core.internal.prim.mod_float (float, float) -> float;
extern function core.internal.prim.div_float (float, float) -> float;

extern function core.internal.prim.defineIntIndex (int) -> SomeIndInt;

extern function core.internal.prim.fromCursor (cursor) -> cursor;

extern function core.internal.prim.subscript
  (SA, cursor, int) -> cursor;

extern function core.internal.prim.subscript_out
  (SA, pointer, int) -> pointer;

extern function core.internal.prim.subarray
  (SA, cursor, int) -> cursor;

extern function core.internal.prim.subarray_out
  (SA, pointer, int) -> pointer;

extern function core.internal.prim.min_ii
  (IndInt, IndInt) -> IndInt;

extern function core.internal.prim.minus_ii
  (IndInt, IndInt) -> IndInt;

extern procedure core.internal.prim.min_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern procedure core.internal.prim.minus_fii
  (FinIndInt, FinIndInt) -> FinIndInt;

extern function core.internal.prim.not (uint) -> uint;

extern function core.internal.prim.gcd (int, int) -> int;

extern function core.internal.prim.extgcd_x (int, int) -> int;

extern function core.internal.prim.doall
  (FinIndInt, owned) -> unit;

extern function core.internal.prim.for
  (owned, FinIndInt, pointer, owned, pointer) -> unit;

///////////////////////////////////////////////////////////////////////////////
// MPI

extern function core.internal.prim.getNumDistributedPlaces
  (unit) -> SomeIndInt;
extern function core.internal.prim.inDistributedTask
  (unit) -> uint32;

import procedure triolet_begin_distributed_task () -> ();
import procedure triolet_end_distributed_task () -> ();
import procedure triolet_get_num_distributed_places () -> int32;
import procedure triolet_in_distributed_task() -> int32;

import procedure triolet_MPITask_launch(int32, pointer) -> pointer;
import procedure triolet_MPITask_wait(pointer, pointer) -> owned;

extern function core.internal.prim.farm (FinIndInt, owned, owned) -> owned;

extern procedure core.internal.prim.triolet_deserialize "triolet_deserialize"
  (uint32, pointer) -> owned;


extern procedure core.internal.prim.triolet_run_task "triolet_run_task"
  (int32, pointer, pointer) -> int32;

///////////////////////////////////////////////////////////////////////////////
// Blocked 1D reduction

extern function core.internal.prim.blocked_1d_reduce
  (FinIndInt, owned, owned, owned) -> owned;

// C implementation of blocked_reduce
import procedure triolet_C_blocked_reduce
  (pointer, owned, int) -> owned;

// Functions called from the C side of the library
extern procedure core.internal.prim.blocked_reduce_accumulate_range
  "blocked_reduce_accumulate_range" (pointer, owned, int, int) -> owned;
extern procedure core.internal.prim.blocked_reduce_reduce
  "blocked_reduce_reduce" (pointer, owned, owned) -> owned;

///////////////////////////////////////////////////////////////////////////////
// Blocked 2D reduction

extern function core.internal.prim.blocked_2d_reduce
  (FinIndInt, FinIndInt, owned, owned, owned) -> owned;

// C implementation of blocked_reduce
import procedure triolet_C_blocked_reduce2
  (pointer, owned, int, int) -> owned;

// Functions called from the C side of the library
extern procedure core.internal.prim.blocked_reduce2_accumulate_range
  "blocked_reduce2_accumulate_range" (pointer, owned, int, int, int, int) -> owned;
extern procedure core.internal.prim.blocked_reduce2_reduce
  "blocked_reduce2_reduce" (pointer, owned, owned) -> owned;

///////////////////////////////////////////////////////////////////////////////
// Blocked 1D reduction with in-place generate

extern function core.internal.prim.blocked_1d_reduceip
  (FinIndInt, owned, owned) -> owned;

// C implementation of blocked_reduce
import procedure triolet_C_blocked_reduceip
  (pointer, int) -> owned;

// Functions called from the C side of the library
extern procedure core.internal.prim.blocked_reduceip_generate_range
  "blocked_reduceip_generate_range" (pointer, int, int) -> owned;
extern procedure core.internal.prim.blocked_reduceip_reduce
  "blocked_reduceip_reduce" (pointer, owned, owned) -> owned;

///////////////////////////////////////////////////////////////////////////////
// Blocked 1D doall

extern function core.internal.prim.blocked_doall
  (FinIndInt, owned) -> unit;

// C implementation of blocked_doall
import procedure triolet_C_blocked_doall
  (owned, int) -> ();

extern procedure core.internal.prim.blocked_doall_worker
  "blocked_doall_worker" (owned, int, int) -> ();

///////////////////////////////////////////////////////////////////////////////
// Blocked 2D doall

extern function core.internal.prim.blocked_doall2
  (FinIndInt, FinIndInt, owned) -> unit;

// C implementation of blocked_doall2
import procedure triolet_C_blocked_doall2
  (owned, int, int) -> ();

extern procedure core.internal.prim.blocked_doall2_worker
  "blocked_doall2_worker" (owned, int, int, int, int) -> ();

///////////////////////////////////////////////////////////////////////////////
// Blocked build-tree reduction

extern function core.internal.prim.blocked_PBTree_doall
  (owned, owned) -> unit;

import procedure triolet_C_blocked_PBTree_doall
  (owned, owned) -> ();

extern procedure core.internal.prim.blocked_doall_PBTree_worker
  "blocked_doall_PBTree_worker" (owned, int, owned) -> ();

// Test whether tree is splittable.
// Return 'true' if splittable.
extern procedure core.internal.prim.PBTree_splittable
  "triolet_PBTree_splittable" (owned) -> bool;

// Split the tree.
// If splittable, write children into a 2-element array and return true.
// Else, write 'NULL' into array and return false.
extern procedure core.internal.prim.PBTree_split
  "triolet_PBTree_split" (owned, pointer) -> bool;

// Get the number of array elements contained in this tree's leaves.
extern procedure core.internal.prim.PBTree_size
  "triolet_PBTree_size" (owned) -> int;

// Construct a leaf from an array.
extern procedure core.internal.prim.PBTree_leaf
  "triolet_PBTree_leaf" (pointer) -> owned;

// Construct a branch from two tree nodes.
extern procedure core.internal.prim.PBTree_branch
  "triolet_PBTree_branch" (owned, owned) -> owned;

// Construct an empty tree.
extern procedure core.internal.prim.PBTree_empty
  "triolet_PBTree_empty" () -> owned;
