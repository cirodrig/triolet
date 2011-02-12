
extern function pyon.internal.prim.storeBox (unit, owned, pointer) -> ();
extern function pyon.internal.prim.loadBox (unit, pointer) -> owned;

extern function pyon.internal.prim.ptrToBox (unit, pointer) -> owned;
extern function pyon.internal.prim.boxToPtr (unit, owned) -> pointer;

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

extern function pyon.internal.prim.subscript
  (unit, unit, owned, pointer, int) -> pointer;

extern function pyon.internal.prim.subscript_out
  (unit, unit, owned, pointer, int) -> pointer;

extern function pyon.internal.prim.min_ii
  (unit, unit, IndexedInt, IndexedInt) -> IndexedInt;

extern function pyon.internal.prim.doall
  (unit, unit, unit, IndexedInt, owned) -> ();