
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

extern function pyon.internal.prim.add_int (int, int) -> int;
extern function pyon.internal.prim.sub_int (int, int) -> int;
extern function pyon.internal.prim.negate_int (int) -> int;
extern function pyon.internal.prim.mul_int (int, int) -> int;
extern function pyon.internal.prim.fromint_int (int) -> int;
extern function pyon.internal.prim.floordiv_int (int, int) -> int;
extern function pyon.internal.prim.mod_int (int, int) -> int;

extern function pyon.internal.prim.add_float (float, float) -> float;
extern function pyon.internal.prim.sub_float (float, float) -> float;
extern function pyon.internal.prim.negate_float (float) -> float;
extern function pyon.internal.prim.mul_float (float, float) -> float;
extern function pyon.internal.prim.fromint_float (int) -> float;
extern function pyon.internal.prim.floordiv_float (float, float) -> int;
extern function pyon.internal.prim.mod_float (float, float) -> float;
extern function pyon.internal.prim.div_float (float, float) -> float;
extern function pyon.internal.prim.scale_float (float, float) -> float;
extern function pyon.internal.prim.magnitude_float (float) -> float;
extern function pyon.internal.prim.magnitude2_float (float) -> float;

extern function pyon.internal.prim.load_complexFloat
  (pointer) -> (complex(float));
extern function pyon.internal.prim.store_complexFloat
  (complex(float), pointer) -> ();

