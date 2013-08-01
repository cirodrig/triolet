
extern procedure core.internal.apply_new.apply_u_f (owned, unit) -> owned;
extern procedure core.internal.apply_new.apply_u (owned, unit, pointer) -> ();
extern procedure core.internal.apply_new.apply_p_f (owned, pointer) -> owned;
extern procedure core.internal.apply_new.apply_p (owned, pointer, pointer) -> ();
extern procedure core.internal.apply_new.apply_o_f (owned, owned) -> owned;
extern procedure core.internal.apply_new.apply_o (owned, owned, pointer) -> ();
extern procedure core.internal.apply_new.apply_c_f (owned, cursor) -> owned;
extern procedure core.internal.apply_new.apply_c (owned, cursor, pointer) -> ();
extern procedure core.internal.apply_new.apply_i32_f (owned, int32) -> owned;
extern procedure core.internal.apply_new.apply_i32 (owned, int32, pointer) -> ();
extern procedure core.internal.apply_new.apply_i64_f (owned, int64) -> owned;
extern procedure core.internal.apply_new.apply_i64 (owned, int64, pointer) -> ();
extern procedure core.internal.apply_new.apply_f32_f (owned, float) -> owned;
extern procedure core.internal.apply_new.apply_f32 (owned, float, pointer) -> ();

extern data owned core.internal.apply_new.typeObject_PAP_u;
extern data owned core.internal.apply_new.typeObject_PAP_p;
extern data owned core.internal.apply_new.typeObject_PAP_o;
extern data owned core.internal.apply_new.typeObject_PAP_c;
extern data owned core.internal.apply_new.typeObject_PAP_i32;
extern data owned core.internal.apply_new.typeObject_PAP_i64;
extern data owned core.internal.apply_new.typeObject_PAP_f32;
