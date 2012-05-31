
/* Object deallocation functions */
void free_pap(TrioletPtr);

/* Apply functions */
TrioletPtr
apply_o_f(TrioletPtr obj, TrioletPtr arg);
void
apply_o(TrioletPtr obj, TrioletPtr arg, TrioletPtr return_struct);

TrioletPtr
apply_i32_f(TrioletPtr obj, uint32_t arg);
void
apply_i32(TrioletPtr obj, uint32_t arg, TrioletPtr return_struct);

TrioletPtr
apply_f32_f(TrioletPtr obj, float arg);
void
apply_f32(TrioletPtr obj, float arg, TrioletPtr return_struct);

TrioletPtr
apply_u_f(TrioletPtr obj, int arg);
void
apply_u(TrioletPtr obj, int arg, TrioletPtr return_struct);
