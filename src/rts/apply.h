
/* Object deallocation functions */
void free_pap(PyonPtr);

/* Apply functions */
PyonPtr
apply_i32_f(PyonPtr obj, uint32_t arg);
void
apply_i32(PyonPtr obj, uint32_t arg, PyonPtr return_struct);

PyonPtr
apply_f32_f(PyonPtr obj, float arg);
void
apply_f32(PyonPtr obj, float arg, PyonPtr return_struct);
