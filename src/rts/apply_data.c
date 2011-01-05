
#if defined(ARCH_I386)
# include "arch/apply_data_x86.c"
#elif defined(ARCH_X86_64)
# include "arch/apply_data_x86_64.c"
#else
# error "Unrecognized architecture"
#endif
