
#include <inttypes.h>

/* The general-purpose memory allocator interface */
char *alloc(uint32_t);
void dealloc(char *);

/* Deallocation functions */
void free_lambda_closure(char *);
void free_pap(char *);
