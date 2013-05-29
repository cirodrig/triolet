/*
 * Memory management
 */

/* The general-purpose memory allocator interface */
TrioletPtr triolet_alloc(uint32_t);
TrioletPtr triolet_alloc_nopointers(uint32_t);
void triolet_dealloc(TrioletPtr);
TrioletPtr triolet_preserve(TrioletPtr);

TrioletPtr triolet_alloc_boxed(uint32_t, uint32_t);
