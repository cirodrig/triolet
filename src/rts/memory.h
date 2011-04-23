/*
 * Memory management
 */

/* The general-purpose memory allocator interface */
PyonPtr pyon_alloc(uint32_t);
PyonPtr pyon_alloc_nopointers(uint32_t);
void pyon_dealloc(PyonPtr);

