/*
 * Memory management
 */

/* The general-purpose memory allocator interface */
PyonPtr pyon_alloc(uint32_t);
void pyon_dealloc(PyonPtr);

