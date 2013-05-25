
#ifndef _MEMORY_MAP_H
#define _MEMORY_MAP_H

/* Address range where library is loaded */
extern void *Triolet_library_address_start;
extern void *Triolet_library_address_end;

/* Return nonzero if the given string is a path of the Triolet library,
 * zero otherwise.
 */
int
triolet_is_rts_path(const char *);

/* Scan the memory map.
 * Initializes Triolet_library_address_start, Triolet_library_address_end
 */
void
triolet_scan_memory_map(void);

/* Translate a pointer to an offset if it falls within the library address
 * range.  Returns ~0 if outside the range.
 */
uint32_t
triolet_global_pointer_offset(void *);

/* Take the minimum of two addresses */
static inline void *
min_addr(void *x, void *y)
{
  return x < y ? x : y;
}

/* Take the maximum of two addresses */
static inline void *
max_addr(void *x, void *y)
{
  return x > y ? x : y;
}

#endif
