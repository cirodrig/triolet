
#ifndef _MEMORY_MAP_H
#define _MEMORY_MAP_H

#include <inttypes.h>

/* Address range where library is loaded */
extern void *Triolet_library_address_start;
extern void *Triolet_library_address_end;

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

#endif
