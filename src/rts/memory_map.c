
#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memory_map.h"
#include "memory_map_procfs.h"
#include "memory_map_darwin.h"

void *Triolet_library_address_start = NULL;
void *Triolet_library_address_end = NULL;

void *Triolet_program_address_start = NULL;
void *Triolet_program_address_end = NULL;

static int
memory_map_valid(void);

///////////////////////////////////////////////////////////////////////////////

/* Check whether the global memory map variables have been initialized */
static int
memory_map_valid(void)
{
  return
    Triolet_library_address_start != NULL &&
    Triolet_library_address_end != NULL;
}

int
triolet_is_rts_path(const char *filename)
{
  if (filename == NULL)
    return 0;

  int slash_index = -1;         // Index of last path separator found so far
  int cur_index = 0;            // Index of character being examined

  /* Find the last path separator in the string */
  {
    char c;
    for (c = filename[cur_index]; c; c = filename[++cur_index]) {
      if (c == '/') slash_index = cur_index;
    }
  }

  /* Does the part following the last path separator match "libtrioletrts"? */
  int cmp_result = strncmp(filename + slash_index + 1, "libtrioletrts",
                           strlen("libtrioletrts"));
  return cmp_result == 0;
}

/* Scan the program's memory map and initialize global memory map
 * information
 */
void
triolet_scan_memory_map(void)
{
  /* Error if the library address range is already set */
  if (memory_map_valid()) {
    fprintf(stderr, "Attempted to reinitialize Triolet memory map\n");
    exit(-1);
  }

#if defined(OS_LINUX)
  triolet_scan_memory_map_procfs();
#elif defined (OS_DARWIN)
  triolet_scan_memory_map_darwin();
#else
# error "triolet_scan_memory_map: Unsupported operating system"
#endif

  /* Error if the libray address range was not set */
  if (!memory_map_valid()) {
    fprintf(stderr, "Could not initialize Triolet memory map\n");
    exit(-1);
  }

#if 0
  /* Debugging output */
  /* Print the library address range inferred from the memory map */
  printf("%llx-%llx\n",
         (unsigned long long) Triolet_program_address_start,
         (unsigned long long) Triolet_program_address_end);
  printf("%llx-%llx\n",
         (unsigned long long) Triolet_library_address_start,
         (unsigned long long) Triolet_library_address_end);
#endif
}

uint32_t
triolet_program_pointer_offset(void *p)
{
  if (p >= Triolet_program_address_start && p <= Triolet_program_address_end) {
    return p - Triolet_program_address_start;
  }
  else
    return ~0U;
}

uint32_t
triolet_library_pointer_offset(void *p)
{
  if (p >= Triolet_library_address_start && p <= Triolet_library_address_end) {
    return p - Triolet_library_address_start;
  }
  else
    return ~0U;
}

void
triolet_extend_address_range (void **_lo_bound, void **_hi_bound,
                              void *lo, void *hi)
{
  /* If range hasn't been set yet, use [lo, hi) as the range */
  if (*_lo_bound == NULL && *_hi_bound == NULL) {
    *_lo_bound = lo;
    *_hi_bound = hi;
  }
  else {
    *_lo_bound = min_addr(*_lo_bound, lo);
    *_hi_bound = max_addr(*_hi_bound, hi);
  }
}
