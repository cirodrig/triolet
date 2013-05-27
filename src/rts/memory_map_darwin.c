
#ifdef USE_DARWIN

#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <dlfcn.h>
#include <mach-o/dyld.h>
#include <mach-o/getsect.h>

#include "memory_map.h"
#include "memory_map_darwin.h"

// Enables debugging output
//#define CHATTY

// True while scanning memory images
static int scanning_images = 0;

struct SectionName {
  const char *segment;
  const char *section;
};

// The Mach-O sections that may be global pointer targets
static const struct SectionName sections[] = {
  { SEG_TEXT, SECT_TEXT },
  { SEG_DATA, SECT_DATA },
  { SEG_DATA, SECT_BSS },
  { SEG_DATA, SECT_COMMON },
  { NULL, NULL }
};

///////////////////////////////////////////////////////////////////////////////

/* Examine a single loaded memory section */
static void
use_section(const Dl_info *dynamic_linker_info,
            const struct SectionName *section,
            const intptr_t start,
            const intptr_t end)
{
#ifdef CHATTY
  // Debugging info
  printf("%llx, %llx, %s\n",
         (unsigned long long)start, (unsigned long long)end,
         dynamic_linker_info->dli_fname);
#endif

    
  // Is the image from the Triolet library?
  if (triolet_is_rts_path(dynamic_linker_info->dli_fname)) {
    /* Include this address range in the Triolet library address range */
    void *sa = (void *)start;
    void *ea = (void *)end;
    if (Triolet_library_address_start == 0) {
      Triolet_library_address_start = sa;
      Triolet_library_address_end = ea;
    }
    else {
      Triolet_library_address_start =
        min_addr(Triolet_library_address_start, sa);
      Triolet_library_address_end =
        max_addr(Triolet_library_address_end, ea);
    }
  }
}

/* The OS calls this function on each image that's loaded into memory.
 */
static void
scan_image (const struct mach_header *_header, intptr_t slide)
{
  int err;

  // Cast to correct type for 64-bit architectures
  const struct mach_header_64 *header = (const struct mach_header_64 *)_header;

  // Only process the image during the scanning phase of the program
  if (!scanning_images) return;

#ifdef CHATTY
  printf("Scanning a loaded binary image\n");
#endif

  // Examine each section
  const struct SectionName *section;
  for (section = sections; section->segment; section++) {
    const struct section_64 *sec =
      getsectbynamefromheader_64(header, section->segment, section->section);

    if (sec == NULL || sec->size == 0) return;

    intptr_t start = slide + sec->addr;
    intptr_t end = start + sec->size;

    // Get image name
    Dl_info dynamic_linker_info;
    if (dladdr((void *)start, &dynamic_linker_info) == 0) {
      // This error should never happen.
      // Start address should always be part of a segment.
      exit(-1);
    }

    use_section(&dynamic_linker_info, section, start, end);
  }

}

void
triolet_scan_memory_map_darwin(void)
{
  scanning_images = 1;

  /* The given callback will be called for each loaded image */
  _dyld_register_func_for_add_image(scan_image);
  scanning_images = 0;
}

#endif
