
#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memory_map.h"
#include "memory_map_procfs.h"

// Enables debugging output
//#define CHATTY

///////////////////////////////////////////////////////////////////////////////
// Parsing for the proc filesystem

// An entry from the linux /proc/*/maps interface
struct map_entry {
  unsigned long long start_addr;
  unsigned long long end_addr;
  char *filename;
};

static void
map_entry_finalize(struct map_entry *p) {
  free(p->filename);
}

static int
parse_memory_map_entry(struct map_entry *result, FILE *maps);

static int
parse_hex_u64(unsigned long long *, FILE *);

static int
parse_u64(unsigned long long *, FILE *);

static int
accept_char(char, FILE *);

static int
accept_permissions(FILE *);

static int
accept_whitespace(FILE *);

static int
accept_string(char **, FILE *);

/* Parse a 64-bit hex number.  Returns 0 on error, 1 otherwise. */
static int
parse_hex_u64(unsigned long long *ret, FILE *f)
{
  char buffer[17];  /* 16 digits plus terminating null */
  int buffer_index = 0;

  /* Read up to 16 hex digits from the file */
  for (buffer_index = 0; buffer_index < 16; buffer_index++) {
    int c = fgetc(f);
    if (c == EOF) break;
    if (!isxdigit(c)) {
      ungetc(c, f);
      break;
    }
    buffer[buffer_index] = c;
  }

  if (buffer_index == 0) {
    return 0;                   /* Error, no characters read */
  }

  buffer[buffer_index] = 0;     /* Terminating NULL */

  /* Convert to an unsigned long long */
  *ret = strtoull(buffer, NULL, 16);
  return 1;
}

/* Parse a 64-bit number.  Returns 0 on error, 1 otherwise. */
static int
parse_u64(unsigned long long *ret, FILE *f)
{
  char buffer[21];  /* 20 digits plus terminating null */
  int buffer_index = 0;

  /* Read up to 20 digits from the file */
  for (buffer_index = 0; buffer_index < 20; buffer_index++) {
    int c = fgetc(f);
    if (c == EOF) break;
    if (!isdigit(c)) {
      ungetc(c, f);
      break;
    }
    buffer[buffer_index] = c;
  }

  if (buffer_index == 0) {
    return 0;                   /* Error, no characters read */
  }

  buffer[buffer_index] = 0;     /* Terminating NULL */

  /* Convert to an unsigned long long */
  *ret = strtoull(buffer, NULL, 10);
  return 1;
}

static int
accept_char(char c, FILE *f)
{
  int ch = fgetc(f);
  if (ch != (int)c) return 0;
  return 1;
}

/* Accept a permissions string from the input file */
static int
accept_permissions(FILE *f)
{
  int ch;
  do {
    ch = fgetc(f);
  } while (ch == 'r' || ch == 'w' || ch == 'x' ||
           ch == 'p' || ch == 's' || ch == '-');
  if (ch == EOF) return 1;
  ungetc(ch, f);
  return 1;
}

/* Accept a whitespace character that is not '\n' */
static int
accept_whitespace(FILE *f)
{
  int ch;
  do {
    ch = fgetc(f);
  } while (ch != '\n' && isspace(ch));
  if (ch == EOF) return 1;
  ungetc(ch, f);
  return 1;
}

static int
accept_string(char **ret, FILE *f)
{
  int capacity = 0;
  int size = 0;
  char *ret_string = NULL;

  /* Read until the first whitespace character */
  do {
    int ch = fgetc(f);
    if (ch == EOF) break;
    if (isspace(ch)) {
      ungetc(ch, f);
      break;
    }

    /* Append to the return string */
    if (capacity == size) {
      capacity = size + (size >> 1) + 1;
      ret_string = (char *)realloc(ret_string, capacity);
    }
    ret_string[size++] = ch;

  } while(1);

  /* Indicate if no characters were read */
  if (size == 0) {
    *ret = NULL;
    return 0;
  }

  /* Add terminating NULL */
  if (capacity == size) {
    capacity = size + 1;
    ret_string = (char *)realloc(ret_string, capacity);
  }
  ret_string[size] = 0;

  *ret = ret_string;
  return 1;
}

/* Parse one line of a memory map.

   Format:
   HEXU64-HEXU64 [rwxps-]* HEXU64 HEXU64:HEXU64 UINT (STRING)?\n
 */
static int
parse_memory_map_entry(struct map_entry *result, FILE *maps)
{
  unsigned long long dummy_ull; /* Destination for unwanted values */

  if (!parse_hex_u64(&result->start_addr, maps)) goto error;
  if (!accept_char('-', maps)) goto error;
  if (!parse_hex_u64(&result->end_addr, maps)) goto error;
  accept_whitespace(maps);
  if (!accept_permissions(maps)) goto error;
  accept_whitespace(maps);
  if (!parse_hex_u64(&dummy_ull, maps)) goto error;
  accept_whitespace(maps);
  if (!parse_hex_u64(&dummy_ull, maps)) goto error;
  if (!accept_char(':', maps)) goto error;
  if (!parse_hex_u64(&dummy_ull, maps)) goto error;
  accept_whitespace(maps);
  if (!parse_u64(&dummy_ull, maps)) goto error;
  accept_whitespace(maps);
  accept_string(&result->filename, maps); /* Optional string */
  if (!accept_char('\n', maps)) goto error;

  return 1;

 error:
  memset(result, 0, sizeof(struct map_entry));
  return 0;
}

/* Scan the parsed memory map entry and update global memory map information.
 *
 * Caller should pass nonzero for 'previous_entry_is_triolet_library' if the
 * previous entry was a Triolet library segment.  For some reason, the unnamed
 * segment after the Triolet library is also part of the Triolet library.
 */
static void
use_memory_map_entry(struct map_entry *entry,
                     int *entry_is_triolet_library,
                     int previous_entry_is_triolet_library)
{
  /* Is the filename's base name "libtrioletrts"? */
  int is_triolet_library = triolet_is_rts_path(entry->filename);
  *entry_is_triolet_library = is_triolet_library;

  if (is_triolet_library || previous_entry_is_triolet_library) {
    /* Include this address range in the Triolet library address range */
    void *sa = (void *)entry->start_addr;
    void *ea = (void *)entry->end_addr;
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

/* Search for the Triolet libraries in the memory map */
void triolet_scan_memory_map_procfs(void)
{
  FILE *maps;

  /* Find and open the memory map */
  {
    pid_t pid = getpid();
    char proc_filename[30];
    sprintf(proc_filename, "/proc/%u/maps", (unsigned int) pid);
    maps = fopen(proc_filename, "r");
    if (!maps) {
      fprintf(stderr, "Cannot view memory map through /proc\n");
      exit(-1);
    }
  }

  /* Read each line */
  int previous_entry_is_triolet_library = 0;
  do {
    struct map_entry entry;
    int entry_is_triolet_library;

    if (!parse_memory_map_entry(&entry, maps)) break;

#ifdef CHATTY
    /* Print the memory map */
    printf("%llx-%llx %s\n",
           entry.start_addr, entry.end_addr, entry.filename);
#endif

    use_memory_map_entry(&entry,
                         &entry_is_triolet_library,
                         previous_entry_is_triolet_library);

    map_entry_finalize(&entry);
    previous_entry_is_triolet_library = entry_is_triolet_library;
  } while(1);

  fclose(maps);
}

