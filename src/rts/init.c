
#include "init.h"
#include "memory_map.h"

int Triolet_is_initialized = 0;

/* Called from Triolet_init() if Triolet hasn't been initialized */
extern void Triolet_init_real(void)
{
  triolet_scan_memory_map();
  Triolet_is_initialized = 1;
}
