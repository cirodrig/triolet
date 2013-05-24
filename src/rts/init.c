
#include <mpi.h>
#include <inttypes.h>
#include <unistd.h>
#include <stdio.h>

#include "init.h"
#include "trioletmpi.h"
#include "memory_map.h"

int Triolet_is_initialized = 0;

/* Called from Triolet_init() if Triolet hasn't been initialized */
extern void Triolet_init_real(int *argc, char ***argv)
{
  triolet_scan_memory_map();

#if 0
  /* Debugging: Wait for an external GDB process to attach */
  printf("PID %d ready\n", getpid());
  fflush(stdout);
  sleep(12);
#endif

  triolet_MPITask_setup(argc, argv);
  Triolet_is_initialized = 1;
}
