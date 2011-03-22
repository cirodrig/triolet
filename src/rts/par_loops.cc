
extern "C" {
#include "pyon.h"
}

/* Functions written in low-level pyon */
extern "C" void *
blocked_reduce_allocate(void *fn);

extern "C" void
blocked_reduce_initial_value(void *fn, void *ret);

extern "C" void
blocked_reduce_accumulate_range(void *fn,
				void *initial_value,
				PyonInt count,
				PyonInt first,
				void *ret);

extern "C" void
blocked_reduce_reducer(void *fn, void *x, void *y, void *ret);


/* Function exported to pyon */
extern "C" void
pyon_C_blocked_reduce(void *allocate_fn,
		      void *initial_value_fn,
		      void *accumulate_range_fn,
		      void *reducer_fn,
		      PyonInt count,
		      PyonInt first,
		      void *ret);



void
pyon_C_blocked_reduce(void *allocate_fn,
		      void *initial_value_fn,
		      void *accumulate_range_fn,
		      void *reducer_fn,
		      PyonInt count,
		      PyonInt first,
		      void *ret)
{
  // Sequential implementation: Process everything in one step

  // Create the neutral element of the reduction
  void *initial_value = blocked_reduce_allocate(allocate_fn);
  blocked_reduce_initial_value(initial_value_fn, initial_value);

  // Perform the reduction
  blocked_reduce_accumulate_range(accumulate_range_fn,
				  initial_value,
				  count,
				  first,
				  ret);
}

