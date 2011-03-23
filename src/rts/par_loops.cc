// This file defines parallelized C/C++ algorithmic skeletons of loops.
//
// The algorithmic skeletons are called from Pyon code.  They call back into
// Pyon code to do the actual work.

#include <stdio.h>

extern "C" {
#include "pyon.h"
}

#ifdef USE_TBB
# include "tbb/tbb_stddef.h"
# include "tbb/blocked_range.h"
# include "tbb/parallel_for.h"
# include "tbb/parallel_reduce.h"
#endif

/*****************************************************************************/
/* Parallelized reduction */

/* Functions written in low-level pyon */
extern "C" void *
blocked_reduce_allocate(void *fn);
extern "C" void
blocked_reduce_copy(void *fn, void *src, void *dst);
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
		      void *copy_fn,
		      void *initial_value_fn,
		      void *accumulate_range_fn,
		      void *reducer_fn,
		      PyonInt count,
		      PyonInt first,
		      void *ret);



#ifndef USE_TBB

// No parallel implementation available; use sequential reduction
void
pyon_C_blocked_reduce(void *allocate_fn,
		      void *copy_fn,
		      void *initial_value_fn,
		      void *accumulate_range_fn,
		      void *reducer_fn,
		      PyonInt count,
		      PyonInt first,
		      void *ret)
{
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

#else  // USE_TBB

// Parallel reduction using TBB

// Data that are constant over an invocation of 'blocked_reduce'.
struct BlockedReducePlan {
  // These are all pyon functions
  void *allocate_fn;
  void *copy_fn;
  void *initial_value_fn;
  void *accumulate_range_fn;
  void *reducer_fn;
};

// A partial reduction result, together with methods for computing a
// partial reduction and updating the result.
//
// Implements the parallel_reduce Body concept.
struct BlockedReducer {
  BlockedReducePlan *const plan;
  void *value;

  void initialize(void) {
    // Use 'plan' to initialize 'value'.
    // Called from constructor functions.
    value = blocked_reduce_allocate(plan->allocate_fn);
    blocked_reduce_initial_value(plan->initial_value_fn, value);
  };

  BlockedReducer(BlockedReducePlan *_plan) : plan(_plan) {
    initialize();
  };

  BlockedReducer(BlockedReducer &other, tbb::split) : plan(other.plan) {
    initialize();
  };

  void operator()(const tbb::blocked_range<int> &range) {
    int first = range.begin();
    int count = range.end() - first;

    void *new_value = blocked_reduce_allocate(plan->allocate_fn);
    blocked_reduce_accumulate_range(plan->accumulate_range_fn,
				    value, count, first, new_value);

    // TODO: finalize and deallocate old value
    value = new_value;
  };

  void join (BlockedReducer &other) {
    void *new_value = blocked_reduce_allocate(plan->allocate_fn);
    blocked_reduce_reducer(plan->reducer_fn, value, other.value, new_value);
    
    // TODO: finalize and deallocate old value
    value = new_value;
  }
};

void
pyon_C_blocked_reduce(void *allocate_fn,
		      void *copy_fn,
		      void *initial_value_fn,
		      void *accumulate_range_fn,
		      void *reducer_fn,
		      PyonInt count,
		      PyonInt first,
		      void *ret)
{
  BlockedReducePlan plan = {allocate_fn,
			    copy_fn,
			    initial_value_fn,
			    accumulate_range_fn,
			    reducer_fn};

  // Use TBB's parallel_reduce template
  tbb::blocked_range<int> range(first, first + count);
  BlockedReducer body(&plan);
  tbb::parallel_reduce(range, body);

  // Copy result
  blocked_reduce_copy(copy_fn, body.value, ret);
}

#endif	// USE_TBB

/*****************************************************************************/
/* Parallelized doall */

/* Functions written in low-level pyon */
extern "C" void
blocked_doall_worker(void *worker_fn, PyonInt count, PyonInt first);

/* Function exported to pyon */
extern "C" void
pyon_C_blocked_doall(void *worker_fn,
		     PyonInt count,
		     PyonInt first);

#ifndef USE_TBB

// Sequential implementation: do everything in one thread
extern "C" void
pyon_C_blocked_doall(void *worker_fn,
		     PyonInt count,
		     PyonInt first)
{
  blocked_doall_worker(worker_fn, count, first);
}

#else  // USE_TBB

// Parallel loop partitioned using TBB

struct BlockedDoer {
  void *worker_fn;

  BlockedDoer(void *_worker) : worker_fn(_worker) {}

  void operator()(tbb::blocked_range<int> &range) const {
    int first = range.begin();
    int count = range.end() - first;
    blocked_doall_worker(worker_fn, count, first);
  }
};

extern "C" void
pyon_C_blocked_doall(void *worker_fn,
		     PyonInt count,
		     PyonInt first)
{
  tbb::parallel_for(tbb::blocked_range<int>(first, first + count),
		    BlockedDoer(worker_fn));
}

#endif	// USE_TBB
