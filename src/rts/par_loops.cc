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
blocked_reduce_accumulate_range(void *data, void *acc, PyonInt start, PyonInt end);
extern "C" void *
blocked_reduce_reduce(void *data, void *x, void *y);


/* Function exported to pyon */
extern "C" void *
pyon_C_blocked_reduce(void *data,
		      void *initial_value,
		      PyonInt count);



#ifndef USE_TBB

// No parallel implementation available; use sequential reduction
void *
pyon_C_blocked_reduce(void *data, void *initial_value, PyonInt count)
{
  // Perform the reduction
  return blocked_reduce_accumulate_range(data, initial_value, 0, count);
}

#else  // USE_TBB

// Parallel reduction using TBB

// Data that are constant over an invocation of 'blocked_reduce'.
struct BlockedReducePlan {
  void *data;
  void *initial_value;
};

// A partial reduction result, together with methods for computing a
// partial reduction and updating the result.
//
// Implements the parallel_reduce Body concept.
struct BlockedReducer {
  BlockedReducePlan *const plan;
  void *value;

  BlockedReducer(BlockedReducePlan *_plan) :
    plan(_plan), value(_plan->initial_value) {};

  BlockedReducer(BlockedReducer &other, tbb::split) :
    plan(other.plan), value(other.plan->initial_value) {};

  void operator()(const tbb::blocked_range<int> &range) {
    int start = range.begin();
    int end = range.end();
    value = blocked_reduce_accumulate_range(plan->data, value, start, end);
  };

  void join (BlockedReducer &other) {
    value = blocked_reduce_reduce(plan->data, value, other.value);
  };
};

void *
pyon_C_blocked_reduce(void *data,
		      void *initial_value,
		      PyonInt count)
{
  BlockedReducePlan plan = {data, initial_value};

  // Use TBB's parallel_reduce template
  tbb::blocked_range<int> range(0, count);
  BlockedReducer body(&plan);
  tbb::parallel_reduce(range, body);

  // Return the result, which may be the initial value
  return body.value;
}

#endif	// USE_TBB

/*****************************************************************************/
/* Parallelized doall */

/* Functions written in low-level pyon */
extern "C" void
blocked_doall_worker(void *worker_fn, PyonInt start, PyonInt end);

/* Function exported to pyon */
extern "C" void
pyon_C_blocked_doall(void *worker_fn, PyonInt count);

#ifndef USE_TBB

// Sequential implementation: do everything in one thread
extern "C" void
pyon_C_blocked_doall(void *worker_fn, PyonInt count)
{
  blocked_doall_worker(worker_fn, 0, count);
}

#else  // USE_TBB

// Parallel loop partitioned using TBB

struct BlockedDoer {
  void *data;

  BlockedDoer(void *_data) : data(_data) {}

  void operator()(tbb::blocked_range<int> &range) const {
    int first = range.begin();
    int end = range.end();
    blocked_doall_worker(data, first, end);
  }
};

extern "C" void
pyon_C_blocked_doall(void *data, PyonInt count)
{
  tbb::parallel_for(tbb::blocked_range<int>(0, count),
		    BlockedDoer(data));
}

#endif	// USE_TBB
