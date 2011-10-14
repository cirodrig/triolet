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
  // These are all pyon functions
  void *copy_fn;
  void *accumulate_range_fn;
  void *reducer_fn;

  // The initial value of the reduction; a read-only reference
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
    void *old_value = get_value();

    value = blocked_reduce_accumulate_range(plan->accumulate_range_fn,
					    old_value, count, first);
    has_value = true;

    // TODO: finalize and deallocate old value if it's not initial_value
  };

  void join (BlockedReducer &other) {
    void *old_value1 = get_value();
    void *old_value2 = other.get_value();
    value = blocked_reduce_reducer(plan->reducer_fn, old_value1, old_value2);
    has_value = true;
    
    // TODO: finalize and deallocate old value if it's not initial_value
  };
};

void *
pyon_C_blocked_reduce(void *data,
		      void *initial_value,
		      PyonInt count)
{
#error "The TBB code is out of date and needs to be rewritten"
  BlockedReducePlan plan = {data, initial_value};

  // Use TBB's parallel_reduce template
  tbb::blocked_range<int> range(first, first + count);
  BlockedReducer body(&plan);
  tbb::parallel_reduce(range, body);

  // Return the result, which may be the initial value
  return body.get_value();
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
#error "The TBB code is out of date and needs to be rewritten"
  tbb::parallel_for(tbb::blocked_range<int>(first, first + count),
		    BlockedDoer(worker_fn));
}

#endif	// USE_TBB
