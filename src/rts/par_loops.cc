// This file defines parallelized C/C++ algorithmic skeletons of loops.
//
// The algorithmic skeletons are called from Triolet code.  They call back into
// Triolet code to do the actual work.

#include <stdio.h>
#include <stdlib.h>

extern "C" {
#include "triolet.h"
}

#ifdef USE_TBB
# include "tbb/tbb_stddef.h"
# include "tbb/blocked_range.h"
# include "tbb/blocked_range2d.h"
# include "tbb/parallel_for.h"
# include "tbb/parallel_reduce.h"
#endif

/*****************************************************************************/
/* Parallelized reduction */

/* Functions written in low-level triolet */
extern "C" void *
blocked_reduce_accumulate_range(void *data, void *acc,
                                TrioletInt start, TrioletInt end);
extern "C" void *
blocked_reduce_reduce(void *data, void *x, void *y);


/* Function exported to triolet */
extern "C" void *
triolet_C_blocked_reduce(void *data,
                         void *initial_value,
                         TrioletInt count);



#ifndef USE_TBB

// No parallel implementation available; use sequential reduction
void *
triolet_C_blocked_reduce(void *data, void *initial_value, TrioletInt count)
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
triolet_C_blocked_reduce(void *data,
                         void *initial_value,
                         TrioletInt count)
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
/* Parallelized 2D reduction */

/* Functions written in low-level triolet */
extern "C" void *
blocked_reduce2_accumulate_range(void *data, void *acc,
                                 TrioletInt start_y, TrioletInt end_y,
                                 TrioletInt start_x, TrioletInt end_x);
extern "C" void *
blocked_reduce2_reduce(void *data, void *x, void *y);


/* Function exported to triolet */
extern "C" void *
triolet_C_blocked_reduce2(void *data,
                          void *initial_value,
                          TrioletInt count_y,
                          TrioletInt count_x);

#ifndef USE_TBB

// No parallel implementation available; use sequential reduction
void *
triolet_C_blocked_reduce2(void *data, void *initial_value,
                          TrioletInt count_y, TrioletInt count_x)
{
  // Perform the reduction
  return blocked_reduce2_accumulate_range(data, initial_value, 0, count_y, 0, count_x);
}

#else  // USE_TBB

// Parallel reduction using TBB

// Data that are constant over an invocation of 'blocked_reduce'.
struct BlockedReduce2Plan {
  void *data;
  void *initial_value;
};

// A partial reduction result, together with methods for computing a
// partial reduction and updating the result.
//
// Implements the parallel_reduce Body concept.
struct BlockedReducer2 {
  BlockedReduce2Plan *const plan;
  void *value;

  BlockedReducer2(BlockedReduce2Plan *_plan) :
    plan(_plan), value(_plan->initial_value) {};

  BlockedReducer2(BlockedReducer2 &other, tbb::split) :
    plan(other.plan), value(other.plan->initial_value) {};

  void operator()(const tbb::blocked_range2d<int> &range) {
    int start_y = range.rows().begin();
    int end_y = range.rows().end();
    int start_x = range.cols().begin();
    int end_x = range.cols().end();
    value = blocked_reduce2_accumulate_range(plan->data, value, start_y, end_y, start_x, end_x);
  };

  void join (BlockedReducer2 &other) {
    value = blocked_reduce2_reduce(plan->data, value, other.value);
  };
};

void *
triolet_C_blocked_reduce2(void *data,
                          void *initial_value,
                          TrioletInt count_y,
                          TrioletInt count_x)
{
  BlockedReduce2Plan plan = {data, initial_value};

  // Use TBB's parallel_reduce template
  tbb::blocked_range2d<int> range(0, count_y, 0, count_x);
  BlockedReducer2 body(&plan);
  tbb::parallel_reduce(range, body);

  // Return the result, which may be the initial value
  return body.value;
}

#endif	// USE_TBB

/*****************************************************************************/
/* Parallelized reduction with in-place generator */

/* Functions written in low-level triolet */
extern "C" void *
blocked_reduceip_generate_range(void *data, TrioletInt start, TrioletInt end);
extern "C" void *
blocked_reduceip_reduce(void *data, void *x, void *y);

/* Function exported to triolet */
extern "C" void *
triolet_C_blocked_reduceip(void *data, TrioletInt count);

#ifndef USE_TBB

// No parallel implementation available; use sequential reduction
void *
triolet_C_blocked_reduceip(void *data, TrioletInt count)
{
  // Perform the reduction
  return blocked_reduceip_generate_range(data, 0, count);
}

#else  // USE_TBB

// Parallel reduction using TBB

// Data that are constant over an invocation of 'blocked_reduceip'.
struct BlockedReduceIPPlan {
  void *data;
};

// A partial reduction computation, together with methods for computing a
// partial reduction and updating the result.
//
// Contents are NULL until operator() is called.  This operator must be
// called before join().
//
// Implements the parallel_reduce Body concept.
struct BlockedInPlaceReducer {
  BlockedReduceIPPlan *const plan;
  bool has_value;
  void *value;

  BlockedInPlaceReducer(BlockedReduceIPPlan *_plan) :
    plan(_plan), has_value(false), value(NULL) {};

  BlockedInPlaceReducer(BlockedInPlaceReducer &other, tbb::split) :
    plan(other.plan), has_value(false), value(NULL) {};

  void operator()(const tbb::blocked_range<int> &range) {
    int start = range.begin();
    int end = range.end();

    /* Compute result over this range */
    void *new_value = blocked_reduceip_generate_range(plan->data, start, end);

    if (has_value) {
      /* Merge new value with existing value */
      value = blocked_reduceip_reduce(plan->data, value, new_value);
    }
    else {
      /* Store value */
      value = new_value;
      has_value = true;
    }
  };

  void join (BlockedInPlaceReducer &other) {
    /* Combine with the old value */
    if (!has_value || !other.has_value) {
      fprintf(stderr, "triolet_C_blocked_reduceip: "
              "Unexpected uninitialized value\n");
      exit(-1);
    }

    value = blocked_reduceip_reduce(plan->data, value, other.value);
  };
};

void *
triolet_C_blocked_reduceip(void *data_value, TrioletInt count)
{
  BlockedReduceIPPlan plan = {data_value};

  // Use TBB's parallel_reduce template
  tbb::blocked_range<int> range(0, count);
  BlockedInPlaceReducer body(&plan);
  tbb::parallel_reduce(range, body);

  // Return the result
  if (!body.has_value) {
    fprintf(stderr, "triolet_C_blocked_reduceip: "
            "Unexpected uninitialized value\n");
    exit(-1);
  }
  return body.value;
}

#endif	// USE_TBB

/*****************************************************************************/
/* Parallelized doall */

/* Functions written in low-level triolet */
extern "C" void
blocked_doall_worker(void *worker_fn, TrioletInt start, TrioletInt end);

/* Function exported to triolet */
extern "C" void
triolet_C_blocked_doall(void *worker_fn, TrioletInt count);

#ifndef USE_TBB

// Sequential implementation: do everything in one thread
extern "C" void
triolet_C_blocked_doall(void *worker_fn, TrioletInt count)
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
triolet_C_blocked_doall(void *data, TrioletInt count)
{
  tbb::parallel_for(tbb::blocked_range<int>(0, count),
		    BlockedDoer(data));
}

#endif	// USE_TBB

/*****************************************************************************/
/* Parallelized 2D doall */

/* Functions written in low-level triolet */
extern "C" void
blocked_doall2_worker(void *worker_fn,
                      TrioletInt start_y, TrioletInt end_y,
                      TrioletInt start_x, TrioletInt end_x);

/* Function exported to triolet */
extern "C" void
triolet_C_blocked_doall2(void *worker_fn, TrioletInt count_y, TrioletInt count_x);

#ifndef USE_TBB

extern "C" void
triolet_C_blocked_doall2(void *worker_fn, TrioletInt count_y, TrioletInt count_x)
{
  blocked_doall2_worker(worker_fn, 0, count_y, 0, count_x);
}

#else

// Parallel loop partitioned using TBB

struct BlockedDoer2 {
  void *data;

  BlockedDoer2(void *_data) : data(_data) {}

  void operator()(tbb::blocked_range2d<int> &range) const {
    int first_y = range.rows().begin();
    int end_y = range.rows().end();
    int first_x = range.cols().begin();
    int end_x = range.cols().end(); 
    blocked_doall2_worker(data, first_y, end_y, first_x, end_x);
  }
};

extern "C" void
triolet_C_blocked_doall2(void *data, TrioletInt count_y, TrioletInt count_x)
{
  tbb::parallel_for(tbb::blocked_range2d<int>(0, count_y, 0, count_x),
		    BlockedDoer2(data));
}

#endif // USE_TBB

/*****************************************************************************/
/* Parallelized tree-of-array doall */

typedef void *PBTree;

/* Functions written in low-level triolet */
extern "C" void
blocked_doall_PBTree_worker(void *worker_fn, TrioletInt i, PBTree tree);

extern "C" int
triolet_PBTree_splittable(PBTree tree);

extern "C" int
triolet_PBTree_split(PBTree tree, PBTree (*children)[2]);

#ifdef USE_TBB

extern "C" void
triolet_C_blocked_PBTree_doall(PBTree tree, void *worker_fn)
{
  blocked_doall_PBTree_worker (worker_fn, 0, tree);
}

#else 

extern "C" void
triolet_C_blocked_PBTree_doall(PBTree tree, void *worker_fn)
{
  fprintf(stderr, "triolet_C_blocked_PBTree_doall: Not implemented\n");
  exit(-1);
}

#endif  // USE_TBB
