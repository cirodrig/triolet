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
# include "tbb/task_scheduler_init.h"
#endif

/*****************************************************************************/
/* Generalized parallel reduction */

/* Functions written in low-level triolet */

/* Do reduction over a range.
 * If the given value is not NULL, combine with the given value. */
extern "C" void *
greduce_range(void *reduce_fn, void *combine_fn,
              void *acc, void *off, void *range);

/* Split a range.  Return 0 if not splittable. */
extern "C" int
greduce_split(void *split_fn, void **out1, void **off2, void **out2,
              void *off, void *range);

/* Combine reduction values */
extern "C" void *
greduce_combine(void *combine_fn, void *x, void *y);

/* Create unit value */
extern "C" void *
greduce_unit(void *unit_fn);

extern "C" void *
triolet_C_greduce(void *zero_offset,
                  void *split_fn,
                  void *combine_fn,
                  void *reduce_fn,
                  void *unit_fn,
                  void *range);

#ifndef USE_TBB

void *
triolet_C_greduce(void *zero_offset,
                  void *split_fn,
                  void *combine_fn,
                  void *reduce_fn,
                  void *unit_fn,
                  void *range)
{
  return greduce_range(reduce_fn, combine_fn, NULL, zero_offset, range);
}

#else

// A domain, wrapped to satisfy the TBB range concept
class GReduceRange
{
  // Constants
  const void *split_fn;         // How to split a domain
  const void *no_offset;        // The null offset

  // Current value of this range as an (offset, domain) pair
  void *offset;
  void *value;

  // Cached values produced by splitting this range.
  // NULL if no values are cached.
  // Either all are NULL, or all are references to objects.
  void *split1;
  void *offset2;
  void *split2;

  GReduceRange(const GReduceRange &other)
    : split_fn(other.split_fn), no_offset(other.no_offset),
      offset(other.offset), value(other.value),
      split1(other.split1), offset2(other.offset2), split2(other.split2) {}

  GReduceRange(const void *_split_fn,
               const void *_no_offset,
               const void *_value)
    : split_fn(_split_fn), no_offset(_no_offset),
      offset(_no_offset), value(_value),
      split1(NULL), offset2(NULL), split2(NULL) {}

  GReduceRange(GReduceRange &other, tbb::split)
    : split_fn(other.split_fn), no_offset(_no_offset),
      split1(NULL), split2(NULL)
  {
    // Ensure that divisible parts are calculated
    if (other.split1 == NULL) other.is_divisible();

    // This object's range is (offset, split1)
    offset = other.offset;
    value = other.split1;

    // Other object's range is (offset2, split2)
    other.offset = other.offset2;
    other.value = other.split2;

    // Clear cached split info
    other.split1 = other.split2 = NULL;
    other.offset2 = NULL;
  }

  bool empty(void) const { return false; }

  bool is_divisible(void) const
  {
    int splittable = greduce_split(split_fn, &split1, &offset2, &split2,
                                   offset, value);
    if (!splittable) {
      split1 = split2 = NULL;
      offset2 = NULL;
    }
    return splittable;
  }

  void *getValue(void) const { return value; }
};

struct GReduceFunc
{
  const void *reduce_fn;
  const void *combine_fn;

  void *operator()(const GReduceRange &range, void *acc) {
    return greduce_range(reduce_fn, combine_fn, acc, range.offset, range.value);
  }
};

struct GReduceReduction
{
  const void *combine_fn;

  void *operator()(void *x, void *y) {
    return greduce_combine(combine_fn, x, y);
  };
};

void *
triolet_C_greduce(void *zero_offset,
                  void *split_fn,
                  void *combine_fn,
                  void *reduce_fn,
                  void *unit_fn,
                  void *range)
{
  GReduceFunc tbb_reduce = {reduce_fn, combine_fn};
  GReduceReduction tbb_reduction = {combine_fn};
  GReduceRange tbb_range(split_fn, zero_offset, range);

  void *p = tbb::parallel_reduce(tbb_range, tbb_reduce, tbb_reduction);

  // If no value was produced, then return a unit value
  if (p == NULL) {
    return greduce_unit(unit_fn);
  }
}

#endif

#if 0
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

  // Set grain size to (count / N_PROCESSORS / 2)
  // Rounding up
  int grain_size;
  {
    int divisor = 2 * tbb::task_scheduler_init::default_num_threads();
    grain_size = (count + divisor - 1) / divisor;
    if (grain_size == 0) grain_size = 1;
  }

  // Use TBB's parallel_reduce template
  tbb::blocked_range<int> range(0, count, grain_size);
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

#endif


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

/* Return nonzero if tree is splittable */
extern "C" int
triolet_PBTree_splittable(PBTree tree);

/* If tree is splittable, return nonzero, put left child in (*children)[0],
   and put right child in (*children)[1].  Otherwise, return zero. */
extern "C" int
triolet_PBTree_split(PBTree tree, PBTree (*children)[2]);

/* Return size of tree */
extern "C" int
triolet_PBTree_size(PBTree tree);

#ifndef USE_TBB

extern "C" void
triolet_C_blocked_PBTree_doall(PBTree tree, void *worker_fn)
{
  blocked_doall_PBTree_worker (worker_fn, 0, tree);
}

#else


struct PBTreeIntegerRange
{
  TrioletInt startRange;
  PBTree tree;

  PBTreeIntegerRange(PBTree t) : startRange(0), tree(t) {};

  bool empty() const { return triolet_PBTree_size(tree) == 0; }
  bool is_divisible() const { return triolet_PBTree_splittable(tree); }
  PBTreeIntegerRange(PBTreeIntegerRange& r, tbb::split)
  {
    PBTree children[2];
    int tree_size = triolet_PBTree_size(r.tree);
    int splittable = triolet_PBTree_split(r.tree, &children);

    if (!splittable)
    {
      fprintf(stderr, "triolet_C_blocked_PBtree_doall: Cannot split range\n");
      exit(-1);
    }

    //r.startRange = startRange;

    r.tree = children[0];

    startRange = r.startRange + triolet_PBTree_size(children[0]);
    tree = children[1];
  }
};

struct PBTreeRangeDoer
{
  void *worker_fn;
  
  PBTreeRangeDoer(void *_worker_fn) : worker_fn(_worker_fn) {};

  void operator()(PBTreeIntegerRange &range) const
  {
    TrioletInt start = range.startRange;
    blocked_doall_PBTree_worker(worker_fn, start, range.tree);
  }
};


extern "C" void
triolet_C_blocked_PBTree_doall(PBTree tree, void *worker_fn)
{
  tbb::parallel_for(PBTreeIntegerRange(tree), PBTreeRangeDoer(worker_fn));
}

#endif  // USE_TBB
