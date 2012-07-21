/* Record type definitions used in pyasm code */

// Header fields of an info table
record InfoTableHeader {
  const uint8 tag;                    // What kind of object this is
};

// Header fields of an object
record ObjectHeader {
  const pointer info;                 // Info table
};

record Obj(a) {
  const ObjectHeader header;
  const a payload;
};

// Size and alignment of an object
record SA {
  const uint size;
  const uint align;
};

// Object layout information
record Repr {
  const ObjectHeader header;
  const SA sizealign;          // Size and alignment in bytes
  const owned copy;                   // Duplicate a value
  const owned convert_to_boxed;	      // Convert a value to boxed type
  const owned convert_to_bare;	      // Convert a value to bare type
  const bool is_pointerless;	      // Is pointerless?
};

record FinIndInt {
  const int n;			// Finite value
};

#define FINITE uint8 0
#define POSINFTY uint8 1
#define NEGINFTY uint8 2

record IndInt {
  const uint8 tag;		// {FINITE, POSINFTY, NEGINFTY}
  const IndIntData val;		// if FINITE
};

record IndIntData {
  const FinIndInt val;
};

record SomeIndInt {
  const FinIndInt index;
};

// Function info table
record FunInfo(n_args) {
  const InfoTableHeader header;
  //const uint8 has_shared_closure; // True iff instances of the function share
                                // their closure with other functions.  Closure
                                // sharing is the result of recursive function
                                // definitions.
  const uint16 arity;	   // Number of arguments the function accepts
  const pointer exact;                // Exact entry point
  const pointer inexact;              // Inexact entry point
  const const_array(value n_args, uint8) arg_types; // Types of arguments
};

// Additive dictionary
record AdditiveDict(a) {
  const ObjectHeader header;
  const owned add;			// Add two values
  const owned subtract;			// A value minus another
  const owned negate;			// Negate a value
  const a zero;				// The zero value
};

// Multiplicative dictionary
record MultiplicativeDict(a) {
  const ObjectHeader header;
  const owned additive;			// Additive dictionary
  const owned mul;			// Multiply two values
  const owned fromInt;			// Create from an integer
  const a one;				// The one value
};

// Traversable dictionary
record TraversableDict {
  const ObjectHeader header;
  const owned traverse;               // Traverse an object
  const owned build;                  // Build an object
};

// Complex numbers
record complex(a) {
  const a real;
  const a imag;
};

// Unboxed 1-tuples
record U1Tuple(a) {
  a member;
};

// Core 1-tuples
record Tuple1(a) {
  const a member;
};

// Core 2-tuples
record Tuple2(a, b) {
  const a member1;
  const b member2;
};

// Mutable 2-tuples
record MTuple2(a, b) {
  a member1;
  b member2;
};

// Core 3-tuples
record Tuple3(a, b, c) {
  const a member1;
  const b member2;
  const c member3;
};

// Mutable 3-tuples
record MTuple3(a, b, c) {
  a member1;
  b member2;
  c member3;
};

// Core 4-tuples
record Tuple4(a, b, c, d) {
  const a member1;
  const b member2;
  const c member3;
  const d member4;
};

// Mutable 4-tuples
record MTuple4(a, b, c, d) {
  a member1;
  b member2;
  c member3;
  d member4;
};

// Core 5-tuples
record Tuple5(a, b, c, d, e, f) {
  const a member1;
  const b member2;
  const c member3;
  const d member4;
  const e member5;
};

// Core 6-tuples
record Tuple6(a, b, c, d, e, f) {
  const a member1;
  const b member2;
  const c member3;
  const d member4;
  const e member5;
  const f member6;
};

// A Maybe object
record Maybe(a) {
  uint8 isjust;			// 0 = Nothing; 1 = Just
  a member;			// Valid if isjust
};

// A boxed object
record Boxed(a) {
  const ObjectHeader header;
  const a member;
};

// Pairs of mutable objects
record Pair(a) {
  a fst;
  a snd;
};

record SliceObject {
  Maybe(int) lo_bound;
  Maybe(int) hi_bound;
  Maybe(Maybe(int)) stride;
};

/* Arrays (called "lists")
 *
 * A list consists of a size and a pointer to an array of list elements.
 * The list elements are arranged consecutively.
 * The list elements have a type and size; this is not stored in the
 * list, but rather passed to functions that operate on the list.
 */
record List {
  FinIndInt nelems;             // Number of elements in the list
  owned contents;		// Pointer to list contents
};

/* Append-lists
 *
 * A list-like data structure that supports mutable append
 */
record AppendList {
  FinIndInt nelems;             // Number of elements allocated for the list
  int used;                     // Number of elements in use
  owned contents;               // Pointer to list contents
};

/* List builders
 *
 * A list-like data structure that supports mutable append.
 * Almost identical to 'AppendList', but it's used by a different part of the
 * library.
 */
record ListBuilder {
  int nelems;                   // Number of elements allocated for the list
  int used;                     // Number of elements in use
  owned contents;               // Pointer to list contents
};

/* 0D arrays
 *
 * A 0-dimensional array contains just a single value.
 */
record Array0(a) {
  const a content;          // The single value contained in the array
};

/* 1D arrays
 *
 * An array has a lower bound, stride, and size.
 */
record Array1 {
  const int first;
  const int stride;
  const FinIndInt size;
  const owned contents;		// Pointer to matrix contents
};

/* 2D arrays
 *
 * An array has a lower and upper bound in each dimension.
 * The lower bound is inclusive and the upper bound is not.
 * The upper bound is greater than or equal to the lower bound.
 * The dimensions are given in the order (y, x).
 * Array elements are consecutive in the X dimension.
 */
record Array2 {
  const int first_y;
  const int stride_y;
  const FinIndInt size_y;
  const int first_x;
  const int stride_x;
  const FinIndInt size_x;
  const owned contents;		// Pointer to matrix contents
};

record Array3 {
  const int first_z;
  const int stride_z;
  const FinIndInt size_z;
  const int first_y;
  const int stride_y;
  const FinIndInt size_y;
  const int first_x;
  const int stride_x;
  const FinIndInt size_x;
  const owned contents;		// Pointer to matrix contents
};

#define PBTree_BRANCH uint8 0
#define PBTree_LEAF   uint8 1
#define PBTree_EMPTY  uint8 2
/* A tree for parallel list construction. */
record PBTree {
  const uint8 tag;              // {BRANCH, LEAF, EMPTY}
};

record PBTreeBranch {
  const uint8 tag;              // BRANCH
  const int size;
  const owned left;
  const owned right;
};

record PBTreeLeaf {
  const uint8 tag;              // LEAF
  const List members;
};

/* This data structure is used by 'blocked_reduce' to store data that's
 * used in C
 */
record BlockedReduceData {
  owned initial_value;
  owned generator;		// Function that generates and reduces values
  owned reducer;		// Function that reduces two values
};

/* This data structure is used by 'blocked_reduceip' to store data that's
 * used in C
 */
record BlockedReduceIPData {
  owned generator;		// Function that generates and reduces values
  owned reducer;		// Function that reduces two values
};

/* A stream of values.  Stream elements are computed on demand.
 *
 * next : state -> StreamNext
 *   Get the next stream element.
 */
record StreamData {
  const owned state;                  // Initial state of stream
  const owned next;                   // Function to get next stream value
};

#define STREAM_EMPTY (uint8 0)
#define STREAM_VALUE (uint8 1)

/* The result of pulling a value from a stream */
record StreamNext {
  const uint8 tag;		// {STREAM_EMPTY, STREAM_VALUE}
  const StreamNextData val;	// if STREAM_VALUE
};

record StreamNextData {
  const owned state;		// Next stream state
  const owned ret;		// Returned value
};
