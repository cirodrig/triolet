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

// Objet layout information
record PassConv {
  const ObjectHeader header;
  const uint size;                    // Size in bytes
  const uint align;                   // Alignment in bytes
  const owned copy;                   // Duplicate a value
  const owned convert_to_boxed;	      // Convert a value to boxed type
  const owned convert_to_bare;	      // Convert a value to bare type
  const owned finalize;               // Finalize a value
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

// Pyon 2-tuples
record PyonTuple2(a, b) {
  const a member1;
  const b member2;
};

// Mutable 2-tuples
record MPyonTuple2(a, b) {
  a member1;
  b member2;
};

// Pyon 3-tuples
record PyonTuple3(a, b, c) {
  const a member1;
  const b member2;
  const c member3;
};

// Mutable 3-tuples
record MPyonTuple3(a, b, c) {
  a member1;
  b member2;
  c member3;
};

// Pyon 4-tuples
record PyonTuple4(a, b, c, d) {
  const a member1;
  const b member2;
  const c member3;
  const d member4;
};

// Mutable 4-tuples
record MPyonTuple4(a, b, c, d) {
  a member1;
  b member2;
  c member3;
  d member4;
};

// Pyon 5-tuples
record PyonTuple5(a, b, c, d, e, f) {
  const a member1;
  const b member2;
  const c member3;
  const d member4;
  const e member5;
};

// Pyon 6-tuples
record PyonTuple6(a, b, c, d, e, f) {
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
record PyonList {
  FinIndInt nelems;		// Number of elements in the list.
                                // Actual allocated size may be larger.
  pointer contents;		// Pointer to list contents
};

/* 0D arrays
 *
 * A 0-dimensional array contains just a single value.
 */
record PyonArray0(a) {
  a content;                    // The single value contained in the array
};

/* 1D arrays
 *
 * An array has a lower bound, stride, and size.
 */
record PyonArray1 {
  int first;
  int stride;
  FinIndInt size;
  pointer contents;		// Pointer to matrix contents
};

/* 2D arrays
 *
 * An array has a lower and upper bound in each dimension.
 * The lower bound is inclusive and the upper bound is not.
 * The upper bound is greater than or equal to the lower bound.
 * The dimensions are given in the order (y, x).
 * Array elements are consecutive in the X dimension.
 */
record PyonArray2 {
  int first_y;
  int stride_y;
  FinIndInt size_y;
  int first_x;
  int stride_x;
  FinIndInt size_x;
  pointer contents;		// Pointer to matrix contents
};

record PyonArray3 {
  int first_z;
  int stride_z;
  FinIndInt size_z;
  int first_y;
  int stride_y;
  FinIndInt size_y;
  int first_x;
  int stride_x;
  FinIndInt size_x;
  pointer contents;		// Pointer to matrix contents
};

/* This data structure is used by 'blocked_reduce' to store data that's
 * used in C
 */
record BlockedReduceData {
  owned initial_value;
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
