/* Record type definitions used in pyasm code */

// Partial applications
record PAP(a) {
  const owned header;           // Object header
  const pointer papTag;         // NULL; distinguishes PAPs from functions
  const owned operator;         // Operator; a function or PAP
  const uint16 arity;           // Number of args not yet applied to function
  const a operand;              // Operand; a promoted function argument
};

record Function {
  const owned header;
  const pointer info;           // : FunInfo; Function info table
  // Closure-captured variables follow
};

record InfoTable {
  const uint16 arity;
  const uint16 captured;
  const pointer exact;
  const pointer inexact;
};

// Header fields of an info table
//record InfoTableHeader {
//  const uint8 tag;                    // What kind of object this is
//};

// Header fields of an object
//record ObjectHeader {
//  const pointer info;                 // Info table
//};

record Obj(a) {
  const owned header;
  const a payload;
};

// Size and alignment of an object
record SA {
  const uint size;
  const uint align;
  const uint pointerless;       // 0 = False; 1 = True
};

// Size and alignment of an object (stored in memory)
record SA_mem {
  const uint size;
  const uint align;
  const uint8 pointerless;       // 0 = False; 1 = True
};

#define NOT_A_REFERENCE uint8 0
#define IS_A_REFERENCE  uint8 1

// An 'IsRef' stored in memory
record IsRef_mem {
  uint8 tag;
};

// Object layout information stored in memory
record Repr_mem {
  const owned header;
  const SA_mem sizealign;      // Size and alignment in bytes
  const bool pointerless;      // True if object contains no pointers
  const IsRef_mem is_ref;      // Whether this 'Repr' describes a reference
};

// Type object information stored in memory
record TypeObject_mem {
  const owned header;
  const uint con_index;         // Data constructor index
  const owned serializer;
  const owned deserializer;
};

record FinIndInt {
  const int n;			// Finite value
};

#define FINITE uint 0
#define POSINFTY uint 1
#define NEGINFTY uint 2

record IndInt {
  const uint tag;		// {FINITE, POSINFTY, NEGINFTY}
  const IndIntData val;		// if FINITE
};

record IndIntData {
  const FinIndInt val;
};

record SomeIndInt {
  const FinIndInt index;
};

#define FUN_INFO uint 0
#define PAP_INFO uint 1

// Function info table
record FunInfo {
  const uint16 arity;	   // Number of arguments the function accepts
  const uint16 captured;   // Number of captured variables in a closure
  const pointer exact;                // Exact entry point
  const pointer inexact;              // Inexact entry point
};

// The values of a 'BitsTag'
#define BITS0TAG uint8 0
#define BITS32TAG uint8 1
#define BITS64TAG uint8 2
#define BITSOWNEDTAG uint8 3
#define BITSCURSORTAG uint8 4

// Data used for creating a buffer
record MkBuffer {
  owned header;                 // Object header
  pointer buffer;               // The buffer (array of bytes)
  pointer hashtable;            // Hash table of objects in buffer
                                // (array of owned pointers)
  pointer hashtable_count;      // Number of items in each hash bin
                                // (array of int)
  uint buffer_capacity;         // Number of allocated bytes in buffer
  uint buffer_size;             // Number of used bytes in buffer
  uint ht_capacity;             // Number of allocated entries in hash table
  uint ht_size;                 // Number of used entries in hash table
};

// Result of reading from a buffer
record ReadResult(a) {
  const cursor buffer;
  const a payload;
};

// A lazily evaluated global value.
// The payload is initialized to null, and is assigned when the value
// is forced.
record Lazy(a) {
  uint status;
  const pointer generator;      /* Procedure that generates this value */
  a payload;                    /* The generated value */
};

#define LAZY_UNEVALUATED uint 0 /* Not yet evaluated */
#define LAZY_BUSY        uint 1 /* Being evaluated */
#define LAZY_MANIFEST    uint 2 /* Has been computed */

// Unboxed 1-tuples
record U1Tuple(a) {
  a member;
};

// Core 1-tuples
record Tuple1(a) {
  const a member;
};

// Unboxed 2-tuples
record U2Tuple(a, b) {
  const a member1;
  const b member2;
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
  uint isjust;			// 0 = Nothing; 1 = Just
  a member;			// Valid if isjust
};

// A boxed object
record Boxed(a) {
  const owned header;
  const a member;
};

// Pairs of mutable objects
//record Pair(a) {
//  a fst;
//  a snd;
//};

//record SliceObject {
//  Maybe(int) lo_bound;
//  Maybe(int) hi_bound;
//  Maybe(Maybe(int)) stride;
//};

/* A hash table, consisting of a keys array and an indirections array
 */

record HashTable(n) {
  array(value n, int) keys;
  array(value n, uint) inds;
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
record Array0 {
  const owned content;          // The single value contained in this array
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
// FIXME: Eliminate the tag
record PBTree {
  const owned header;
  const uint8 tag;              // {BRANCH, LEAF, EMPTY}
};

record PBTreeBranch {
  const owned header;
  const uint8 tag;              // BRANCH
  const PBTreeBranch_other other;
};

record PBTreeBranch_other {
  const int size;
  const owned left;
  const owned right;
};

record PBTreeLeaf {
  const owned header;
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
