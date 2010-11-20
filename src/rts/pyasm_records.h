/* Record type definitions used in pyasm code */

// Header fields of an info table
record InfoTableHeader {
  pointer dealloc;              // How to deallocate an object
  uint8 tag;                    // What kind of object this is
};

// Header fields of an object
record ObjectHeader {
  int refct;                    // Reference count
  pointer info;                 // Info table
};

// Objet layout information
record PassConv {
  word size;                    // Size in bytes
  word align;                   // Alignment in bytes
  owned copy;                   // Duplicate a value
  owned finalize;               // Finalize a value
};

// Function info table
record FunInfoHeader {
  InfoTableHeader header;
  uint8 has_shared_closure;     // True iff instances of the function share
                                // their closure with other functions.  Closure
                                // sharing is the result of recursive function
                                // definitions.
  uint16 arity;                 // Number of arguments the function accepts
  pointer exact;                // Exact entry point
  pointer inexact;              // Inexact entry point
};

// PAP/function instance header
record PAPHeader {
  ObjectHeader header;		// Object header
  uint16 nargs;                 // Number of arguments that have been applied
};

// Additive dictionary
record AdditiveDict(a) {
  PassConv repr;		// Represesntation of the data type
  owned add;			// Add two values
  owned subtract;		// A value minus another
  owned negate;			// Negate a value
  a zero;			// The zero value
};

// Multiplicative dictionary
record MultiplicativeDict(a) {
  AdditiveDict(a) additive;     // Additive dictionary
  owned mul;			// Multiply two values
  owned fromInt;		// Create from an integer
  a one;			// The one value
};

// Traversable dictionary
record TraversableDict {
  owned traverse;               // Traverse an object
  owned build;                  // Build an object
};

// Complex numbers
record complex(a) {
  a real;
  a imag;
};

// Pairs of objects; 2-tuples
record Pair(a) {
  a fst;
  a snd;
};

/* Arrays (called "lists")
 *
 * A list consists of a size and a pointer to an array of list elements.
 * The list elements are arranged consecutively.
 * The list elements have a type and size; this is not stored in the
 * list, but rather passed to functions that operate on the list.
 */
record PyonList {
  word nelems;			// Number of elements in the list.
                                // Actual allocated size may be larger.
  pointer contents;		// Pointer to list contents
};

/* A stream of values.  Stream elements are computed on demand.
 *
 * next : (pointer to state, pointer to output) -> bool
 *   Get the next stream element.
 *   Return True if an element is available, False otherwise.
 *
 * initialize : pointer to state -> ()
 *   Initialize the stream state.
 */
record Stream {
  ObjectHeader header;
  owned next;                   // How to get the next stream element
  owned initialize;             // How to initialize the stream state
  PassConv return_repr;		// Representation of return value
  word state_size;              // Size of stream state
  word state_align;             // Alignment of stream state
  owned state_finalize;         // Finalizer for stream state
};
