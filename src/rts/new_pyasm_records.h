/* Record type definitions used in pyasm code */

// Header fields of an info table
record InfoTableHeader {
  const pointer dealloc;              // How to deallocate an object
  const uint8 tag;                    // What kind of object this is
};

// Header fields of an object
record ObjectHeader {
  int refct;                    // Reference count
  const pointer info;                 // Info table
};

// Objet layout information
record PassConv {
  const word size;                    // Size in bytes
  const word align;                   // Alignment in bytes
  const owned copy;                   // Duplicate a value
  const owned finalize;               // Finalize a value
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
  const owned add;			// Add two values
  const owned subtract;		// A value minus another
  const owned negate;			// Negate a value
  const a zero;			// The zero value
};

// Multiplicative dictionary
record MultiplicativeDict(a) {
  const AdditiveDict(a) additive;     // Additive dictionary
  const owned mul;			// Multiply two values
  const owned fromInt;		// Create from an integer
  const a one;			// The one value
};

// Traversable dictionary
record TraversableDict {
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

// Pairs of objects
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
  const word nelems;			// Number of elements in the list.
                                // Actual allocated size may be larger.
  const pointer contents;		// Pointer to list contents
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
  const ObjectHeader header;
  const owned next;                   // How to get the next stream element
  const owned initialize;             // How to initialize the stream state
  const PassConv return_repr;		// Representation of return value
  const PassConv state_repr;		// Representation of stream state.
                                      // The copy function will not be used.
};
