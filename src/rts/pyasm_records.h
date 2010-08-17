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


/* A stream of values.  Stream elements are computed on demand.
 *
 * next : (pointer to state, (owned to output -> bool)) -> bool
 *   Get the next stream element and pass it to the consumer function.
 *   Keep passing values to the consumer function until it returns True
 *   or the stream is depleted.  Return True if the consumer returns True,
 *   False otherwise.
 *
 * initialize : pointer to state -> ()
 *   Initialize the stream state.
 */
record Stream {
  ObjectHeader header;
  owned next;                   // How to get the next stream element
  owned initialize;             // How to initialize the stream state
  word state_size;              // Size of stream state
  word state_align;             // Alignment of stream state
  owned state_finalize;         // Finalizer for stream state
};
