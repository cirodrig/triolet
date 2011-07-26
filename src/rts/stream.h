
// Allocate a stream and initialize its object header
extern procedure pyon.internal.stream.Stream_alloc () -> owned;

// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

extern function pyon.internal.stream.histogramArray
  (FinIndInt, owned, pointer) -> ();

extern function pyon.internal.stream.createHistogram
  (FinIndInt, owned, pointer) -> ();

extern data owned pyon.internal.stream.Stream_count;
