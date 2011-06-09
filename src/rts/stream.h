
// Allocate a stream and initialize its object header
extern procedure pyon.internal.stream.Stream_alloc () -> owned;

// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream traversable methods
extern function pyon.internal.stream.Stream_traverse
  (owned, owned) -> owned;

extern function pyon.internal.stream.Stream_build
  (owned, owned) -> owned;

// Stream constructors and functions
extern function pyon.internal.stream.Stream_return
  (owned, owned) -> owned;
//extern function pyon.internal.stream.Stream_empty
//  (unit, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (owned, owned, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_guard
  (owned, bool, owned) -> owned;
extern function pyon.internal.stream.Stream_generate
  (owned, int, owned) -> owned;

extern function pyon.internal.stream.Stream_asList
  (owned) -> owned;

extern function pyon.internal.stream.Stream_map
  (owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.map
  (owned, owned, owned, owned, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_reduce
  (owned, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.stream.reduce
  (owned, owned, owned, pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_reduce1
  (owned, owned, owned, pointer) -> ();

extern function pyon.internal.stream.reduce1
  (owned, owned, owned, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_fold
  (owned, owned, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.stream.histogram
  (int, owned, pointer) -> ();

extern function pyon.internal.stream.histogramArray
  (FinIndInt, owned, pointer) -> ();

extern function pyon.internal.stream.createHistogram
  (FinIndInt, owned, pointer) -> ();

extern function pyon.internal.stream.Stream_zip
  (owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip
  (owned, owned, owned,
   pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_zip3
  (owned, owned, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip3
  (owned, owned, owned, owned,
   pointer, pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_zip4
  (owned, owned, owned, owned, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip4
  (owned, owned, owned, owned, owned,
   pointer, pointer, pointer, pointer, pointer) -> ();

extern data owned pyon.internal.stream.Stream_count;

extern function pyon.internal.stream.Stream_range (int) -> owned;

extern function pyon.internal.stream.Stream_rangeIndexed
  (IndInt) -> owned;

extern function pyon.internal.stream.generate
  (IndInt, owned, owned) -> owned;
