
// Allocate a stream and initialize its object header
extern procedure pyon.internal.stream.Stream_alloc () -> owned;

// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream traversable methods
extern function pyon.internal.stream.Stream_traverse
  (unit, owned, owned) -> owned;

extern function pyon.internal.stream.Stream_build
  (unit, owned, owned) -> owned;

// Stream constructors and functions
extern function pyon.internal.stream.Stream_return
  (unit, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (unit, unit, owned, owned, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_generate
  (unit, unit, owned, int, owned) -> owned;

extern function pyon.internal.stream.Stream_map
  (unit, unit, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.map
  (unit, unit, unit, unit, owned, owned, owned, owned, owned, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_reduce
  (unit, owned, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.stream.reduce
  (unit, unit, owned, owned, owned, pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_reduce1
  (unit, owned, owned, owned, pointer) -> ();

extern function pyon.internal.stream.reduce1
  (unit, unit, owned, owned, owned, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_zip
  (unit, unit, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip
  (unit, unit, unit, unit, unit, owned, owned, owned, owned, owned,
   pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_zip3
  (unit, unit, unit, owned, owned, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip3
  (unit, unit, unit, unit, unit, unit, unit,
   owned, owned, owned, owned, owned, owned, owned,
   pointer, pointer, pointer, pointer) -> ();

extern function pyon.internal.stream.Stream_zip4
  (unit, unit, unit, unit,
   owned, owned, owned, owned, owned, owned, owned, owned) -> owned;

extern function pyon.internal.stream.zip4
  (unit, unit, unit, unit, unit, unit, unit, unit, unit,
   owned, owned, owned, owned, owned, owned, owned, owned, owned,
   pointer, pointer, pointer, pointer, pointer) -> ();

extern data owned pyon.internal.stream.Stream_count;

extern function pyon.internal.stream.generate
  (unit, unit, IndexedInt, owned, owned) -> owned;