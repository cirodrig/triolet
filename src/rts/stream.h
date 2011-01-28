
// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream constructors
extern function pyon.internal.stream.Stream_return
  (unit, pointer, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (unit, unit, pointer, pointer, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_generate
  (unit, unit, pointer, int, owned) -> owned;
extern function pyon.internal.stream.Stream_map
  (unit, unit, unit, pointer, pointer, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_reduce
  (unit, unit, pointer, pointer, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.stream.reduce
  (unit, unit, unit, pointer, pointer, pointer, owned, pointer, pointer, pointer) -> ();
