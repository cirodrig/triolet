
// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream constructors
extern function pyon.internal.stream.Stream_return
  (unit, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (unit, unit, owned, owned, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_generate
  (unit, unit, owned, int, owned) -> owned;
extern function pyon.internal.stream.Stream_map
  (unit, unit, unit, owned, owned, owned, owned) -> owned;
extern function pyon.internal.stream.Stream_reduce
  (unit, unit, owned, owned, owned, pointer, owned, pointer) -> ();

extern function pyon.internal.stream.reduce
  (unit, unit, unit, owned, owned, pointer, owned, pointer, pointer, pointer) -> ();
