
// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream constructors
extern function pyon.internal.stream.Stream_return
  (unit, unit, pointer, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (unit, unit, unit, pointer, pointer, owned, owned) -> owned;
