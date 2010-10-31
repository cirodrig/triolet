
// The info table for stream objects
extern data pointer pyon.internal.stream.Stream_info;

// Stream constructors
extern function pyon.internal.stream.Stream_return
  (pointer, owned) -> owned;
extern function pyon.internal.stream.Stream_bind
  (pointer, pointer, owned, owned) -> owned;
