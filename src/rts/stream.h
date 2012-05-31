
// Allocate a stream and initialize its object header
extern procedure core.internal.stream.Stream_alloc () -> owned;

// The info table for stream objects
extern data pointer core.internal.stream.Stream_info;

extern data owned core.internal.stream.Stream_count;
