
// Helper functions for array serialization
extern function core.internal.buffer.putArrWithSerializer
  (FinIndInt, SA, owned, cursor, owned, unit) -> unit;
extern function core.internal.buffer.getArrWithSerializer
  (FinIndInt, SA, owned, cursor) -> ReadResult(owned);

extern function core.internal.buffer.putInt (int, owned, unit) -> unit;
extern function core.internal.buffer.putUint (uint, owned, unit) -> unit;
extern function core.internal.buffer.putUintAsUint8 (uint, owned, unit) -> unit;
extern function core.internal.buffer.putUintAsUint16 (uint, owned, unit) -> unit;
extern function core.internal.buffer.putFloat (float, owned, unit) -> unit;
extern function core.internal.buffer.putUnit (unit, owned, unit) -> unit;
extern function core.internal.buffer.putPointer (pointer, owned, unit) -> unit;
extern function core.internal.buffer.putCursor (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredInt (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredUint (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredFloat (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putBoxedObject (owned, owned, unit) -> unit;

extern function core.internal.buffer.getInt (cursor) -> ReadResult(int);
extern function core.internal.buffer.getUint (cursor) -> ReadResult(uint);
extern function core.internal.buffer.getUint8AsUint (cursor) -> ReadResult(uint);
extern function core.internal.buffer.getUint16AsUint (cursor) -> ReadResult(uint);
extern function core.internal.buffer.getFloat (cursor) -> ReadResult(float);
extern function core.internal.buffer.getUnit (cursor) -> ReadResult(unit);
extern function core.internal.buffer.getPointer (cursor) -> ReadResult(pointer);
extern function core.internal.buffer.getCursor (cursor) -> ReadResult(cursor);
extern function core.internal.buffer.getStoredInt (cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredUint (cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredFloat (cursor) -> ReadResult(owned);
extern function core.internal.buffer.getBoxedObject (cursor) -> ReadResult(owned);

extern function core.internal.buffer.testCopyViaBuffer (owned, owned) -> owned;
