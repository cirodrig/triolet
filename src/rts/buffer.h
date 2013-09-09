
// Helper functions for array serialization
extern function core.internal.buffer.putArrWithSerializer
  (FinIndInt, SA, owned, cursor, owned, unit) -> unit;
extern function core.internal.buffer.getArrWithSerializer
  (FinIndInt, owned, owned, owned, cursor) -> ReadResult(owned);

extern function core.internal.buffer.putInt (int, owned, unit) -> unit;
extern function core.internal.buffer.putUint (uint, owned, unit) -> unit;
extern function core.internal.buffer.putUintAsUint8 (uint, owned, unit) -> unit;
extern function core.internal.buffer.putUintAsUint16 (uint, owned, unit) -> unit;
extern function core.internal.buffer.putFloat (float, owned, unit) -> unit;
extern function core.internal.buffer.putByte (uint8, owned, unit) -> unit;
extern function core.internal.buffer.putInt64 (int64, owned, unit) -> unit;
extern function core.internal.buffer.putUnit (unit, owned, unit) -> unit;
extern function core.internal.buffer.putPointer (pointer, owned, unit) -> unit;
extern function core.internal.buffer.putCursor (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredInt (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredUint (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredFloat (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredByte (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredInt64 (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putStoredCursor (cursor, owned, unit) -> unit;
extern function core.internal.buffer.putBoxedObject (owned, owned, unit) -> unit;

extern function core.internal.buffer.putListSection_low_level (FinIndInt, owned, owned, owned, unit) -> unit;
extern function core.internal.buffer.getListSection_low_level (owned, owned, cursor) -> ReadResult(owned);

extern function core.internal.buffer.getInt (owned, cursor) -> ReadResult(int);
extern function core.internal.buffer.getUint (owned, cursor) -> ReadResult(uint);
extern function core.internal.buffer.getUint8AsUint (owned, cursor) -> ReadResult(uint);
extern function core.internal.buffer.getUint16AsUint (owned, cursor) -> ReadResult(uint);
extern function core.internal.buffer.getFloat (owned, cursor) -> ReadResult(float);
extern function core.internal.buffer.getByte (owned, cursor) -> ReadResult(uint8);
extern function core.internal.buffer.getInt64 (owned, cursor) -> ReadResult(int64);
extern function core.internal.buffer.getUnit (owned, cursor) -> ReadResult(unit);
extern function core.internal.buffer.getPointer (owned, cursor) -> ReadResult(pointer);
extern function core.internal.buffer.getCursor (owned, cursor) -> ReadResult(cursor);
extern function core.internal.buffer.getStoredInt (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredUint (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredFloat (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredByte (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredInt64 (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getStoredCursor (owned, cursor) -> ReadResult(owned);
extern function core.internal.buffer.getBoxedObject (owned, cursor) -> ReadResult(owned);

extern function core.internal.buffer.serializeBoxedObject(owned) -> (uint, pointer);
extern function core.internal.buffer.deserializeBoxedObject(uint32, pointer) -> owned;

extern function core.internal.buffer.updateDeserializationTable (owned, owned) -> unit;

extern function core.internal.buffer.testCopyViaBuffer (owned, owned) -> owned;

// Defined in memory_map.c
extern data pointer builtin.Triolet_library_address_start
  "Triolet_library_address_start";
extern data pointer builtin.Triolet_program_address_start
  "Triolet_program_address_start";
import procedure triolet_library_pointer_offset (pointer) -> uint32;
import procedure triolet_program_pointer_offset (pointer) -> uint32;

