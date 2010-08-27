/* C functions and data structure layout information used within Pyon code.
 *
 * This header file is automatically included when compiling pyon files via
 * the C backend.
 */

#include <inttypes.h>
#include "pyon_types.h"
#include "pyon_list.h"

/* Very low-level pointer manipulation.
 * Add a byte offset to a pointer. */
#define PYON_OFF(base, offset) ((PyonPtr)((char *)(base) + (offset)))

#define PYON_OFF_TYPE(base, offset, type) ((type *)((char *)(base) + (offset)))

#define PYON_OFF_U8(base, offset) PYON_OFF_TYPE(base, offset, uint8_t)
#define PYON_OFF_I8(base, offset) PYON_OFF_TYPE(base, offset, int8_t)
#define PYON_OFF_U16(base, offset) PYON_OFF_TYPE(base, offset, uint16_t)
#define PYON_OFF_I16(base, offset) PYON_OFF_TYPE(base, offset, int16_t)
#define PYON_OFF_U32(base, offset) PYON_OFF_TYPE(base, offset, uint32_t)
#define PYON_OFF_I32(base, offset) PYON_OFF_TYPE(base, offset, int32_t)
#define PYON_OFF_U64(base, offset) PYON_OFF_TYPE(base, offset, uint64_t)
#define PYON_OFF_I64(base, offset) PYON_OFF_TYPE(base, offset, int64_t)
#define PYON_OFF_F32(base, offset) PYON_OFF_TYPE(base, offset, float)
#define PYON_OFF_F64(base, offset) PYON_OFF_TYPE(base, offset, double)
#define PYON_OFF_PTR(base, offset) PYON_OFF_TYPE(base, offset, PyonPtr)

/* An object's 'free' method */
typedef void (*PyonFreeFunc)(PyonPtr);


