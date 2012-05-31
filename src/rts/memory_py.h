
import procedure triolet_alloc (uint) -> pointer;
import procedure triolet_alloc_nopointers (uint) -> pointer;
import procedure triolet_dealloc (pointer) -> ();
import procedure memcpy (pointer, pointer, word) -> ();

extern function core.internal.memory_py.deallocF (pointer) -> ();
extern function core.internal.memory_py.copy1F "copy1F"
  (pointer, pointer) -> unit;
extern function core.internal.memory_py.copy2F "copy2F"
  (pointer, pointer) -> unit;
extern function core.internal.memory_py.copy4F "copy4F"
  (pointer, pointer) -> unit;
extern function core.internal.memory_py.copy8F "copy8F"
  (pointer, pointer) -> unit;
extern function core.internal.memory_py.copy
  (owned, pointer, pointer) -> unit;
