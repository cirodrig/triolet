
import procedure pyon_alloc (uint) -> pointer;
import procedure pyon_alloc_nopointers (uint) -> pointer;
import procedure pyon_dealloc (pointer) -> ();
import procedure memcpy (pointer, pointer, word) -> ();

extern function pyon.internal.memory_py.deallocF (pointer) -> ();
extern function pyon.internal.memory_py.copy1F "copy1F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy2F "copy2F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy4F "copy4F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy8F "copy8F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy
  (owned, pointer, pointer) -> ();
