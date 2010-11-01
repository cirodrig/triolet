
import procedure pyon_alloc (word) -> pointer;
import procedure pyon_dealloc (pointer) -> ();
import procedure memcpy (pointer, pointer, word) -> ();

extern function pyon.internal.memory_py.deallocF (pointer) -> ();
extern function pyon.internal.memory_py.dummy_finalizer "dummy_finalizer"
  (pointer) -> ();
extern function pyon.internal.memory_py.copy1F "copy1F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy2F "copy2F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy4F "copy4F"
  (pointer, pointer) -> ();
extern function pyon.internal.memory_py.copy
  (unit, pointer, pointer, pointer) -> ();
