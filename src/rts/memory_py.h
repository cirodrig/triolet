
import pointer pyon_alloc;
import pointer pyon_dealloc;
import pointer memcpy;

extern owned pyon.internal.memory_py.deallocF;
extern owned pyon.internal.memory_py.dummy_finalizer "dummy_finalizer";
extern owned pyon.internal.memory_py.copy1F "copy1F";
extern owned pyon.internal.memory_py.copy2F "copy2F";
extern owned pyon.internal.memory_py.copy4F "copy4F";
