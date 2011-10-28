/* This is an internal C++ header file.  Do not include this directly. */

/* Low-level data layout computation.
 *
 * Explicit byte arithmetic is used to compute the size of Pyon objects and
 * the position of object fields.
 *
 * Each bare object is described by a size and an alignment (see
 * 'BareType').  Composite objects consist of the bytes of their fields
 * in the same order as the fields themselves, plus the
 * minimum amount of padding bytes between fields required to
 * satisfy alignment constraints.  There is never any padding at the
 * beginning of an object.  Most objects have no padding at the
 * end. Arrays have padding bytes after each array element,
 * including the last one.
 *
 * Tuple and array layouts are computed here.  Layouts of
 * other objects are computed using functions that were compiled through
 * the pyon compiler.
 */

#ifndef _PYON_LAYOUT_H
#define _PYON_LAYOUT_H

namespace Pyon {

  /* Allocate a bare object inside a box.
   * The box consists of a pointer and the bare object. */
  extern "C" PyonBoxPtr
  pyon_alloc_boxed(uint32_t size, uint32_t alignment);

  /* The offset of an address, relative to the starting offset of some
   * object.  An offset of 0 is assumed to have infinite alignment. */
  typedef unsigned int offset;

  /* Pad an offset to a power-of-two alignment */
  static inline offset
  addPadding(offset o, unsigned int alignment)
  {
    /* The additive inverse of 'o' modulo 'alignment' */
    offset negative_o = (1 + ~o) % alignment;
    return o + negative_o;
  }

  /* Pad an offset to a power-of-two alignment */
  template<typename bare_type>
  static inline offset
  addPadding(offset o)
  {
    return addPadding(o, bare_type::getAlignment());
  }

  /* Allocate some space onto an offset */
  static inline offset
  addBytes(offset o, unsigned int size)
  {
    return o + size;
  }

  /* Allocate some space onto an offset */
  template<typename bare_type>
  static inline offset
  addBytes(offset o)
  {
    return o + bare_type::getSize();
  }

  /* Allocate space for an object, including initial padding */
  static inline offset
  allocateObject(offset o, unsigned int size, unsigned int alignment)
  {
    return addBytes(addPadding(o, alignment), size);
  }

  /* Allocate space for an object, including initial padding */
  template<typename bare_type>
  static inline offset
  allocateObject(offset o)
  {
    return allocateObject(o, bare_type::getSize(), bare_type::getAlignment());
  }

  /* Layout and member access of various data structures */
  extern "C" const PyonUInt pyon_List_size;
  extern "C" const PyonUInt pyon_List_alignment;
  extern "C" void
  pyon_List_initialize(PyonInt length,
                       PyonUInt elt_size,
                       PyonUInt elt_align,
                       PyonBarePtr ret);
  extern "C" PyonBarePtr
  pyon_List_get_contents(PyonBarePtr list) __attribute__((pure));

  extern "C" PyonUInt
  pyon_Array0_size(PyonUInt elt_size,
                   PyonUInt elt_align) __attribute__((const));
  extern "C" PyonUInt
  pyon_Array0_alignment(PyonUInt elt_size,
                        PyonUInt elt_align) __attribute__((const));
  extern "C" PyonBarePtr
  pyon_Array0_get_contents(PyonBarePtr array,
                           PyonUInt elt_size,
                           PyonUInt elt_align) __attribute__((pure));

  extern "C" const PyonUInt pyon_Array1_size;
  extern "C" const PyonUInt pyon_Array1_alignment;
  extern "C" void
  pyon_Array1_initialize(PyonInt min,
                         PyonInt end,
                         PyonUInt elt_size,
                         PyonUInt elt_align,
                         PyonBarePtr ret);
  extern "C" PyonBarePtr
  pyon_Array1_get_contents(PyonBarePtr array) __attribute__((pure));

  struct Array1Bounds {
    int32_t min;
    int32_t end;
  };
  extern "C" Array1Bounds
  pyon_Array1_get_bounds(PyonBarePtr array) __attribute__((pure));

  extern "C" const PyonUInt pyon_Array2_size;
  extern "C" const PyonUInt pyon_Array2_alignment;
  extern "C" void
  pyon_Array2_initialize(PyonInt y_min,
                         PyonInt y_end,
                         PyonInt x_min,
                         PyonInt x_end,
                         PyonUInt elt_size,
                         PyonUInt elt_align,
                         PyonBarePtr ret);
  extern "C" PyonBarePtr
  pyon_Array2_get_contents(PyonBarePtr array) __attribute__((pure));
  
  struct Array2Bounds {
    int32_t ymin;
    int32_t yend;
    int32_t xmin;
    int32_t xend;
  };
  extern "C" Array2Bounds
  pyon_Array2_get_bounds(PyonBarePtr array) __attribute__((pure));
}

#endif
