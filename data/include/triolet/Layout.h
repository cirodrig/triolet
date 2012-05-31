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

namespace Triolet {

  /* Allocate a bare object inside a box.
   * The box consists of a pointer and the bare object. */
  extern "C" TriBoxPtr
  triolet_alloc_boxed(uint32_t size, uint32_t alignment);

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
# define TRIOLET_OBJECT_HEADER_SIZE (sizeof(void *))
  extern "C" const TrioletUInt triolet_List_size;
  extern "C" const TrioletUInt triolet_List_alignment;
  extern "C" void
  triolet_List_initialize(TrioletInt length,
                       TrioletUInt elt_size,
                       TrioletUInt elt_align,
                       TriBarePtr ret);
  extern "C" TriBarePtr
  triolet_List_get_contents(TriBarePtr list,
                         TrioletUInt elt_size,
                         TrioletUInt elt_align) __attribute__((pure));
  extern "C" TrioletUInt
  triolet_List_get_length(TriBarePtr list) __attribute__((pure));

  extern "C" TrioletUInt
  triolet_Array0_size(TrioletUInt elt_size,
                   TrioletUInt elt_align) __attribute__((const));
  extern "C" TrioletUInt
  triolet_Array0_alignment(TrioletUInt elt_size,
                        TrioletUInt elt_align) __attribute__((const));
  extern "C" TriBarePtr
  triolet_Array0_get_contents(TriBarePtr array,
                           TrioletUInt elt_size,
                           TrioletUInt elt_align) __attribute__((pure));

  extern "C" const TrioletUInt triolet_Array1_size;
  extern "C" const TrioletUInt triolet_Array1_alignment;
  extern "C" void
  triolet_Array1_initialize(TrioletInt min,
                         TrioletInt stride,
                         TrioletInt size,
                         TrioletUInt elt_size,
                         TrioletUInt elt_align,
                         TriBarePtr ret);
  extern "C" TriBarePtr
  triolet_Array1_get_contents(TriBarePtr array,
                           TrioletUInt elt_size,
                           TrioletUInt elt_align) __attribute__((pure));

  struct Array1Bounds {
    int32_t min;
    int32_t stride;
    int32_t size;
  };
  extern "C" Array1Bounds
  triolet_Array1_get_bounds(TriBarePtr array) __attribute__((pure));

  extern "C" const TrioletUInt triolet_Array2_size;
  extern "C" const TrioletUInt triolet_Array2_alignment;
  extern "C" void
  triolet_Array2_initialize(TrioletInt y_min,
                         TrioletInt y_stride,
                         TrioletInt y_size,
                         TrioletInt x_min,
                         TrioletInt x_stride,
                         TrioletInt x_size,
                         TrioletUInt elt_size,
                         TrioletUInt elt_align,
                         TriBarePtr ret);
  extern "C" TriBarePtr
  triolet_Array2_get_contents(TriBarePtr array,
                           TrioletUInt elt_size,
                           TrioletUInt elt_align) __attribute__((pure));
  
  struct Array2Bounds {
    int32_t ymin;
    int32_t ystride;
    int32_t ysize;
    int32_t xmin;
    int32_t xstride;
    int32_t xsize;
  };
  extern "C" Array2Bounds
  triolet_Array2_get_bounds(TriBarePtr array) __attribute__((pure));

  extern "C" const TrioletUInt triolet_Array3_size;
  extern "C" const TrioletUInt triolet_Array3_alignment;
  extern "C" void
  triolet_Array3_initialize(TrioletInt z_min,
                         TrioletInt z_stride,
                         TrioletInt z_size,
                         TrioletInt y_min,
                         TrioletInt y_stride,
                         TrioletInt y_size,
                         TrioletInt x_min,
                         TrioletInt x_stride,
                         TrioletInt x_size,
                         TrioletUInt elt_size,
                         TrioletUInt elt_align,
                         TriBarePtr ret);

  extern "C" TriBarePtr
  triolet_Array3_get_contents(TriBarePtr array,
                           TrioletUInt elt_size,
                           TrioletUInt elt_align) __attribute__((pure));

  struct Array3Bounds {
    int32_t zmin;
    int32_t zstride;
    int32_t zsize;
    int32_t ymin;
    int32_t ystride;
    int32_t ysize;
    int32_t xmin;
    int32_t xstride;
    int32_t xsize;
  };
  extern "C" Array3Bounds
  triolet_Array3_get_bounds(TriBarePtr array) __attribute__((pure));
}

#endif
