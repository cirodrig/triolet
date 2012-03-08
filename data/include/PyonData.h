
/* C++ data marshaling interface for Pyon
 */

#ifndef PYON_DATA_H
#define PYON_DATA_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <pyon.h>
#include <pyon/Base.h>
#include <pyon/Layout.h>

#include "inttypes.h"

namespace Pyon {

  /****************************************************************************/
  /* Concept checks */

  template<class T>
  void ValType_concept(T x);

  template<class T>
  void BareType_concept(T x);

  template<class T>
  void BoxType_concept(T x);

  /****************************************************************************/
  /* Wrappers for specific type constructors  */

  template<typename val_type> class Stored;
  template<typename bare_type> class Boxed;
  template<typename box_type> class StuckRef;
  template<typename bare_type> class Incomplete;

  /****************************************************************************/
  /* Kind conversions */

  template<typename kind, typename pyon_type> struct AsBareTypeWithTag;
  template<typename pyon_type> struct AsBareType;

  /* Compute the bare type corresponding to a Pyon type.  The type
   * is computed by dispatching on the type's kind.
   */
  template<typename pyon_type>
  struct AsBareType {
    typedef typename AsBareTypeWithTag<typename pyon_type::kind,
				       pyon_type>::type type;
  };

  /* This class is used by 'AsBareType' */
  template<typename kind, typename pyon_type>
  struct AsBareTypeWithTag {
#if BEGIN_SIGNATURE
    typedef _ type;
#endif
  };

  template<typename pyon_type>
  struct AsBareTypeWithTag<BareKindTag, pyon_type> {
    typedef pyon_type type;
  };

  template<typename pyon_type>
  struct AsBareTypeWithTag<ValKindTag, pyon_type> {
    typedef Stored<pyon_type> type;
  };

  /* The bare type corresponding to a Boxed object is its unboxed form */
  template<typename bare_type>
  struct AsBareTypeWithTag<BoxKindTag, Boxed<bare_type> > {
    typedef bare_type type;
  };

  template<typename kind, typename pyon_type> struct AsBoxTypeWithTag;
  template<typename pyon_type> struct AsBoxType;

  /* Compute the boxed type corresponding to a Pyon type.  The type
   * is computed by dispatching on the type's kind.
   */
  template<typename pyon_type>
  struct AsBoxType {
    typedef typename AsBoxTypeWithTag<typename pyon_type::kind,
				        pyon_type>::type type;
  };

  /* This class is used by 'AsBoxType' */
  template<typename kind, typename pyon_type>
  struct AsBoxTypeWithTag {
#if BEGIN_SIGNATURE
    typedef _ type;
#endif
  };

  template<typename pyon_type>
  struct AsBoxTypeWithTag<BoxKindTag, pyon_type> {
    typedef pyon_type type;
  };

  template<typename pyon_type>
  struct AsBoxTypeWithTag<ValKindTag, pyon_type> {
    typedef Boxed<Stored<pyon_type> > type;
  };

  /* The boxed type corresponding to any other object is its wrapped form */
  template<typename bare_type>
  struct AsBoxTypeWithTag<BareKindTag, bare_type> {
    typedef Boxed<bare_type> type;
  };

  /****************************************************************************/
  /* Incomplete objects */

  /* A reference to an incomplete object consisting of a single chunk
   * of memory.  This is used as the base class for most Incomplete objects.
   *
   * This object has three states.
   *
   * 1. No object is referenced.  'owner' and 'object' are NULL.
   *
   * 2. A bare object is referenced, and it's stored in a box owned by this
   *    incomplete object reference.  'owner' points
   *    to the box.  'object' points to the object.  This state is
   *    entered by 'allocate' and left by 'freeze'.
   *
   * 3. A bare object stored somewhere else is referenced.  'owner' is NULL.
   *    'object' points to the object.  New incomplete objects are created in
   *    this state by some incomplete object methods.  This state can also
   *    be entered by assignment.
   *
   * Incomplete references of type 3 are derived from an incomplete
   * reference of type 2, and they are only valid as long as their
   * parent reference is valid.  For reasons of efficiency, no attempt
   * is made to detect whether the parent reference is valid.
   */
  template<typename bare_type>
  class IncompleteSingleRef {
  private:
    PyonBoxPtr owner;
    PyonBarePtr object;

  public:
    // Exactly one of the following three predicates is true at any time.
    bool isEmpty(void) const {return object == NULL;}
    bool isOwner(void) const {return owner != NULL;}
    bool isBorrowed(void) const {return object != NULL && owner == NULL;}

  public:
    // Construct an empty incomplete reference
    IncompleteSingleRef(void) : owner(NULL), object(NULL) {}

    // Construct a borrowed incomplete reference
    IncompleteSingleRef(PyonBarePtr _s) : owner(NULL), object(_s) {}

    IncompleteSingleRef(const IncompleteSingleRef& other) {
      // Cannot copy incomplete references that own an object
      if (other.isOwner()) {
        pyonError ("Cannot copy a reference to an allocated object");
      }
      owner = NULL;
      object = other.object;
    }
    
    PyonBarePtr getObject() { return object; }

    void operator=(const IncompleteSingleRef& other) {
      // Cannot copy incomplete references that own an object
      if (other.isOwner()) {
        pyonError ("Cannot copy a reference to an allocated object");
      }

      // If the reference owns an object, release it first
      if (isOwner()) {
        freeze(); // Freeze and discard the result
      }

      owner = NULL;
      object = other.object;
    }

    void allocate(void) {
      if (!isEmpty()) {
        pyonError("Incomplete object is already referencing an object");
      }

      // Create boxed object and initialize header
      owner = pyon_alloc_boxed(bare_type::getSize(), bare_type::getAlignment());

      // Get pointer to the bare object
      object = (PyonBarePtr) ((char *)owner) + addPadding<bare_type>(sizeof(void *));
    }

    bare_type freeze(void) {
      if (!isOwner()) {
        pyonError("No incomplete object reference");
      }
      PyonBarePtr ret = object;
      object = NULL;
      owner = NULL;
      return bare_type(ret);
    }
  };

  template<typename boxed_type>
  class IncompleteBoxedRef {
  private:
    PyonBoxPtr object;

  public:
    bool isEmpty(void) const {return object == NULL;}
    bool isOwner(void) const {return object != NULL;}
    bool isBorrowed(void) const {return false;}

  public:
    // Construct an empty incomplete reference
    IncompleteBoxedRef(void) : object(NULL) {}

    PyonBoxPtr getObject() { return object; }

    void allocate(void) {
      if (!isEmpty()) {
        pyonError("Incomplete object is already referencing an object");
      }
      // Create boxed object and initialize header
      object = pyon_alloc_boxed(boxed_type::getSize(), boxed_type::getAlignment());
    }

    boxed_type freeze(void) {
      if (!isOwner()) {
        pyonError("No incomplete object reference");
      }
      boxed_type ret(object);
      object = NULL;
      return ret;
    }
  };

  /* Abstract template of incomplete objects.  Only specializations
   * should be used.
   *
   * Incomplete bare objects have three states.
   *
   * 1. No object is referenced.
   *
   * 2. A bare object is referenced, and it's stored in a box owned by
   *    this incomplete object reference.  'owner' points to the box.
   *    'object' points to the object.  This state is entered by
   *    'allocate' and left by 'freeze'.
   *
   * 3. A bare object stored somewhere else is referenced.  'owner' is NULL.
   *    'object' points to the object.  New incomplete objects are created in
   *    this state by some incomplete object methods.  This state can also
   *    be entered by assignment.
   *
   * Incomplete references of type 3 are derived from an incomplete reference
   * of type 2, and they are only valid as long as their parent reference is
   * valid.  For reasons of efficiency, no attempt is made to detect whether the
   * parent reference is valid.
   *
   * Incomplete boxed objects have two states.
   *
   * 1. No object is referenced.
   *
   * 2. A boxed object is referenced.
   *
   * For boxed objects, there is no state corresponding to state 3 above.
   */
  template<typename bare_type>
  class Incomplete {

    void create(const typename bare_type::initializer& i)
    {
      this->allocate();
      initialize(i);
    }
#if BEGIN_SIGNATURE
  public:
    // Exactly one of the following three predicates is true at any time.
    bool isEmpty(void) const;
    bool isOwner(void) const;
    bool isBorrowed(void) const;

    Incomplete(void);
    Incomplete(const Incomplete &other);

    void allocate(void);
    void initialize(const bare_type::initializer&);

    // These convenience functions should provide the same functionality
    // as the functions that take a bare_type::initializer argument
    void initialize(...);
    void create(...) { allocate(); initialize(...); }

    bare_type freeze(void);
#endif
  };




/******************************************************************************/
/*                             Class Summary                                  */
/******************************************************************************/

  /* C++ Wrapper Classes that wrap value objects (extend class ValType) */

  class NoneType;

  class Int;

  class Bool;

  class Float;

  /* C++ Wrapper Classes that wrap bare objects (extend class BareType) */

    template<typename T1, typename T2, typename T3 = void, typename T4 = void>
  class Tuple;
  
    template<typename T1, typename T2, typename T3>
  class Tuple<T1,T2,T3,void>;

    template<typename T1, typename T2>
  class Tuple<T1,T2,void,void>;

    template<typename T>
  class List;

    template<typename T>
  class BList;
  
    template<typename T>
  class Array1;
  
    template<typename T>
  class Array2;

    template<typename T>
  class Array3;
  
    template<typename T>
  class BArray1;
  
    template<typename T>
  class BArray2;

    template<typename T>
  class BArray3;

  /* Stored Classes: BareType versions of ValType classes (specializations of 
   * class Stored, extend class BareType ) */

    template<typename T>
  class Stored;

    template<>
  class Stored<NoneType>;

  /* Incomplete BareType Objects (specializations of Incomplete, inherit from
   * IncompleteSingleRef) */

    template<typename T>
  class Incomplete < StuckRef<T> >;

    template<typename T>
  class Incomplete < Stored<T> >;

    template<typename T1, typename T2, typename T3, typename T4>
  class Incomplete< Tuple<T1,T2,T3,T4> >;

    template<typename T1, typename T2, typename T3>
  class Incomplete< Tuple<T1,T2,T3> >;

    template<typename T1, typename T2>
  class Incomplete< Tuple<T1,T2> >;

    template<typename T>
  class Incomplete< List<T> >;

    template<typename T>
  class Incomplete< BList<T> >;

    template<typename T>
  class Incomplete< Array1<T> >;

    template<typename T>
  class Incomplete< Array2<T> >;

    template<typename T>
  class Incomplete< Array3<T> >;

    template<typename T>
  class Incomplete< BArray1<T> >;

    template<typename T>
  class Incomplete< BArray2<T> >;

    template<typename T>
  class Incomplete< BArray3<T> >;

  /* Incomplete BoxType Objects (specializations of Incomplete, inherit from
   * IncompleteBoxedRef) */
    template<typename T>
  class Incomplete<Boxed<T> >;

/******************************************************************************/
/*              C++ Wrapper Classes that wrap value objects                   */
/******************************************************************************/

  /* Implementation of the NoneType wrapper */

  class NoneType : public ValType {
    public:
      typedef NoneType type;

    NoneType(void) {}
    NoneType(const NoneType &x) {}
    inline operator Boxed<Stored<NoneType> >() const;
  };

  /* Implementation of the Int wrapper */

  class Int : public ValType {
    public:
      typedef int32_t type;
      int32_t nativeElement;

      Int(int32_t i) { nativeElement = i; }
      Int(const Stored<Int> &s);
      operator int32_t() { return nativeElement; }
      inline operator Boxed<Stored<Int> >() const;
  };

  /* Implementation of the Bool wrapper */

  class Bool : public ValType {
    public:
      typedef char type;
      int nativeElement;

      Bool(char b) { nativeElement = b; }
      Bool(const Stored<Bool> &s);
      operator int() { return nativeElement; }
      inline operator Boxed<Stored<Bool> >() const;
  };

  /* Implementation of the Float wrapper */

  class Float : public ValType {
    public:
      typedef float type;
      float nativeElement;

      Float(float f) { nativeElement = f; }
      Float(const Stored<Float> &s);
      operator float() { return nativeElement; }
      inline operator Boxed<Stored<Float> >() const;
  };


/******************************************************************************/
/*               C++ Wrapper Classes that wrap boxed objects                  */
/******************************************************************************/

  /* A reference to a boxed object.
   *
   * This reference type is _not_ removed by 'AsBare'.
   */
  template<typename T>
  class StuckRef : public BareType {
  private:
    typedef typename AsBoxType<T>::type T_Box;
  public:
    typedef typename T_Box::initializer initializer;
    static initializer defaultInitializer(void)
    {return T_Box::defaultInitializer();}

    StuckRef(PyonBarePtr _bare_data) : BareType(_bare_data) {}

    static unsigned int getSize(void) {return sizeof(PyonBoxPtr);}
    static unsigned int getAlignment(void) {return __alignof__(PyonBoxPtr);}
    static void copy(StuckRef<T> ref, Incomplete<StuckRef<T> >&incompleteRef)
    {
      incompleteRef = ref;
    }
    static bool isPOD(void) {return false;}

    operator T_Box() {
      return T_Box(*(PyonBoxPtr*)getBareData());
    }
  };

/******************************************************************************/
/*               C++ Wrapper Classes that wrap bare objects                   */
/******************************************************************************/

  /* A box for holding bare objects.
   *
   * It consists of a header pointer followed by aligned data.
   */
  template<typename T>
  class Boxed : public BoxType {
  private:
    typedef typename AsBareType<T>::type T_Bare;
  public:
    typedef typename T_Bare::initializer initializer;

  public:
    Boxed(PyonBoxPtr p) : BoxType(p) {}
    PyonBarePtr getContents(void) const
    {
      /* Compute size of header plus padding */
      unsigned int contents_offset =
        addPadding<T_Bare>(PYON_OBJECT_HEADER_SIZE);
      return (PyonBarePtr)((char *)getBoxData() + contents_offset);
    }

    static unsigned int getSize(void)
    { return allocateObject<T_Bare>(PYON_OBJECT_HEADER_SIZE); }

    static unsigned int getAlignment(void)
    {
      unsigned int bare_align = T_Bare::getAlignment();
      return (bare_align > PYON_OBJECT_HEADER_SIZE)
        ? bare_align : PYON_OBJECT_HEADER_SIZE;
    }
    operator T() const {
      return T(getContents());
    }
  };


/* ----------------------- Tuple with 4 elements ---------------------------- */

	  /* Helper struct get_return_type to select type from list based on index */

    template<int index, typename T1, typename T2, typename T3 = void, typename T4 = void>
  struct get_return_type {
    // T1 when index=0 , T2 when index=1 , T3 when index=2 , T4 when index=2
    typedef void type;
    // Helper function that creates an object of the right type to be returned
    static type 
    get_return_object(Tuple<T1, T2, T3, T4>* tuple);
    /* Helper function to create an incomplete bare object of the right type to 
     * be returned */
    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3,T4> >* incompleteTuple);
  };

  /* Implementation of Tuple */

  template<typename T1, typename T2, typename T3, typename T4>
  class Tuple : public BareType {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
      typedef typename AsBareType<T3>::type T3_Bare;
      typedef typename AsBareType<T4>::type T4_Bare;
    public:
      struct initializer {
        typename T1_Bare::initializer init_1;
        typename T2_Bare::initializer init_2;
        typename T3_Bare::initializer init_3;
        typename T4_Bare::initializer init_4;

        initializer(const typename T1_Bare::initializer& i1,
                    const typename T2_Bare::initializer& i2,
                    const typename T3_Bare::initializer& i3,
                    const typename T4_Bare::initializer& i4)
          : init_1(i1), init_2(i2), init_3(i3), init_4(i4) {}
      };
      static initializer defaultInitializer(void) {
        return initializer(T1_Bare::defaultInitializer(),
                           T2_Bare::defaultInitializer(),
                           T3_Bare::defaultInitializer(),
                           T4_Bare::defaultInitializer());
      }
    public:
      // Constructors
      Tuple<T1, T2, T3, T4>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        int t1Size = addPadding<T2_Bare>(T1_Bare::getSize());
        int t2Size = addPadding<T3_Bare>(T2_Bare::getSize());
        int t3Size = addPadding<T4_Bare>(T3_Bare::getSize());
        int t4Size = T4_Bare::getSize();
        return t1Size + t2Size + t3Size + t4Size;
      }
      
      static unsigned int 
      getAlignment() { 
        int t1Alignment = T1_Bare::getAlignment();
        int t2Alignment = T2_Bare::getAlignment();
        int t3Alignment = T3_Bare::getAlignment();
        int t4Alignment = T4_Bare::getAlignment();
        int max = (t1Alignment > t2Alignment) ? t1Alignment : t2Alignment;
        max = (max > t3Alignment) ? max : t3Alignment;
        max = (max > t4Alignment) ? max : t4Alignment;
        return max; 
      }
      
      static void 
      copy(Tuple<T1,T2,T3,T4> tuple, Incomplete< Tuple<T1,T2,T3,T4> > &incompleteTuple) {
        Incomplete<T1_Bare> i1(incompleteTuple.get<0>());
        T1_Bare::copy(tuple.get<0>(), i1);
        Incomplete<T2_Bare> i2(incompleteTuple.get<1>());
        T2_Bare::copy(tuple.get<1>(), i2);
        Incomplete<T3_Bare> i3(incompleteTuple.get<2>());
        T3_Bare::copy(tuple.get<2>(), i3);
        Incomplete<T4_Bare> i4(incompleteTuple.get<3>());
        T4_Bare::copy(tuple.get<3>(), i4);
      }
      
      static bool 
      isPOD() { return T1_Bare::isPOD() && T2_Bare::isPOD() &&
                       T3_Bare::isPOD() && T4_Bare::isPOD(); }

      // Member Functions
        template<int index>
      typename get_return_type<index, T1, T2, T3, T4>::type 
      get() { return get_return_type<index, T1, T2, T3, T4>::get_return_object(this); }

  };

  /* Specialization of get_return_type helper struct */

    template<typename T1, typename T2, typename T3, typename T4>
  struct get_return_type<0, T1, T2, T3, T4> {
    typedef typename AsBareType<T1>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3, T4>* tuple) {
      return type(tuple->getBareData());
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3,T4> >* incompleteTuple) {
      return Incomplete<type>(incompleteTuple->getObject());
    }
  };
  
    template<typename T1, typename T2, typename T3, typename T4>
  struct get_return_type<1, T1, T2, T3, T4> {
    typedef typename AsBareType<T2>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3, T4>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return type(tuple->getBareData() + t1Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3,T4> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size);
    }
  };
  
    template<typename T1, typename T2, typename T3, typename T4>
  struct get_return_type<2, T1, T2, T3, T4> {
    typedef typename AsBareType<T3>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3, T4>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      return type(tuple->getBareData() + t1Size + t2Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3,T4> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size + t2Size);
    }
  };

    template<typename T1, typename T2, typename T3, typename T4>
  struct get_return_type<3, T1, T2, T3, T4> {
    typedef typename AsBareType<T4>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3, T4>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      int t3Size = addPadding< typename AsBareType<T4>::type >(AsBareType<T3>::type::getSize());
      return type(tuple->getBareData() + t1Size + t2Size + t3Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3,T4> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      int t3Size = addPadding< typename AsBareType<T4>::type >(AsBareType<T3>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size + t2Size + t3Size);
    }
  };

/* ----------------------- Tuple with 3 elements ---------------------------- */

	  /* Helper struct get_return_type to select type from list based on index */

    template<int index, typename T1, typename T2, typename T3>
  struct get_return_type<index,T1,T2,T3,void> {
    // T1 when index=0 , T2 when index=1 , T3 when index=2
    typedef void type;
    // Helper function that creates an object of the right type to be returned
    static type 
    get_return_object(Tuple<T1, T2, T3>* tuple);
    /* Helper function to create an incomplete bare object of the right type to 
     * be returned */
    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3> >* incompleteTuple);
  };

  /* Implementation of Tuple */

  template<typename T1, typename T2, typename T3>
  class Tuple<T1,T2,T3,void> : public BareType {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
      typedef typename AsBareType<T3>::type T3_Bare;
    public:
      struct initializer {
        typename T1_Bare::initializer init_1;
        typename T2_Bare::initializer init_2;
        typename T3_Bare::initializer init_3;

        initializer(const typename T1_Bare::initializer& i1,
                    const typename T2_Bare::initializer& i2,
                    const typename T3_Bare::initializer& i3)
          : init_1(i1), init_2(i2), init_3(i3) {}
      };
      static initializer defaultInitializer(void) {
        return initializer(T1_Bare::defaultInitializer(),
                           T2_Bare::defaultInitializer(),
                           T3_Bare::defaultInitializer());
      }
    public:
      // Constructors
      Tuple<T1, T2, T3>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        int t1Size = addPadding<T2_Bare>(T1_Bare::getSize());
        int t2Size = addPadding<T3_Bare>(T2_Bare::getSize());
        int t3Size = T3_Bare::getSize();
        return t1Size + t2Size + t3Size;
      }
      
      static unsigned int 
      getAlignment() { 
        int t1Alignment = T1_Bare::getAlignment();
        int t2Alignment = T2_Bare::getAlignment();
        int t3Alignment = T3_Bare::getAlignment();
        int max = (t1Alignment > t2Alignment) ? t1Alignment : t2Alignment;
        max = (max > t3Alignment) ? max : t3Alignment;
        return max; 
      }
      
      static void 
      copy(Tuple<T1,T2,T3> tuple, Incomplete< Tuple<T1,T2,T3> > &incompleteTuple) { 
        Incomplete<T1_Bare> i1(incompleteTuple.get<0>());
        T1_Bare::copy(tuple.get<0>(), i1);
        Incomplete<T2_Bare> i2(incompleteTuple.get<1>());
        T2_Bare::copy(tuple.get<1>(), i2);
        Incomplete<T3_Bare> i3(incompleteTuple.get<2>());
        T3_Bare::copy(tuple.get<2>(), i3);
      }
      
      static bool 
      isPOD() { return T1_Bare::isPOD() && T2_Bare::isPOD() && T3_Bare::isPOD(); }

      // Member Functions
        template<int index>
      typename get_return_type<index, T1, T2, T3>::type 
      get() { return get_return_type<index, T1, T2, T3>::get_return_object(this); }

  };

  /* Specialization of get_return_type helper struct */

    template<typename T1, typename T2, typename T3>
  struct get_return_type<0, T1, T2, T3, void> {
    typedef typename AsBareType<T1>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3>* tuple) {
      return type(tuple->getBareData());
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3> >* incompleteTuple) {
      return Incomplete<type>(incompleteTuple->getObject());
    }
  };
  
    template<typename T1, typename T2, typename T3>
  struct get_return_type<1, T1, T2, T3, void> {
    typedef typename AsBareType<T2>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return type(tuple->getBareData() + t1Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size);
    }
  };
  
    template<typename T1, typename T2, typename T3>
  struct get_return_type<2, T1, T2, T3, void> {
    typedef typename AsBareType<T3>::type type;

    static type 
    get_return_object(Tuple<T1, T2, T3>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      return type(tuple->getBareData() + t1Size + t2Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2,T3> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      int t2Size = addPadding< typename AsBareType<T3>::type >(AsBareType<T2>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size + t2Size);
    }
  };

/* ----------------------- Tuple with 2 elements ---------------------------- */

	  /* Helper struct get_return_type to select type from list based on index */

    template<int index, typename T1, typename T2>
  struct get_return_type<index,T1,T2,void,void> {
    // T1 when index=0 , T2 when index=1
    typedef void type;
    // Helper function that creates an object of the right type to be returned
    static type 
    get_return_object(Tuple<T1, T2>* tuple);
    /* Helper function to create an incomplete bare object of the right type to 
     * be returned */
    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2> >* incompleteTuple);
  };

  /* Implementation of Tuple */

  template<typename T1, typename T2>
  class Tuple<T1,T2,void,void> : public BareType {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
    public:
      struct initializer {
        typename T1_Bare::initializer init_1;
        typename T2_Bare::initializer init_2;

        initializer(const typename T1_Bare::initializer& i1,
                    const typename T2_Bare::initializer& i2)
          : init_1(i1), init_2(i2) {}
      };
      static initializer defaultInitializer(void) {
        return initializer(T1_Bare::defaultInitializer(),
                           T2_Bare::defaultInitializer());
      }
    public:
      // Constructors
      Tuple<T1,T2>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        int t1Size = addPadding<T2_Bare>(T1_Bare::getSize());
        int t2Size = T2_Bare::getSize();
        return t1Size + t2Size;
      }
      
      static unsigned int 
      getAlignment() { 
        int t1Alignment = T1_Bare::getAlignment();
        int t2Alignment = T2_Bare::getAlignment();
        return (t1Alignment > t2Alignment) ? t1Alignment : t2Alignment; 
      }
      
      static void 
      copy(Tuple<T1,T2> tuple, Incomplete< Tuple<T1,T2> > &incompleteTuple) { 
        Incomplete<T1_Bare> i1(incompleteTuple.get<0>());
        T1_Bare::copy(tuple.get<0>(), i1);
        Incomplete<T2_Bare> i2(incompleteTuple.get<1>());
        T2_Bare::copy(tuple.get<1>(), i2);
      }
      
      static bool 
      isPOD() { return T1_Bare::isPOD() && T2_Bare::isPOD(); }

      // Member Functions
        template<int index>
      typename get_return_type<index, T1, T2>::type 
      get() { return get_return_type<index, T1, T2>::get_return_object(this); }

  };

  /* Specialization of get_return_type helper struct */

    template<typename T1, typename T2>
  struct get_return_type<0, T1, T2, void, void> {
    typedef typename AsBareType<T1>::type type;

    static type 
    get_return_object(Tuple<T1, T2>* tuple) {
      return type(tuple->getBareData());
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2> >* incompleteTuple) {
      return Incomplete<type>(incompleteTuple->getObject());
    }
  };
  
    template<typename T1, typename T2>
  struct get_return_type<1, T1, T2, void, void> {
    typedef typename AsBareType<T2>::type type;

    static type 
    get_return_object(Tuple<T1, T2>* tuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return type(tuple->getBareData() + t1Size);
    }

    static Incomplete<type> 
    get_incomplete_return_object(Incomplete< Tuple<T1,T2> >* incompleteTuple) {
      int t1Size = addPadding< typename AsBareType<T2>::type >(AsBareType<T1>::type::getSize());
      return Incomplete<type>(incompleteTuple->getObject() + t1Size);
    }
  };


/* -------------------------------- List ------------------------------------ */

  template<typename T>
  class List : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      struct initializer {
        int length;
        initializer(int _length) : length(_length) {};
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      List<T>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_List_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_List_alignment;
      }
      
      static void 
      copy(List<T> list, Incomplete< List<T> > &incompleteList) { 
        if (!incompleteList.isEmpty()) {
          pyonError("Attempted to write an already-initalized list\n");
        }

        /* Create the new list */
        int length = pyon_List_get_length(list.getBareData());
        incompleteList.create(length);

        /* Copy list contents */
        int i;
        for (i = 0; i < length; i++)
          incompleteList.at(i) = list.at(i);
      }
      
      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Bare 
      at(int index) { 
        PyonBarePtr list_contents = pyon_List_get_contents(getBareData());
        return T_Bare(list_contents + index*addPadding<T_Bare>(T_Bare::getSize()) ); 
      }

  };


/* -------------------------------- BList ----------------------------------- */

  template<typename T>
  class BList : public BareType {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      struct initializer {
        int length;
        initializer(int _length) : length(_length) {};
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      BList<T>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_List_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_List_alignment;
      }
      
      static void 
      copy(BList<T> list, Incomplete<BList<T> > &incompleteList) { 
        if (!incompleteList.isEmpty()) {
          pyonError("Attempted to write an already-initalized list\n");
        }

        /* Create the new list */
        int length = pyon_List_get_length(list.getBareData());
        incompleteList.create(length);

        /* Copy list contents.  It's an array of pointers. */
        PyonBarePtr src_array =
          pyon_List_get_contents(list.getBareData());
        PyonBarePtr dst_array =
          pyon_List_get_contents(incompleteList.getObject());
        memcpy(dst_array, src_array, length * sizeof(PyonBoxPtr));
      }

      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Box
      at(int index) { 
        PyonBoxPtr *list_contents =
          (PyonBoxPtr *)pyon_List_get_contents(getBareData());
        return T_Box(list_contents[index]);
      }
  };


/* ------------------------------- Array1 ----------------------------------- */

  template<typename T>
  class Array1 : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      struct initializer {
        int min;
        int end;
        initializer(int _min, int _end) : min(_min), end(_end) {};
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      Array1<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array1_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array1_alignment;
      }
      
      static void 
      copy(Array1<T> array1, Incomplete< Array1<T> > &incompleteArray1) { 
        if (!incompleteArray1.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array1Bounds bounds = pyon_Array1_get_bounds(array1.getBareData());
        if (bounds.stride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray1.create(bounds.min, bounds.min + bounds.size);

        /* Copy array contents */
        int i;
        for (i = 0; i < bounds.size; i++) {
          int ix = bounds.min + i * bounds.stride;
          incompleteArray1.at(i) = array1.at(i);
        }
      }
      
      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Bare 
      at(int index) { 
        Array1Bounds array1Bounds = pyon_Array1_get_bounds(getBareData());
        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t displacement = index - array1Bounds.min;
        int i = displacement / array1Bounds.stride;
        if (displacement % array1Bounds.stride != 0)
          pyonError("Array index out of bounds\n");

        PyonBarePtr array1_contents = pyon_Array1_get_contents(getBareData());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return T_Bare(array1_contents + i * element_size);
      }

  };

/* ------------------------------- BArray1 ---------------------------------- */

  template<typename T>
  class BArray1 : public BareType {
    /* BArray1 has the same memory layout as Array1.  However, the array
     * elements are pointers to boxed objects. */
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      struct initializer {
        int min;
        int end;
        initializer(int _min, int _end) : min(_min), end(_end) {};
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      BArray1<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array1_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array1_alignment;
      }
      
      static void 
      copy(BArray1<T> array1, Incomplete< BArray1<T> > &incompleteArray1) {
        if (!incompleteArray1.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array1Bounds bounds = pyon_Array1_get_bounds(array1.getBareData());
        if (bounds.stride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray1.create(bounds.min, bounds.min + bounds.size);

        /* Copy array contents, which is an array of pointers */
        PyonBarePtr dst_array =
          pyon_Array1_get_contents(incompleteArray1.getObject());
        PyonBarePtr src_array =
          pyon_Array1_get_contents(array1.getBareData());
        memcpy(dst_array, src_array, bounds.size * sizeof(PyonBoxPtr));
      }
      
      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Box
      at(int index) { 
        Array1Bounds array1Bounds = pyon_Array1_get_bounds(getBareData());
        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t displacement = index - array1Bounds.min;
        int i = displacement / array1Bounds.stride;
        if (displacement % array1Bounds.stride != 0)
          pyonError("Array index out of bounds\n");

        PyonBoxPtr *array1_contents =
          (PyonBoxPtr *)pyon_Array1_get_contents(getBareData());
        return T_Box(array1_contents[i]);
      }

  };

/* ------------------------------- Array2 ----------------------------------- */

  template<typename T>
  class Array2 : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      struct initializer {
        int ymin;
        int yend;
        int xmin;
        int xend;
        initializer(int _ymin, int _yend, int _xmin, int _xend)
          : ymin(_ymin), yend(_yend), xmin(_xmin), xend(_xend) {}
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      Array2<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array2_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array2_alignment;
      }
      
      static void 
      copy(Array2<T> array2, Incomplete< Array2<T> > &incompleteArray2) { 
        if (!incompleteArray2.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array2Bounds bounds = pyon_Array2_get_bounds(array2.getBareData());
        if (bounds.ystride != 1 || bounds.xstride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray2.create(bounds.ymin, bounds.ymin + bounds.ysize,
                                bounds.xmin, bounds.xmin + bounds.xsize);

        /* Copy array contents */
        int j, i;
        for (j = 0; j < bounds.ysize; j++) {
          for (i = 0; i < bounds.xsize; i++) {
            int ix_j = bounds.ymin + j * bounds.ystride;
            int ix_i = bounds.xmin + i * bounds.xstride;
            incompleteArray2.at(j, i) = array2.at(j, i);
          }
        }
      }
      
      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Bare 
      at(int rowIndex, int columnIndex) {
        Array2Bounds array2Bounds = pyon_Array2_get_bounds(getBareData());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array2Bounds.xmin;
        int xi = x_displacement / array2Bounds.xstride;
        if (x_displacement % array2Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array2Bounds.ymin;
        int yi = y_displacement / array2Bounds.ystride;
        if (y_displacement % array2Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array2Bounds.xsize;
        int index = yi * row_n_members + xi;
        PyonBarePtr array2_contents = pyon_Array2_get_contents(getBareData());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return T_Bare(array2_contents + index * element_size);
      }

  };


/* ------------------------------- BArray2 ---------------------------------- */

  template<typename T>
  class BArray2 : public BareType {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      struct initializer {
        int ymin;
        int yend;
        int xmin;
        int xend;
        initializer(int _ymin, int _yend, int _xmin, int _xend)
          : ymin(_ymin), yend(_yend), xmin(_xmin), xend(_xend) {}
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      BArray2<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array2_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array2_alignment;
      }
      
      static void 
      copy(BArray2<T> array2, Incomplete< BArray2<T> > &incompleteArray2) { 
        if (!incompleteArray2.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array2Bounds bounds = pyon_Array2_get_bounds(array2.getBareData());
        if (bounds.ystride != 1 || bounds.xstride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray2.create(bounds.ymin, bounds.ymin + bounds.ysize,
                                bounds.xmin, bounds.xmin + bounds.xsize);

        /* Copy array contents.  It's an array of pointers. */
        PyonBarePtr dst_array =
          pyon_Array2_get_contents(incompleteArray2.getObject());
        PyonBarePtr src_array =
          pyon_Array2_get_contents(array2.getBareData());
        memcpy(dst_array, src_array,
               bounds.ysize * bounds.xsize * sizeof(PyonBoxPtr));
      }
      
      static bool 
      isPOD() { return false; }

      // Member Functions
      T_Box
      at(int rowIndex, int columnIndex) {
        Array2Bounds array2Bounds = pyon_Array2_get_bounds(getBareData());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array2Bounds.xmin;
        int xi = x_displacement / array2Bounds.xstride;
        if (x_displacement % array2Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array2Bounds.ymin;
        int yi = y_displacement / array2Bounds.ystride;
        if (y_displacement % array2Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array2Bounds.xsize;
        int index = yi * row_n_members + xi;
        PyonBoxPtr *array2_contents =
          (PyonBoxPtr *)pyon_Array2_get_contents(getBareData());
        return T_Box(array2_contents[index]);
      }
  };

/* ------------------------------- Array3 ----------------------------------- */

  template<typename T>
  class Array3 : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      struct initializer {
        int zmin;
        int zend;
        int ymin;
        int yend;
        int xmin;
        int xend;
        initializer(int _zmin, int _zend,
                    int _ymin, int _yend,
                    int _xmin, int _xend)
          : zmin(_zmin), zend(_zend), ymin(_ymin),
            yend(_yend), xmin(_xmin), xend(_xend) {}
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      Array3<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array3_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array3_alignment;
      }
      
      static void
      copy(Array3<T> array3, Incomplete< Array3<T> > &incompleteArray3) { 
        if (!incompleteArray3.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array3Bounds bounds = pyon_Array3_get_bounds(array3.getBareData());
        if (bounds.zstride != 1 || bounds.ystride != 1 || bounds.xstride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray3.create(bounds.zmin, bounds.zmin + bounds.zsize,
                                bounds.ymin, bounds.ymin + bounds.ysize,
                                bounds.xmin, bounds.xmin + bounds.xsize);

        /* Copy array contents */
        int k, j, i;
        for (k = 0; k < bounds.zsize; k++) {
          for (j = 0; j < bounds.ysize; j++) {
            for (i = 0; i < bounds.xsize; i++) {
              int ix_k = bounds.zmin + k * bounds.zstride;
              int ix_j = bounds.ymin + j * bounds.ystride;
              int ix_i = bounds.xmin + i * bounds.xstride;
              incompleteArray3.at(k, j, i) = array3.at(k, j, i);
            }
          }
        }
      }

      static bool
      isPOD() { return false; }

      // Member Functions
      T_Bare
      at(int zIndex, int rowIndex, int columnIndex) {
        Array3Bounds array3Bounds = pyon_Array3_get_bounds(getBareData());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array3Bounds.xmin;
        int xi = x_displacement / array3Bounds.xstride;
        if (x_displacement % array3Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array3Bounds.ymin;
        int yi = y_displacement / array3Bounds.ystride;
        if (y_displacement % array3Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t z_displacement = zIndex - array3Bounds.zmin;
        int zi = z_displacement / array3Bounds.zstride;
        if (z_displacement % array3Bounds.zstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array3Bounds.xsize;
        int32_t plane_n_members = row_n_members * array3Bounds.ysize;
        int index = zi * plane_n_members + yi * row_n_members + xi;
        PyonBarePtr array3_contents = pyon_Array3_get_contents(getBareData());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return T_Bare(array3_contents + index * element_size);
      }

  };

/* ------------------------------- BArray3 ---------------------------------- */

  template<typename T>
  class BArray3 : public BareType {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      struct initializer {
        int zmin;
        int zend;
        int ymin;
        int yend;
        int xmin;
        int xend;
        initializer(int _zmin, int _zend,
                    int _ymin, int _yend,
                    int _xmin, int _xend)
          : zmin(_zmin), zend(_zend), ymin(_ymin),
            yend(_yend), xmin(_xmin), xend(_xend) {}
      };
      // no definition of defaultInitializer
    public:
      // Constructors
      BArray3<T>(PyonBarePtr _bare_data) : BareType(_bare_data) { }
      
      // Static Member Functions
      static unsigned int 
      getSize() {
        return pyon_Array3_size;
      }
      
      static unsigned int 
      getAlignment() { 
        return pyon_Array3_alignment;
      }
      
      static void
      copy(BArray3<T> array3, Incomplete< BArray3<T> > &incompleteArray3) { 
        if (!incompleteArray3.isEmpty()) {
          pyonError("Attempted to write an already-initalized array\n");
        }

        /* Create the new array */
        Array3Bounds bounds = pyon_Array3_get_bounds(array3.getBareData());
        if (bounds.zstride != 1 || bounds.ystride != 1 || bounds.xstride != 1) {
          pyonError("Non-unit stride arrays are not implemented\n");
        }
        incompleteArray3.create(bounds.zmin, bounds.zmin + bounds.zsize,
                                bounds.ymin, bounds.ymin + bounds.ysize,
                                bounds.xmin, bounds.xmin + bounds.xsize);

        /* Copy array contents.  It's an array of pointers. */
        PyonBarePtr dst_array =
          pyon_Array3_get_contents(incompleteArray3.getObject());
        PyonBarePtr src_array =
          pyon_Array3_get_contents(array3.getBareData());
        memcpy(dst_array, src_array,
               bounds.zsize * bounds.ysize * bounds.xsize * sizeof(PyonBoxPtr));
      }

      static bool
      isPOD() { return false; }

      // Member Functions
      T_Box
      at(int zIndex, int rowIndex, int columnIndex) {
        Array3Bounds array3Bounds = pyon_Array3_get_bounds(getBareData());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array3Bounds.xmin;
        int xi = x_displacement / array3Bounds.xstride;
        if (x_displacement % array3Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array3Bounds.ymin;
        int yi = y_displacement / array3Bounds.ystride;
        if (y_displacement % array3Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t z_displacement = zIndex - array3Bounds.zmin;
        int zi = z_displacement / array3Bounds.zstride;
        if (z_displacement % array3Bounds.zstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array3Bounds.xsize;
        int32_t plane_n_members = row_n_members * array3Bounds.ysize;
        int index = zi * plane_n_members + yi * row_n_members + xi;
        PyonBoxPtr *array3_contents =
          (PyonBoxPtr *)pyon_Array3_get_contents(getBareData());
        return T_Box(array3_contents[index]);
      }

  };


/******************************************************************************/
/*          Stored Classes: BareType versions of ValType classes              */
/******************************************************************************/

    template<typename T>
  class Stored : public BareType {
    public:
      struct initializer {}; // Class is empty
      static initializer defaultInitializer(void) { return initializer(); }

      // Constructors
      Stored<T>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return sizeof(typename T::type);}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return __alignof__(typename T::type);}
      
      static inline void 
      copy(Stored<T> i, Incomplete<Stored<T> >& incompleteI);
      
      static bool 
      isPOD() __attribute__((const)) { return true; }

      // Member Functions
      operator T() const {
        return T(*(typename T::type*) getBareData());
      }

      operator typename T::type() const {
        return *(typename T::type *)getBareData();
      }

      inline operator Boxed<Stored<T> >() const;
  };

  /* Implementation of Stored<NoneType> */

    template<>
  class Stored<NoneType> : public BareType {
    public:
      struct initializer {}; // Class is empty
      static initializer defaultInitializer(void) { return initializer(); }

      // Constructors
      Stored<NoneType>(PyonBarePtr _bare_data) : BareType(_bare_data) {}

      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return 0;}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return 1;}
      
      static inline void
      copy(Stored<NoneType> n, Incomplete< Stored<NoneType> >& incompleteN);
      
      static bool 
      isPOD() __attribute__((const)) { return true; }
      
      //Member Functions
      operator NoneType() {
        return NoneType();
      }
  };


/******************************************************************************/
/*                      Incomplete BareType Objects                           */
/******************************************************************************/

  /* Implementation of Incomplete< StuckRef <T> > */
    template<typename T>
  class Incomplete<StuckRef<T> > : public IncompleteSingleRef<StuckRef<T> > {
    public:
      Incomplete < StuckRef<T> >(void)
        : IncompleteSingleRef< StuckRef<T> >() {}
      Incomplete < StuckRef<T> >(PyonBarePtr _s)
        : IncompleteSingleRef< StuckRef<T> >(_s) {}
      void initialize(const typename StuckRef<T>::initializer&) { }
      void create(const typename StuckRef<T>::initializer& init)
      { this->allocate(); initialize(init); }
      void initialize() { initialize(StuckRef<T>::defaultInitializer()); }
      void create() { create(StuckRef<T>::defaultInitializer()); }

      /* There is no operator=(StuckRef<T>).
       * Instead, StuckRef<T> is cast to T, which can be passed to the
       * following operator. */
      void operator=(T other) {
        /* Copy a pointer */
        PyonBoxPtr *data = (PyonBoxPtr *)this->getObject();
        *data = other.getBoxData();
      }
  };


  /* Implementation of Incomplete< Stored <T> > */
  
    template<typename T>
  class Incomplete < Stored<T> > : public IncompleteSingleRef< Stored<T> > {
    public:
      Incomplete < Stored<T> >(void) : IncompleteSingleRef< Stored<T> >() {}
      Incomplete < Stored<T> >(PyonBarePtr _s) : IncompleteSingleRef< Stored<T> >(_s) {}
      void initialize(const typename Stored<T>::initializer&) { }
      void create(const typename Stored<T>::initializer& init)
      { this->allocate(); initialize(init); }
      void initialize() { initialize(Stored<T>::defaultInitializer()); }
      void create() { create(Stored<T>::defaultInitializer()); }
      void operator=(const T& other) {
        typename T::type *data = (typename T::type *) this->getObject();
        *data = other.nativeElement; 
      }
  };

  /* Implementation of Incomplete< Stored <NoneType> > */
  
    template<>
  class Incomplete< Stored<NoneType> > : public IncompleteSingleRef< Stored<NoneType> > {
    public:
      Incomplete < Stored<NoneType> >(void) : IncompleteSingleRef< Stored<NoneType> >() {}
      Incomplete < Stored<NoneType> >(PyonBarePtr _s) : IncompleteSingleRef< Stored<NoneType> >(_s) {}
      void initialize(const Stored<NoneType>::initializer&) { }
      void create(const Stored<NoneType>::initializer& init)
      { this->allocate(); initialize(init); }
      void initialize() { initialize(Stored<NoneType>::defaultInitializer()); }
      void create() { create(Stored<NoneType>::defaultInitializer()); }
      void operator=(const NoneType& other) { }
  };
  
  /* Implementation of Incomplete< Tuple<T1,T2,T3,T4> > */

    template<typename T1, typename T2, typename T3, typename T4>
  class Incomplete< Tuple<T1,T2,T3,T4> > : public IncompleteSingleRef< Tuple<T1,T2,T3,T4> > {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
      typedef typename AsBareType<T3>::type T3_Bare;
      typedef typename AsBareType<T4>::type T4_Bare;
    public:
      // Constructors
      Incomplete< Tuple<T1,T2,T3,T4> >(void) : IncompleteSingleRef< Tuple<T1,T2,T3,T4> >() {}
      Incomplete< Tuple<T1,T2,T3,T4> >(PyonBarePtr _s) : IncompleteSingleRef< Tuple<T1,T2,T3,T4> >(_s) {}
      
      // Member Functions
      void initialize(const typename Tuple<T1,T2,T3,T4>::initializer& init)
      {
        get<0>().initialize(init.init_1);
        get<1>().initialize(init.init_2);
        get<2>().initialize(init.init_3);
        get<3>().initialize(init.init_4);
      }
      void create(const typename Tuple<T1,T2,T3,T4>::initializer& init)
      {
        this->allocate();
        initialize(init);
      }
      void initialize() {initialize(Tuple<T1,T2,T3,T4>::defaultInitializer());}
      void create() {create(Tuple<T1,T2,T3,T4>::defaultInitializer());}

        template<int index>
      Incomplete<typename get_return_type<index, T1, T2, T3, T4>::type> 
      get() { return get_return_type<index, T1, T2, T3, T4>::get_incomplete_return_object(this); }

  };

  /* Implementation of Incomplete< Tuple<T1,T2,T3> > */

    template<typename T1, typename T2, typename T3>
  class Incomplete< Tuple<T1,T2,T3> > : public IncompleteSingleRef< Tuple<T1,T2,T3> > {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
      typedef typename AsBareType<T3>::type T3_Bare;
    public:
      // Constructors
      Incomplete< Tuple<T1,T2,T3> >(void) : IncompleteSingleRef< Tuple<T1,T2,T3> >() {}
      Incomplete< Tuple<T1,T2,T3> >(PyonBarePtr _s) : IncompleteSingleRef< Tuple<T1,T2,T3> >(_s) {}
      
      // Member Functions
      void initialize(const typename Tuple<T1,T2,T3>::initializer& init)
      {
        get<0>().initialize(init.init_1);
        get<1>().initialize(init.init_2);
        get<2>().initialize(init.init_3);
      }
      void create(const typename Tuple<T1,T2,T3>::initializer& init)
      {
        this->allocate();
        initialize(init);
      }
      void initialize() {initialize(Tuple<T1,T2,T3>::defaultInitializer());}
      void create() {create(Tuple<T1,T2,T3>::defaultInitializer());}

        template<int index>
      Incomplete<typename get_return_type<index, T1, T2, T3>::type> 
      get() { return get_return_type<index, T1, T2, T3>::get_incomplete_return_object(this); }

  };

  /* Implementation of Incomplete< Tuple<T1,T2> > */

    template<typename T1, typename T2>
  class Incomplete< Tuple<T1,T2> > : public IncompleteSingleRef< Tuple<T1,T2> > {
    private:
      typedef typename AsBareType<T1>::type T1_Bare;
      typedef typename AsBareType<T2>::type T2_Bare;
    public:
      // Constructors
      Incomplete< Tuple<T1,T2> >(void) : IncompleteSingleRef< Tuple<T1,T2> >() {}
      Incomplete< Tuple<T1,T2> >(PyonBarePtr _s) : IncompleteSingleRef< Tuple<T1,T2> >(_s) {}
      
      // Member Functions
      void initialize(const typename Tuple<T1,T2>::initializer& init)
      {
        get<0>().initialize(init.init_1);
        get<1>().initialize(init.init_2);
      }
      void create(const typename Tuple<T1,T2>::initializer& init)
      {
        this->allocate();
        initialize(init);
      }
      void initialize() {initialize(Tuple<T1,T2>::defaultInitializer());}
      void create() {create(Tuple<T1,T2>::defaultInitializer());}

        template<int index>
      Incomplete<typename get_return_type<index, T1, T2>::type> 
      get() { return get_return_type<index, T1, T2>::get_incomplete_return_object(this); }

  };

  /* Implementation of Incomplete< List<T> > */

    template<typename T>
  class Incomplete< List<T> > : public IncompleteSingleRef< List<T> > {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      // Constructors
      Incomplete< List<T> >(void)
        : IncompleteSingleRef< List<T> >() {}
      Incomplete< List<T> >(PyonBarePtr _s)
        : IncompleteSingleRef< List<T> >(_s) {}

      // Member Functions
      void initialize(const typename List<T>::initializer& init) {
        pyon_List_initialize(init.length,
                             T_Bare::getSize(),
                             T_Bare::getAlignment(),
                             this->getObject());
      }
      void create(const typename List<T>::initializer& init)
      { this->allocate(); initialize(init); }
      void initialize(int length)
      { initialize(typename List<T>::initializer(length)); }
      void create(int length)
      { create(typename List<T>::initializer(length)); }

      Incomplete< T_Bare > 
      at(int index) { 
        PyonBarePtr list_contents = pyon_List_get_contents(this->getObject());
        return Incomplete<T_Bare>(list_contents + index*addPadding<T_Bare>(T_Bare::getSize()) ); 
      }

  };

  /* Implementation of Incomplete< BList<T> > */

    template<typename T>
  class Incomplete<BList<T> > : public IncompleteSingleRef<BList<T> > {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      // Constructors
      Incomplete<BList<T> >(void)
        : IncompleteSingleRef<BList<T> >() {}
      Incomplete<BList<T> >(PyonBarePtr _s)
        : IncompleteSingleRef<BList<T> >(_s) {}

      // Member Functions
      void initialize(const typename BList<T>::initializer& init) {
        pyon_List_initialize(init.length,
                             sizeof(PyonBoxPtr),
                             __alignof__(PyonBoxPtr),
                             this->getObject());
      }
      void create(const typename BList<T>::initializer& init)
      { this->allocate(); initialize(init); }
      void initialize(int length)
      { initialize(typename BList<T>::initializer(length)); }
      void create(int length)
      { create(typename BList<T>::initializer(length)); }

      Incomplete<StuckRef<T_Box> > 
      at(int index) {
        PyonBoxPtr *list_contents =
          (PyonBoxPtr *)pyon_List_get_contents(this->getObject());
        return Incomplete<StuckRef<T_Box> >((PyonBarePtr)&list_contents[index]);
      }

  };

  /* Implementation of Incomplete< Array1<T> > */

    template<typename T>
  class Incomplete< Array1<T> > : public IncompleteSingleRef< Array1<T> > {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      // Constructors
      Incomplete< Array1<T> >(void) : IncompleteSingleRef< Array1<T> >() { }
      Incomplete< Array1<T> >(PyonBarePtr _s) : IncompleteSingleRef< Array1<T> >(_s) { }
      
      // Member Functions
      void initialize(const typename Array1<T>::initializer &init)
      {
        pyon_Array1_initialize(init.min, 1, init.end,
                               T_Bare::getSize(),
                               T_Bare::getAlignment(),
                               this->getObject());
      }
      void create(const typename Array1<T>::initializer &init)
      { this->allocate(); initialize(init); }
      void initialize(int min, int end)
      { initialize(typename Array1<T>::initializer(min, end)); }
      void create(int min, int end)
      { create(typename Array1<T>::initializer(min, end)); }

      Incomplete< T_Bare > 
      at(int index) { 
        int32_t min = pyon_Array1_get_bounds(this->getObject()).min;
        PyonBarePtr array1_contents = pyon_Array1_get_contents(this->getObject());
        return Incomplete<T_Bare>(array1_contents + (index - min)*addPadding<T_Bare>(T_Bare::getSize()) ); 
      }

  };

    template<typename T>
  class Incomplete< BArray1<T> > : public IncompleteSingleRef< BArray1<T> > {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      // Constructors
      Incomplete< BArray1<T> >(void) : IncompleteSingleRef< BArray1<T> >() { }
      Incomplete< BArray1<T> >(PyonBarePtr _s) : IncompleteSingleRef< BArray1<T> >(_s) { }
      
      // Member Functions
      void initialize(const typename BArray1<T>::initializer &init)
      {
        pyon_Array1_initialize(init.min, 1, init.end,
                               sizeof(PyonBarePtr),
                               __alignof__(PyonBarePtr),
                               this->getObject());
      }
      void create(const typename BArray1<T>::initializer &init)
      { this->allocate(); initialize(init); }
      void initialize(int min, int end)
      { initialize(typename BArray1<T>::initializer(min, end)); }
      void create(int min, int end)
      { create(typename BArray1<T>::initializer(min, end)); }

      Incomplete<StuckRef<T_Box> > 
      at(int index) {
        int32_t min = pyon_Array1_get_bounds(this->getObject()).min;
        PyonBoxPtr *array1_contents = (PyonBoxPtr *)pyon_Array1_get_contents(this->getObject());
        
        return Incomplete<StuckRef<T_Box> >((PyonBarePtr)&array1_contents[index - min]);
      }

  };

  /* Implementation of Incomplete< Array2<T> > */

    template<typename T>
  class Incomplete< Array2<T> > : public IncompleteSingleRef< Array2<T> > {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      // Constructors
      Incomplete< Array2<T> >(void) : IncompleteSingleRef< Array2<T> >() { }
      Incomplete< Array2<T> >(PyonBarePtr _s) : IncompleteSingleRef< Array2<T> >(_s) { }
      
      // Member Functions
      void initialize(const typename Array2<T>::initializer &init)
      {
        pyon_Array2_initialize(init.ymin, 1, init.yend,
                               init.xmin, 1, init.xend,
                               T_Bare::getSize(),
                               T_Bare::getAlignment(),
                               this->getObject());
      }
      void create(const typename Array2<T>::initializer &init)
      { this->allocate(); initialize(init); }

      void initialize(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end)
      { initialize(typename Array2<T>::initializer(y_min, y_end, x_min, x_end)); }

      void create(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end)
      { create(typename Array2<T>::initializer(y_min, y_end, x_min, x_end)); }

      Incomplete< T_Bare > 
      at(int rowIndex, int columnIndex) { 
        Array2Bounds array2Bounds = pyon_Array2_get_bounds(this->getObject());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array2Bounds.xmin;
        int xi = x_displacement / array2Bounds.xstride;
        if (x_displacement % array2Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array2Bounds.ymin;
        int yi = y_displacement / array2Bounds.ystride;
        if (y_displacement % array2Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array2Bounds.xsize;
        int index = yi * row_n_members + xi;
        PyonBarePtr array2_contents = pyon_Array2_get_contents(this->getObject());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return Incomplete<T_Bare>(array2_contents + index * element_size ); 
      }

  };


    template<typename T>
  class Incomplete<BArray2<T> > : public IncompleteSingleRef<BArray2<T> > {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      // Constructors
      Incomplete<BArray2<T> >(void) : IncompleteSingleRef<BArray2<T> >() { }
      Incomplete<BArray2<T> >(PyonBarePtr _s) : IncompleteSingleRef<BArray2<T> >(_s) { }

      // Member Functions
      void initialize(const typename BArray2<T>::initializer &init)
      {
        pyon_Array2_initialize(init.ymin, 1, init.yend,
                               init.xmin, 1, init.xend,
                               sizeof(PyonBoxPtr),
                               __alignof__(PyonBoxPtr),
                               this->getObject());
      }
      void create(const typename BArray2<T>::initializer &init)
      { this->allocate(); initialize(init); }

      void initialize(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end)
      { initialize(typename BArray2<T>::initializer(y_min, y_end, x_min, x_end)); }

      void create(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end)
      { create(typename BArray2<T>::initializer(y_min, y_end, x_min, x_end)); }

      Incomplete<StuckRef<T_Box > >
      at(int rowIndex, int columnIndex) { 
        Array2Bounds array2Bounds = pyon_Array2_get_bounds(this->getObject());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array2Bounds.xmin;
        int xi = x_displacement / array2Bounds.xstride;
        if (x_displacement % array2Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array2Bounds.ymin;
        int yi = y_displacement / array2Bounds.ystride;
        if (y_displacement % array2Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array2Bounds.xsize;
        int index = yi * row_n_members + xi;
        PyonBoxPtr *array2_contents =
          (PyonBoxPtr *)pyon_Array2_get_contents(this->getObject());
        return Incomplete<StuckRef<T_Box> >((PyonBarePtr)&array2_contents[index]); 
      }
  };

  /* Implementation of Incomplete< Array3<T> > */

    template<typename T>
  class Incomplete< Array3<T> > : public IncompleteSingleRef< Array3<T> > {
    private:
      typedef typename AsBareType<T>::type T_Bare;
    public:
      // Constructors
      Incomplete< Array3<T> >(void) : IncompleteSingleRef< Array3<T> >() { }
      Incomplete< Array3<T> >(PyonBarePtr _s) : IncompleteSingleRef< Array3<T> >(_s) { }
      
      // Member Functions
      void initialize(const typename Array3<T>::initializer &init)
      {
        pyon_Array3_initialize(init.zmin, 1, init.zend,
                               init.ymin, 1, init.yend,
                               init.xmin, 1, init.xend,
                               T_Bare::getSize(),
                               T_Bare::getAlignment(),
                               this->getObject());
      }
      void create(const typename Array3<T>::initializer &init)
      { this->allocate(); initialize(init); }

      void initialize(int32_t z_min, int32_t z_end, int32_t y_min,
                      int32_t y_end, int32_t x_min, int32_t x_end)
      {
        initialize(typename Array3<T>::initializer(z_min, z_end, y_min,
                                                   y_end, x_min, x_end));
      }

      void create(int32_t z_min, int32_t z_end, int32_t y_min,
                  int32_t y_end, int32_t x_min, int32_t x_end)
      {
        create(typename Array3<T>::initializer(z_min, z_end, y_min,
                                               y_end, x_min, x_end));
      }

      Incomplete< T_Bare > 
      at(int zIndex, int rowIndex, int columnIndex) { 
        Array3Bounds array3Bounds = pyon_Array3_get_bounds(this->getObject());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array3Bounds.xmin;
        int xi = x_displacement / array3Bounds.xstride;
        if (x_displacement % array3Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array3Bounds.ymin;
        int yi = y_displacement / array3Bounds.ystride;
        if (y_displacement % array3Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t z_displacement = zIndex - array3Bounds.zmin;
        int zi = z_displacement / array3Bounds.zstride;
        if (z_displacement % array3Bounds.zstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array3Bounds.xsize;
        int32_t plane_n_members = row_n_members * array3Bounds.ysize;
        int index = zi * plane_n_members + yi * row_n_members + xi;
        PyonBarePtr contents = pyon_Array3_get_contents(this->getObject());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return Incomplete<T_Bare>(contents + index * element_size);
      }

  };


    template<typename T>
  class Incomplete<BArray3<T> > : public IncompleteSingleRef<BArray3<T> > {
    private:
      typedef typename AsBoxType<T>::type T_Box;
    public:
      // Constructors
      Incomplete<BArray3<T> >(void) : IncompleteSingleRef<BArray3<T> >() { }
      Incomplete<BArray3<T> >(PyonBarePtr _s) : IncompleteSingleRef<BArray3<T> >(_s) { }

      // Member Functions
      void initialize(const typename BArray3<T>::initializer &init)
      {
        pyon_Array3_initialize(init.zmin, 1, init.zend,
                               init.ymin, 1, init.yend,
                               init.xmin, 1, init.xend,
                               sizeof(PyonBoxPtr),
                               __alignof__(PyonBoxPtr),
                               this->getObject());
      }
      void create(const typename BArray3<T>::initializer &init)
      { this->allocate(); initialize(init); }

      void initialize(int32_t z_min, int32_t z_end, int32_t y_min,
                      int32_t y_end, int32_t x_min, int32_t x_end)
      {
        initialize(typename BArray3<T>::initializer(z_min, z_end, y_min,
                                                   y_end, x_min, x_end));
      }

      void create(int32_t z_min, int32_t z_end, int32_t y_min,
                  int32_t y_end, int32_t x_min, int32_t x_end)
      {
        create(typename BArray3<T>::initializer(z_min, z_end, y_min,
                                               y_end, x_min, x_end));
      }

      Incomplete<StuckRef<T_Box > >
      at(int zIndex, int rowIndex, int columnIndex) { 
        Array3Bounds array3Bounds = pyon_Array3_get_bounds(this->getObject());

        // The real index in each dimension is (i - lower_bound) / stride.
        // The remainder modulo the stride must be zero.
        int32_t x_displacement = columnIndex - array3Bounds.xmin;
        int xi = x_displacement / array3Bounds.xstride;
        if (x_displacement % array3Bounds.xstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t y_displacement = rowIndex - array3Bounds.ymin;
        int yi = y_displacement / array3Bounds.ystride;
        if (y_displacement % array3Bounds.ystride != 0)
          pyonError("Array index out of bounds\n");

        int32_t z_displacement = zIndex - array3Bounds.zmin;
        int zi = z_displacement / array3Bounds.zstride;
        if (z_displacement % array3Bounds.zstride != 0)
          pyonError("Array index out of bounds\n");

        int32_t row_n_members = array3Bounds.xsize;
        int32_t plane_n_members = row_n_members * array3Bounds.ysize;
        int index = zi * plane_n_members + yi * row_n_members + xi;
        PyonBoxPtr *contents =
          (PyonBoxPtr *)pyon_Array3_get_contents(this->getObject());
        return Incomplete<StuckRef<T_Box> >((PyonBarePtr)&contents[index]);
      }
  };

  /* Implementation of Incomplete< Boxed<T> > */
    template<typename T>
  class Incomplete<Boxed<T> > : public IncompleteBoxedRef<Boxed<T> > {
    private:
      typedef typename AsBareType<T>::type T_Bare;

    public:
      Incomplete<Boxed<T> >(void) : IncompleteBoxedRef<Boxed<T> >() {}

      void initialize(const typename Boxed<T>::initializer &init)
      {
        // Initialize the contents of this object
        this->get().initialize(init);
      }

      void create(const typename Boxed<T>::initializer &init)
      { this->allocate(); initialize(init); }

      Incomplete<T_Bare>
      get() {
        /* Get a reference to the contents of this boxed object.
         * Compute size of object header plus padding. */
        unsigned int contents_offset =
          addPadding<T_Bare>(PYON_OBJECT_HEADER_SIZE);
        PyonBarePtr contents_ptr =
          (PyonBarePtr)((char *)this->getObject() + contents_offset);
        return Incomplete<T_Bare>(contents_ptr);
      }
  };

/******************************************************************************/
/*      Class methods that depend on T and Incomplete<T> are defined here     */
/******************************************************************************/
    

  inline void
  Stored<NoneType>::copy(Stored<NoneType> n,
                         Incomplete<Stored<NoneType> >& incompleteN)
  { // Do nothing
  }

  template<typename T>
  inline void 
  Stored<T>::copy(Stored<T> i, Incomplete< Stored<T> >& incompleteI)
  {
    void (*concept_check)(T) = &ValType_concept;
    incompleteI = (T)i;
  }

  template<typename T>
  inline
  Stored<T>::operator Boxed<Stored<T> >() const
  {
    Incomplete<Boxed<Stored<T> > > i;
    i.create();
    i.get() = *this;
    return i.freeze();
  }

  inline
  NoneType::operator Boxed<Stored<NoneType> >() const
  {
    Incomplete<Boxed<Stored<NoneType> > > i;
    i.create(Stored<NoneType>::defaultInitializer());
    return i.freeze();
  }

  inline
  Int::Int(const Stored<Int> &s)
  {
    nativeElement = (int32_t)s;
  }

  inline
  Int::operator Boxed<Stored<Int> >() const
  {
    Incomplete<Boxed<Stored<Int> > > i;
    i.create(Stored<Int>::defaultInitializer());
    i.get() = *this;
    return i.freeze();
  }

  inline
  Bool::Bool(const Stored<Bool> &s)
  {
    nativeElement = (char)s;
  }

  inline
  Bool::operator Boxed<Stored<Bool> >() const
  {
    Incomplete<Boxed<Stored<Bool> > > i;
    i.create(Stored<Bool>::defaultInitializer());
    i.get() = *this;
    return i.freeze();
  }

  inline
  Float::Float(const Stored<Float> &s)
  {
    nativeElement = (float)s;
  }

  inline
  Float::operator Boxed<Stored<Float> >() const
  {
    Incomplete<Boxed<Stored<Float> > > i;
    i.create(Stored<Float>::defaultInitializer());
    i.get() = *this;
    return i.freeze();
  }

/******************************************************************************/
/*      Concept checking                                                      */
/******************************************************************************/

  template<class T>
  void ValType_concept(T x) {
    /* T::kind == ValKindTag */
    typename T::kind kind_tag2 = ValKindTag();

    /* T::type is a POD type */
    typename T::type initializer_value;

    /* Casting between T and T::type is possible */
    T cast_initializer_value(initializer_value);
    initializer_value = cast_initializer_value;

    /* Stored<T> and Incomplete<Stored<T> > are valid types */
    BareType_concept(*(Stored<T> *)NULL);

    /* It's possible to create, assign, and freeze an incomplete object */
    Incomplete<Stored<T> > incomplete_t;
    incomplete_t.create();
    incomplete_t = initializer_value;
    incomplete_t = cast_initializer_value;
    Stored<T> stored_t = incomplete_t.freeze();

    /* It's possible to assign a T from a Stored<T> */
    initializer_value = stored_t;
    cast_initializer_value = stored_t;
  }

  template<class T>
  void BareType_concept(T x) {
    /* T::kind == BareKindTag */
    typename T::kind kind_tag2 = BareKindTag();

    /* T::initializer exists and is POD */
    typename T::initializer init = *(typename T::initializer *)NULL;

    PyonBarePtr p = x.getBareData();

    /* Incomplete<T> methods */
    Incomplete<T> incomplete_t;
    incomplete_t.allocate();
    incomplete_t.initialize(init);
    incomplete_t.create(init);
    Incomplete<T> incomplete2(p);

    /* Methods getSize, getAlignment, isPOD, copy */
    unsigned int x1 = T::getSize();
    unsigned int x2 = T::getAlignment();
    bool b = T::isPOD();

    T::copy(x, incomplete_t);
  }

  template<class T>
  void BoxType_concept(T x) {
    /* T::kind == BoxKindTag */
    typename T::kind kind_tag2 = BoxKindTag();

    /* T::initializer exists and is POD */
    typename T::initializer init = *(typename T::initializer *)NULL;

    PyonBoxPtr p = x.getBoxData();

    /* Incomplete<T> methods */
    Incomplete<T> incomplete_t;
    incomplete_t.allocate();
    incomplete_t.initialize(init);
    incomplete_t.create(init);

    /* Methods getSize, getAlignment */
    unsigned int x1 = T::getSize();
    unsigned int x2 = T::getAlignment();
  }

  /* This function performs compile-time correctness checks.
   * It is not meant to be called. */
  static void
  Pyon_concept_checks(void) {
    void (*f_NoneType)(NoneType) = &ValType_concept;
    void (*f_Bool)(Bool)         = &ValType_concept;
    void (*f_Int)(Int)           = &ValType_concept;
    void (*f_Float)(Float)       = &ValType_concept;
    void (*f_Boxed)(Boxed<Int>) = &BoxType_concept;
    void (*f_StuckRef)(StuckRef<Boxed<Int> >) = &BareType_concept;
    void (*f_Tuple2)(Tuple<Int,Int>)          = &BareType_concept;
    void (*f_Tuple3)(Tuple<Int,Int,Int>)      = &BareType_concept;
    void (*f_Tuple4)(Tuple<Int,Int,Int,Int>)  = &BareType_concept;
    void (*f_List)(List<Int>)                 = &BareType_concept;
    void (*f_Array1)(Array1<Int>)             = &BareType_concept;
    void (*f_Array2)(Array2<Int>)             = &BareType_concept;
    void (*f_Array3)(Array3<Int>)             = &BareType_concept;
    void (*f_BList)(BList<Int>)               = &BareType_concept;
    void (*f_BArray1)(BArray1<Int>)           = &BareType_concept;
    void (*f_BArray2)(BArray2<Int>)           = &BareType_concept;
    void (*f_BArray3)(BArray3<Int>)           = &BareType_concept;
  }

} // end namespace

#endif

