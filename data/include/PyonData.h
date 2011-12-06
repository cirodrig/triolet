
/* C++ data marshaling interface for Pyon
 */

#ifndef PYON_DATA_H
#define PYON_DATA_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <pyon.h>
#include <pyon/Base.h>
#include <pyon/Layout.h>

#include "inttypes.h"

namespace Pyon {

  /****************************************************************************/
  /* Wrappers for specific type constructors  */

  template<typename val_type> class Stored;
  template<typename bare_type> class Boxed;
  template<typename bare_type> class Incomplete;


  /* A box for holding bare objects */
  template<typename bare_type>
  class Boxed : public BoxType {
  public:
    PyonBarePtr getContents(void) { NOT_IMPLEMENTED; }
  };

  template<typename val_type>
  class Stored : public BareType {
#if BEGIN_SIGNATURE
    operator val_type(void);
#endif
  };

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

  /* The bare type corresponding to a boxed object is its unboxed form */
  template<typename bare_type>
  struct AsBareTypeWithTag<BoxKindTag, Boxed<bare_type> > {
    typedef bare_type type;
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

  /* Abstract template of incomplete objects.  Only specializations
   * should be used.
   *
   * Incomplete objects have three states.
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
   */
  template<typename bare_type>
  class Incomplete {
#if BEGIN_SIGNATURE
  public:
    // Exactly one of the following three predicates is true at any time.
    bool isEmpty(void) const;
    bool isOwner(void) const;
    bool isBorrowed(void) const;

    Incomplete(void);
    Incomplete(const Incomplete &other);

    void allocate(void);
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
  class Array1;
  
    template<typename T>
  class Array2;
  
  /* Stored Classes: BareType versions of ValType classes (specializations of 
   * class Stored, extend class BareType ) */

    template<>
  class Stored<NoneType>;

    template<>
  class Stored<Int>;

    template<>
  class Stored<Bool>;

    template<>
  class Stored<Float>;

  /* Incomplete BareType Objects (specializations of Incomplete, inherit from
   * IncompleteSingleRef) */

    template<typename T>
  class Incomplete < Stored<T> >;

    template<>
  class Incomplete< Stored<NoneType> >;
  
    template<typename T1, typename T2, typename T3, typename T4>
  class Incomplete< Tuple<T1,T2,T3,T4> >;

    template<typename T1, typename T2, typename T3>
  class Incomplete< Tuple<T1,T2,T3> >;

    template<typename T1, typename T2>
  class Incomplete< Tuple<T1,T2> >;

    template<typename T>
  class Incomplete< List<T> >;

    template<typename T>
  class Incomplete< Array1<T> >;

    template<typename T>
  class Incomplete< Array2<T> >;



/******************************************************************************/
/*              C++ Wrapper Classes that wrap value objects                   */
/******************************************************************************/

  /* Implementation of the NoneType wrapper */

  class NoneType : public ValType {
    public:
      typedef NoneType type;
  };

  /* Implementation of the Int wrapper */

  class Int : public ValType {
    public:
      typedef Int type;
      int32_t nativeElement;

      Int(int32_t i) { nativeElement = i; }
      operator int32_t() { return nativeElement; }
  };

  /* Implementation of the Bool wrapper */

  class Bool : public ValType {
    public:
      typedef Bool type;
      int nativeElement;

      Bool(char b) { nativeElement = b; }
      operator int() { return nativeElement; }
  };

  /* Implementation of the Float wrapper */

  class Float : public ValType {
    public:
      typedef Float type;
      float nativeElement;

      Float(float f) { nativeElement = f; }
      operator float() { return nativeElement; }
  };



/******************************************************************************/
/*               C++ Wrapper Classes that wrap bare objects                   */
/******************************************************************************/

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
          T1_Bare::copy(tuple.get<0>(), incompleteTuple.get<0>());
          T2_Bare::copy(tuple.get<1>(), incompleteTuple.get<1>());
          T3_Bare::copy(tuple.get<2>(), incompleteTuple.get<2>());
          T4_Bare::copy(tuple.get<3>(), incompleteTuple.get<3>());
      }
      
      static bool 
      isPOD() { return T1::isPOD() && T2::isPOD() && T3::isPOD() && T4::isPOD(); }

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
          T1_Bare::copy(tuple.get<0>(), incompleteTuple.get<0>());
          T2_Bare::copy(tuple.get<1>(), incompleteTuple.get<1>());
          T3_Bare::copy(tuple.get<2>(), incompleteTuple.get<2>());
      }
      
      static bool 
      isPOD() { return T1::isPOD() && T2::isPOD() && T3::isPOD(); }

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
          T1_Bare::copy(tuple.get<0>(), incompleteTuple.get<0>());
          T2_Bare::copy(tuple.get<1>(), incompleteTuple.get<1>());
      }
      
      static bool 
      isPOD() { return T1::isPOD() && T2::isPOD(); }

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
          incompleteList = Incomplete< List<T> >(list.getBareData());
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


/* ------------------------------- Array1 ----------------------------------- */

  template<typename T>
  class Array1 : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
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
          incompleteArray1 = Incomplete< Array1<T> >(array1.getBareData());
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

/* ------------------------------- Array2 ----------------------------------- */

  template<typename T>
  class Array2 : public BareType {
    private:
      typedef typename AsBareType<T>::type T_Bare;
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
          incompleteArray2 = Incomplete< Array2<T> >(array2.getBareData());
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




/******************************************************************************/
/*                      Incomplete BareType Objects                           */
/******************************************************************************/

  /* Implementation of Incomplete< Stored <T> > */
  
    template<typename T>
  class Incomplete < Stored<T> > : public IncompleteSingleRef< Stored<T> > {
    public:
      Incomplete < Stored<T> >(void) : IncompleteSingleRef< Stored<T> >() {}
      Incomplete < Stored<T> >(PyonBarePtr _s) : IncompleteSingleRef< Stored<T> >(_s) {}
      void initialize() { }
      void create() { this->allocate(); initialize(); }
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
      void initialize() { }
      void create() { this->allocate(); initialize(); }
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
      void initialize() { }
      void create() { this->allocate(); initialize(); }

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
      void initialize() { }
      void create() { this->allocate(); initialize(); }

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
      void initialize() { }
      void create() { this->allocate(); initialize(); }

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
      void initialize(int _length) {
        pyon_List_initialize(_length,
                             T_Bare::getSize(),
                             T_Bare::getAlignment(),
                             this->getObject());
      }
      void create(int _length) { this->allocate(); initialize(_length); }

      Incomplete< T_Bare > 
      at(int index) { 
        PyonBarePtr list_contents = pyon_List_get_contents(this->getObject());
        return Incomplete<T_Bare>(list_contents + index*addPadding<T_Bare>(T_Bare::getSize()) ); 
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
      void initialize(int min, int end) { 
        pyon_Array1_initialize(min, end, T_Bare::getSize(), T_Bare::getAlignment(), this->getObject() );
      }
      void create(int min, int end) { this->allocate(); initialize(min, end); }

      Incomplete< T_Bare > 
      at(int index) { 
        int32_t min = pyon_Array1_get_bounds(this->getObject()).min;
        PyonBarePtr array1_contents = pyon_Array1_get_contents(this->getObject());
        return Incomplete<T_Bare>(array1_contents + (index - min)*addPadding<T_Bare>(T_Bare::getSize()) ); 
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
      void initialize(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end) { 
        pyon_Array2_initialize(y_min, y_end, x_min, x_end, T_Bare::getSize(), T_Bare::getAlignment(), this->getObject() );
      }
      void create(int32_t y_min, int32_t y_end, int32_t x_min, int32_t x_end) { this->allocate(); initialize(y_min, y_end, x_min, x_end); }

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
        PyonBarePtr array2_contents = pyon_Array2_get_contents(this->getBareData());
        int element_size = addPadding<T_Bare>(T_Bare::getSize());
        return Incomplete<T_Bare>(array2_contents + index * element_size ); 
      }

  };




/******************************************************************************/
/*          Stored Classes: BareType versions of ValType classes              */
/******************************************************************************/

  /* Implementation of Stored<NoneType> */

    template<>
  class Stored<NoneType> : public BareType {
    public:
      // Constructors
      Stored<NoneType>(PyonBarePtr _bare_data) : BareType(_bare_data) {}

      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return 0;}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return 1;}
      
      static void 
      copy(Stored<NoneType> n, Incomplete< Stored<NoneType> >& incompleteN) { }
      
      static bool 
      isPOD() __attribute__((const)) { return true; }
      
      //Member Functions
      operator NoneType() {
        return NoneType();
      }
  };

  /* Implementation of Stored<Int> */

    template<>
  class Stored<Int> : public BareType {
    public:
      // Constructors
      Stored<Int>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return sizeof(int32_t);}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return sizeof(int32_t);}
      
      static void 
      copy(Stored<Int> i, Incomplete< Stored<Int> >& incompleteI) { incompleteI = Incomplete< Stored<Int> >(i.getBareData()); }
      
      static bool 
      isPOD() __attribute__((const)) { return true; }

      // Member Functions
      operator Int() {
        int32_t* nativePtr = (int32_t*) getBareData();
        return Int(*nativePtr);
      }
  };

  /* Implementation of Stored<Bool> */

    template<>
  class Stored<Bool> : public BareType {
    public:
      // Constructors
      Stored<Bool>(PyonBarePtr _bare_data) : BareType(_bare_data) {}
      
      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return sizeof(char);}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return sizeof(char);}
      
      static void 
      copy(Stored<Bool> b, Incomplete< Stored<Bool> >& incompleteB) { incompleteB = Incomplete< Stored<Bool> >(b.getBareData()); }
      
      static bool 
      isPOD() __attribute__((const)) { return true; }

      // Member Functions
      operator Bool() {
        char* nativePtr = (char*) getBareData();
        return Bool(*nativePtr);
      }

  };

  /* Implementation of Stored<Float> */
  template<>
  class Stored<Float> : public BareType {
    public:
      // Constructors
      Stored<Float>(PyonBarePtr _bare_data) : BareType(_bare_data) {}

      // Static Member Functions
      static unsigned int 
      getSize() __attribute__((const)) { return sizeof(float);}
      
      static unsigned int 
      getAlignment() __attribute__((const)) {return sizeof(float);}
      
      static void 
      copy(Stored<Float> f, Incomplete< Stored<Float> >& incompleteF) { incompleteF = Incomplete< Stored<Float> >(f.getBareData()); }
      
      static bool 
      isPOD() __attribute__((const)) { return true; }

      // Member Functions
      operator Float() {
        float* nativePtr = (float*) getBareData();
        return Float(*nativePtr);
      }

  };

} // end namespace

#endif

