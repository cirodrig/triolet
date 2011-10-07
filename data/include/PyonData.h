/* C++ data marshaling interface for Pyon
 */

#include <stdio.h>
#include <stdlib.h>

// This macro is used to demarcate signature specifications
#define BEGIN_SIGNATURE 0

#define NOT_IMPLEMENTED pyonError("Not implemented")

namespace Pyon {

  struct PyonBareObj {};	// Some bare object implemented in Pyon
  struct PyonBoxObj {};	       // Some boxed object implemented in Pyon
  typedef PyonBareObj *PyonBarePtr;
  typedef PyonBoxObj *PyonBoxPtr;

  static inline void
  pyonError(const char *s) {
    fputs(s, stderr);
    exit(-1);
  }

  /****************************************************************************/
  /* Pyon Kinds */

  // One of these tags is associated to each C++ type corresponding to
  // a Pyon data constructor.  The tag specifies the Pyon type's kind.
  struct BareKindTag {};
  struct BoxKindTag {};
  struct ValKindTag {};

  // All wrapper classes are subclasses of one of these.
  // These classes each use an associated type to specify their kind.
  class ValType;		// Base class of value types
  class BareType;		// Base class of bare types
  class BoxType;		// Base class of boxed types

  // Kind conversions
  template<typename kind, typename pyon_type> struct AsBareTypeWithTag;
  template<typename pyon_type> struct AsBareType;

  /* Abstract base class for value types.
   *
   * Stored<typeof(this)> <: BareType */
  class ValType {
  public:
    typedef ValKindTag kind;
  };

  /* An abstract base class for bare types.  Bare types encapsulate a
   * reference to a bare Pyon object.
   *
   * Derived classes should not define additional fields. Dervied classes
   * should define the methods specified in the signature. */
  class BareType {
  public:
    typedef BareKindTag kind;

  private:
    PyonBarePtr const bare_data; // The pyon object

  public:
    BareType(PyonBarePtr _bare_data) : bare_data(_bare_data) {}
    PyonBarePtr getBareData(void) const {return bare_data;}

#if BEGIN_SIGNATURE
    static int getSize(void);
    static int getAlignment(void);
    static void copy(T *, Incomplete<T> *);
    static bool isPOD(void);
#endif
  };

  /* An abstract base class for boxed types.  Boxed types encapsulate a
   * reference to a boxed Pyon object.
   *
   * Derived classes should not define additional fields. */
  class BoxType {
  public:
    typedef BoxKindTag kind;

  private:
    PyonBoxPtr const box_data;
  };

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
      // Create object and initialize header
      owner = pyon_allocate_object(bare_type::getSize());

      // Get pointer to field
      object = Boxed<bare_type>(owner).getContents();
    }

    bare_type freeze(void) {
      if (!isOwner()) {
 	pyonError("No incomplete object reference");
      }
      PyonBoxPtr ret = owner;
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

} // end namespace
