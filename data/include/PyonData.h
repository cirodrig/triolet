/* C++ data marshaling interface for Pyon
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <pyon/Base.h>
#include <pyon/Layout.h>

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
      owner = pyon_alloc_boxed(bare_type::getSize(),
			       bare_type::getAlignment());

      // Get pointer to the bare object
      object = ((char *)owner) + addPadding<bare_type>(sizeof(void *));
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
