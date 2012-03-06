/* This is an internal C++ header file.  Do not include this directly. */

/* Basic data types and functions. */

#ifndef _PYON_BASE_H
#define _PYON_BASE_H

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

  /* Abstract base class for value types.
   *
   * Stored<typeof(this)> <: BareType */
  class ValType {
  public:
    typedef ValKindTag kind;

#if BEGIN_SIGNATURE
    typedef _ type;
#endif
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
    struct initializer {
      // The initializer should be a POD type.  It is passed by value
      // to Incomplete<typeof(this)>::create.
    };

    // This function may be undefined if there is no reasonable default
    // initializer value
    static initializer defaultInitializer(void);

    static unsigned int getSize(void);
    static unsigned int getAlignment(void);
    static void copy(T, Incomplete<T>&);
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

  public:
    BoxType(PyonBoxPtr _box_data) : box_data(_box_data) {}
    PyonBoxPtr getBoxData(void) const {return box_data;}

#if BEGIN_SIGNATURE
    struct initializer {
      // The initializer should be a POD type.  It is passed by value
      // to Incomplete<typeof(this)>::create.
    };

    // This function may be undefined if there is no reasonable default
    // initializer value
    static initializer defaultInitializer(void);
#endif
  };

}

#endif
