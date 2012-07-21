/* This is an internal C++ header file.  Do not include this directly. */

/* Basic data types and functions. */

#ifndef _PYON_BASE_H
#define _PYON_BASE_H

// This macro is used to demarcate signature specifications
#define BEGIN_SIGNATURE 0

#define NOT_IMPLEMENTED pyonError("Not implemented")

namespace Triolet {

  struct TriBareObj {};	// Some bare object implemented in Triolet
  struct TriBoxObj {};	       // Some boxed object implemented in Triolet
  typedef TriBareObj *TriBarePtr;
  typedef TriBoxObj *TriBoxPtr;

  static inline void
  trioletError(const char *s) {
    fputs(s, stderr);
    exit(-1);
  }

  /****************************************************************************/
  /* Triolet Kinds */

  // One of these tags is associated to each C++ type corresponding to
  // a Triolet data constructor.  The tag specifies the Triolet type's kind.
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
   * reference to a bare Triolet object.
   *
   * Derived classes should not define additional fields. Dervied classes
   * should define the methods specified in the signature. */
  class BareType {
  public:
    typedef BareKindTag kind;

  private:
    TriBarePtr bare_data; // The triolet object

  public:
  BareType() : bare_data(NULL) {}
    BareType(TriBarePtr _bare_data) : bare_data(_bare_data) {}
    TriBarePtr getBareData(void) const {return bare_data;}

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
   * reference to a boxed Triolet object.
   *
   * Derived classes should not define additional fields. */
  class BoxType {
  public:
    typedef BoxKindTag kind;

  private:
    TriBoxPtr box_data;

  public:
  BoxType() : box_data(NULL) {}
    BoxType(TriBoxPtr _box_data) : box_data(_box_data) {}
    TriBoxPtr getBoxData(void) const {return box_data;}

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
