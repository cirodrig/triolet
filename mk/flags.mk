
# Conventions for program flags and options
#
# Because there are a number of different compilation paths involved, flags
# and options go through an assembly process.  First, parameters
# are given for subsets of compilation paths.  These are meticulously and
# lovingly assembled into a full parameter string for each compilation path,
# which can be used in makefile rules.
#
# Program flags and options consist of three parts:
#	prefix_program_(RAW_)suffix
#
# The prefix indicates what files the variable applies to.
# Note that the underscore is present even for an empty prefix.
#	w	All compiled files
#	C	Any C file
#	CHS	Any C file that's part of haskell code
#	CPY	Any C file that's part of a python module
#	HS	Any haskell file
#	HSCPY	A .hsc file that uses the python runtime
#
# The program is the step of compilation where the flag is used.
#	C	Compilation
#	A	Creating a static archive
#	D	Creating a dynamic archive
#	X	Creating an executable
# 
# Variables containing 'RAW' are used to create other variables.  They
# shouldn't be used directly in makefile rules.
#
# The suffix follows conventional linker terminology when possible.

###############################################################################
# Platform-dependent file extensions

SOEXT=so

###############################################################################
# Paths and command-line options

# Header directories
w_C_RAW_INCLUDEDIRS=
C_C_RAW_INCLUDEDIRS=
CHS_C_RAW_INCLUDEDIRS=/usr/local/lib/ghc-6.10.4/include
CPY_C_RAW_INCLUDEDIRS=/usr/include/python2.4
HS_C_RAW_INCLUDEDIRS=/usr/local/lib/ghc-6.10.4/include

# Library directories
w_A_RAW_LIBDIRS=
C_A_RAW_LIBDIRS=
CHS_A_RAW_LIBDIRS=
CPY_A_RAW_LIBDIRS=
HS_A_RAW_LIBDIRS=

w_D_RAW_LIBDIRS=
C_D_RAW_LIBDIRS=
CHS_D_RAW_LIBDIRS=
CPY_D_RAW_LIBDIRS=
HS_D_RAW_LIBDIRS=

# Libraries
w_A_RAW_LIBS=
C_A_RAW_LIBS=
CHS_A_RAW_LIBS=
CPY_A_RAW_LIBS=
HS_A_RAW_LIBS=

w_D_RAW_LIBS=
C_D_RAW_LIBS=
CHS_D_RAW_LIBS=
CPY_D_RAW_LIBS=
HS_D_RAW_LIBS=

w_X_RAW_LIBS=
C_X_RAW_LIBS=
CHS_X_RAW_LIBS=
CPY_X_RAW_LIBS=python2.4
HS_X_RAW_LIBS=

# Command-line options
#  For Python, compile position-independent code
w_C_RAW_OPTS=
C_C_RAW_OPTS=
CHS_C_RAW_OPTS=
CPY_C_RAW_OPTS=-fPIC
HS_C_RAW_OPTS=

w_A_RAW_OPTS=
C_A_RAW_OPTS=
CHS_A_RAW_OPTS=
CPY_A_RAW_OPTS=
HS_A_RAW_OPTS=

w_D_RAW_OPTS=
C_D_RAW_OPTS=
CHS_D_RAW_OPTS=
CPY_D_RAW_OPTS=
HS_D_RAW_OPTS=

###############################################################################
# Option assembly

C_FLAG_SET=w C
CHS_FLAG_SET=w C CHS
CPY_FLAG_SET=w C CPY
HS_FLAG_SET=w HS
HSCPY_FLAG_SET=w C CPY HS

# ASSEMBLE_FLAGS
#  $(1):	flag set
#  $(2):	compilation stage
#  $(3):	suffix
#  $(4):	how to transform flags
ASSEMBLE_FLAGS=$(call $(4), $(foreach ftype, $(1), $($(ftype)_$(2)_RAW_$(3))))

# TRANSFORM_ID
# The identity transformation.
define TRANSFORM_ID
$(1)
endef

# TRANSFORM_INCLUDEDIR
# Use syntax for include paths.
define TRANSFORM_INCLUDEDIR
$(foreach param, $(1), -I$(param))
endef

# TRANSFORM_LIBDIR
# Use syntax for library paths.
define TRANSFORM_LIBDIR
$(foreach param, $(1), -L$(param))
endef

# TRANSFORM_LIB
# Use syntax for static/dynamic libraries.
define TRANSFORM_LIB
$(foreach param, $(1), -l$(param))
endef

# DEFINE_FLAG
# Define a flag, using ASSEMBLE_FLAGS to create the flag's value.
# Should be called with 'eval'.
#  $(1):	file type
#  $(2):	compilation stage
#  $(3):	suffix
#  $(4):	how to transform flags
define DEFINE_FLAG
$(1)_$(2)_$(3)=$(call ASSEMBLE_FLAGS,$($(1)_FLAG_SET),$(2),$(3),$(4))
endef

###############################################################################
# Options

$(foreach ftype, C CHS CPY HS HSCPY, \
 $(foreach stage, C A D X, \
  $(eval \
   $(call DEFINE_FLAG,$(ftype),$(stage),INCLUDEDIRS, TRANSFORM_INCLUDEDIR))))

$(foreach ftype, C CHS CPY HS HSCPY, \
 $(foreach stage, C A D X, \
  $(eval \
   $(call DEFINE_FLAG,$(ftype),$(stage),LIBDIRS, TRANSFORM_LIBDIR))))

$(foreach ftype, C CHS CPY HS HSCPY, \
 $(foreach stage, C A D X, \
  $(eval \
   $(call DEFINE_FLAG,$(ftype),$(stage),LIBS, TRANSFORM_LIB))))

$(foreach ftype, C CHS CPY HS HSCPY, \
 $(foreach stage, C A D X, \
  $(eval \
   $(call DEFINE_FLAG,$(ftype),$(stage),OPTS, TRANSFORM_ID))))
