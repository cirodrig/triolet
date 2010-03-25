# This is a makefile, to be included by other makefiles.
# Variables are assigned here.

# Platform-specific settings generated by autoconf
include config.mk

## Convert parameters into command line option strings

PACKAGE_FLAGS=$(foreach pkg, $(PACKAGES), -package $(pkg))
LIB_FLAGS=$(foreach lib, $(LIBS), -l$(lib))
HS_INCLUDEDIR_FLAGS=-isrc/program -i$(BUILDDIR) $(foreach dir, $(INCLUDEDIRS), -I$(dir))
C_INCLUDEDIR_FLAGS=-Isrc/program -I$(BUILDDIR) $(foreach dir, $(INCLUDEDIRS), -I$(dir))
LIBDIR_FLAGS=$(foreach dir, $(LIBDIRS), -L$(dir))

HS_HSC2HS_OPTS=$(HSC2HSFLAGS) $(C_INCLUDEDIR_FLAGS)
HS_C_OPTS=$(HCFLAGS) -outputdir $(BUILDDIR) \
	-XMultiParamTypeClasses $(HS_INCLUDEDIR_FLAGS) $(PACKAGE_FLAGS)
C_C_OPTS=$(CCFLAGS) $(C_INCLUDEDIR_FLAGS)
L_OPTS=$(LFLAGS) $(PACKAGE_FLAGS) $(LIDIR_FLAGS) $(LIB_FLAGS)

## File lists

PYON_C_SRCS=Main_c.c \
	PythonInterface/Python_c.c \
	PythonInterface/HsObject_c.c \
	Pyon/Exports/Gluon_c.c \
	Pyon/Exports/SystemF_c.c
PYON_C_GENERATED_SRCS=Parser/Driver_stub.c \
	Pyon/Exports/Gluon_stub.c \
	Pyon/Exports/SystemF_stub.c \
	PythonInterface/HsObject_stub.c
PYON_HS_SRCS=Main.hs \
	Parser/Driver.hs \
	Parser/Parser.hs \
	Parser/Output.hs \
	Parser/ParserSyntax.hs \
	Pyon/Exports/Delayed.hs \
	Pyon/Exports/Gluon.hs \
	Pyon/Exports/SystemF.hs \
	Pyon/Globals.hs \
	Pyon/SystemF/Builtins.hs \
	Pyon/SystemF/Optimizations.hs \
	Pyon/SystemF/Print.hs \
	Pyon/SystemF/Syntax.hs \
	Pyon/SystemF/Typecheck.hs \
	Pyon/SystemF/Flatten.hs \
	Pyon/NewCore/Optimizations.hs \
	Pyon/NewCore/Print.hs \
	Pyon/NewCore/Rename.hs \
	Pyon/NewCore/Syntax.hs \
	Pyon/NewCore/Typecheck.hs

PYON_HS_GENERATED_SRCS=Paths_pyon.hs \
	PythonInterface/Python.hs \
	PythonInterface/HsObject.hs

PYON_HS_OBJECTS=$(patsubst %.hs, %.o, $(PYON_HS_SRCS) $(PYON_HS_GENERATED_SRCS))
PYON_C_OBJECTS=$(patsubst %.c, %.o, $(PYON_C_SRCS) $(PYON_C_GENERATED_SRCS))
PYON_OBJECTS=$(PYON_HS_OBJECTS) $(PYON_C_OBJECTS)

PYON_SCRIPTS=pyon_testsuite pyon_compile
PYON_GENERATED_SCRIPTS=$(foreach sc, $(PYON_SCRIPTS), build/scripts/$(sc))

PYON_TARGET=build/pyon

# Generated HS files with full path
PYON_HS_GENERATED_FILES=$(foreach src, $(PYON_HS_GENERATED_SRCS), $(BUILDDIR)/$(src))

# Object files with full path
PYON_OBJECT_FILES=$(foreach obj, $(PYON_OBJECTS), $(BUILDDIR)/$(obj))

# All source files with full path
PYON_HS_SOURCE_FILES=$(foreach src, $(PYON_HS_SRCS), $(SRCDIR)/$(src)) \
	$(foreach src, $(PYON_HS_GENERATED_SRCS), $(BUILDDIR)/$(src))
