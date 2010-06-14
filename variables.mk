# This is a makefile, to be included by other makefiles.
# Variables are assigned here.

# Platform-specific settings generated by autoconf
include config.mk

## Convert parameters into command line option strings

PACKAGE_FLAGS=$(foreach pkg, $(PACKAGES), -package $(pkg))
TH_PACKAGE_FLAGS=$(foreach pkg, $(TH_PACKAGES), -package $(pkg))
LIB_FLAGS=$(foreach lib, $(LIBS), -l$(lib))
HS_INCLUDEDIR_FLAGS=-isrc/program -i$(BUILDDIR) $(foreach dir, $(INCLUDEDIRS), -I$(dir))
C_INCLUDEDIR_FLAGS=-Isrc/program -I$(BUILDDIR) $(foreach dir, $(INCLUDEDIRS), -I$(dir))
LIBDIR_FLAGS=$(foreach dir, $(LIBDIRS), -L$(dir))

HS_HSC2HS_OPTS=$(HSC2HSFLAGS) $(C_INCLUDEDIR_FLAGS)
HS_C_OPTS=$(HCFLAGS) -outputdir $(BUILDDIR) \
	-XMultiParamTypeClasses $(HS_INCLUDEDIR_FLAGS) $(PACKAGE_FLAGS)
HS_TH_C_OPTS=$(HCFLAGS) -outputdir $(BUILDDIR) \
	-XMultiParamTypeClasses $(HS_INCLUDEDIR_FLAGS) $(TH_PACKAGE_FLAGS)
C_C_OPTS=$(CCFLAGS) $(C_INCLUDEDIR_FLAGS)
L_OPTS=$(LFLAGS) $(PACKAGE_FLAGS) $(LIDIR_FLAGS) $(LIB_FLAGS)

## File lists

PYON_C_SRCS=Main_c.c \
	PythonInterface/Python_c.c \
	PythonInterface/HsObject_c.c \
	Pyon/Exports/Gluon_c.c \
	Pyon/Exports/Untyped_c.c
PYON_C_GENERATED_SRCS=Parser/Driver_stub.c \
	Pyon/Exports/Gluon_stub.c \
	Pyon/Exports/Untyped_stub.c \
	PythonInterface/HsObject_stub.c
PYON_HS_SRCS=Main.hs \
	Parser/Driver.hs \
	Parser/Parser.hs \
	Parser/Output.hs \
	Parser/ParserSyntax.hs \
	Pyon/Exports/Delayed.hs \
	Pyon/Exports/Gluon.hs \
	Pyon/Globals.hs \
	Pyon/Untyped/Classes.hs \
	Pyon/Untyped/Data.hs \
	Pyon/Untyped/GenSystemF.hs \
	Pyon/Untyped/HMType.hs \
	Pyon/Untyped/Kind.hs \
	Pyon/Untyped/CallConv.hs \
	Pyon/Untyped/Print.hs \
	Pyon/Untyped/Syntax.hs \
	Pyon/Untyped/TypeAssignment.hs \
	Pyon/Untyped/TypeInference.hs \
	Pyon/Untyped/TypeInferenceEval.hs \
	Pyon/Untyped/Unification.hs \
	Pyon/SystemF/DeadCode.hs \
	Pyon/SystemF/ElimPatternMatching.hs \
	Pyon/SystemF/PartialEval.hs \
	Pyon/SystemF/Print.hs \
	Pyon/SystemF/StreamSpecialize.hs \
	Pyon/SystemF/Syntax.hs \
	Pyon/SystemF/Typecheck.hs \
	Pyon/SystemF/NewFlatten/PassConv.hs \
	Pyon/SystemF/NewFlatten/SetupEffect.hs \
	Pyon/Anf/Syntax.hs \
	Pyon/Anf/Print.hs \
	Pyon/Anf/Rename.hs \
	Pyon/Anf/Typecheck.hs \
	Pyon/NewCore/Optimizations.hs \
	Pyon/NewCore/Print.hs \
	Pyon/NewCore/Rename.hs \
	Pyon/NewCore/Syntax.hs
PYON_TH_HS_SRCS=Pyon/SystemF/Builtins.hs \
	Pyon/SystemF/BuiltinsTH.hs \
	Pyon/Exports/Untyped.hs \
	Pyon/Untyped/Builtins.hs \
	Pyon/Untyped/BuiltinsTH.hs \
	Pyon/Untyped/InitializeBuiltins.hs \
	Pyon/Anf/BuiltinsTH.hs \
	Pyon/Anf/Builtins.hs
PYON_HS_BOOT_SRCS=Pyon/Untyped/Syntax.hs-boot

PYON_HS_GENERATED_SRCS=Paths_pyon.hs \
	PythonInterface/Python.hs \
	PythonInterface/HsObject.hs

PYON_HS_OBJECTS=$(patsubst %.hs, %.o, $(PYON_HS_SRCS) $(PYON_TH_HS_SRCS) $(PYON_HS_GENERATED_SRCS))
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
PYON_HS_SOURCE_FILES=$(foreach src, $(PYON_HS_BOOT_SRCS), $(SRCDIR)/$(src)) \
	$(foreach src, $(PYON_HS_SRCS), $(SRCDIR)/$(src)) \
	$(foreach src, $(PYON_TH_HS_SRCS), $(SRCDIR)/$(src)) \
	$(foreach src, $(PYON_HS_GENERATED_SRCS), $(BUILDDIR)/$(src))
