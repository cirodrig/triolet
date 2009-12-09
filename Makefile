
# Platform-specific settings
include config.linux.mk

## Convert parameters into command line option strings
PACKAGE_FLAGS=$(foreach pkg, $(PACKAGES), -package $(pkg))
LIB_FLAGS=$(foreach lib, $(LIBS), -l$(lib))
INCLUDEDIR_FLAGS=$(foreach dir, $(INCLUDEDIRS), -I$(dir))
LIBDIR_FLAGS=$(foreach dir, $(LIBDIRS), -L$(dir))

HS_HSC2HS_OPTS=$(HSC2HSFLAGS) $(INCLUDEDIR_FLAGS)
HS_C_OPTS=$(HCFLAGS) $(INCLUDEDIR_FLAGS) $(PACKAGE_FLAGS)
C_C_OPTS=$(CCFLAGS) $(INCLUDEDIR_FLAGS)
L_OPTS=$(LFLAGS) $(PACKAGE_FLAGS) $(LIDIR_FLAGS) $(LIB_FLAGS)

## File lists

PYON_C_SRCS=Main_c.c
PYON_C_GENERATED_SRCS=Parser/Driver_stub.c
PYON_HS_SRCS=Main.hs \
	Parser/Driver.hs \
	Parser/Parser.hs \
	Parser/Output.hs \
	Parser/ParserSyntax.hs
PYON_HS_GENERATED_SRCS=Python.hs

PYON_HS_OBJECTS=$(patsubst %.hs, %.o, $(PYON_HS_SRCS) $(PYON_HS_GENERATED_SRCS))
PYON_C_OBJECTS=$(patsubst %.c, %.o, $(PYON_C_SRCS) $(PYON_C_GENERATED_SRCS))
PYON_OBJECTS=$(PYON_HS_OBJECTS) $(PYON_C_OBJECTS)

# Object files with full path
PYON_OBJECT_FILES=$(foreach obj, $(PYON_OBJECTS), $(BUILDDIR)/$(obj))

###############################################################################
# Targets

.PHONY : all build_python clean veryclean

all : build_python bin/pyon

clean :
	if [ -d build ]; then rm -rf build; fi

veryclean : clean
	find src -name "*~" -exec rm {} ';'
	if [ -d bin ]; then rm -f bin/*; rmdir bin; fi

bin :
	mkdir bin

build :
	mkdir build

build_python :
	python setup.py build

###############################################################################
# Program 'pyon'

# Dependences
$(BUILDDIR)/Main_c.o : $(BUILDDIR)/Parser/Driver_stub.h
$(BUILDDIR)/Main.o : $(BUILDDIR)/Parser/Driver_stub.h
$(BUILDDIR)/Main.o : $(BUILDDIR)/Python.hi
$(BUILDDIR)/Parser/Driver_stub.c \
 $(BUILDDIR)/Parser/Driver_stub.h \
 $(BUILDDIR)/Parser/Driver.o : $(BUILDDIR)/Python.hi
$(BUILDDIR)/Parser/Driver_stub.c \
 $(BUILDDIR)/Parser/Driver_stub.h \
 $(BUILDDIR)/Parser/Driver.o : $(BUILDDIR)/Parser/Parser.hi
$(BUILDDIR)/Parser/Driver_stub.c \
 $(BUILDDIR)/Parser/Driver_stub.h \
 $(BUILDDIR)/Parser/Driver.o : $(BUILDDIR)/Parser/Output.hi
$(BUILDDIR)/Parser/Output.o : $(BUILDDIR)/Python.hi
$(BUILDDIR)/Parser/Output.o : $(BUILDDIR)/Parser/ParserSyntax.hi
$(BUILDDIR)/Parser/Parser.o : $(BUILDDIR)/Parser/ParserSyntax.hi

# After invoking the compiler,
# touch interface files to ensure that their timestamps are updated
define PYON_COMPILE_HS_SOURCE
$(BUILDDIR)/$(patsubst %.hs,%.o,$(1)) : $(BUILDDIR)/$(1)
	$(HC) -c $$< -o $$@ -i$(BUILDDIR) $(HS_C_OPTS)
	touch $(BUILDDIR)/$(patsubst %.hs,%.hi,$(1))

endef

$(BUILDDIR)/Python.hs : $(SRCDIR)/Python.hsc
	$(HSC2HS) $(HS_HSC2HS_OPTS) $< -o $@

$(eval $(call PYON_COMPILE_HS_SOURCE,Main.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE,Python.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE,Parser/Parser.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE,Parser/Output.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE,Parser/ParserSyntax.hs))

# 'Driver.hs' has multiple targets, so it needs a distinct rule
$(BUILDDIR)/Parser/Driver_stub.c \
 $(BUILDDIR)/Parser/Driver_stub.h \
 $(BUILDDIR)/Parser/Driver.o : $(BUILDDIR)/Parser/Driver.hs
	$(HC) -c $< -o $(BUILDDIR)/Parser/Driver.o -i$(BUILDDIR) \
	 $(HS_C_OPTS)
	touch $(BUILDDIR)/Parser/Driver.hi

$(BUILDDIR)/Main_c.o : $(SRCDIR)/Main_c.c
	$(CC) -c $< -o $@ $(C_C_OPTS)

$(BUILDDIR)/Parser/Driver_stub.o : $(BUILDDIR)/Parser/Driver_stub.c
	$(CC) -c $< -o $@ $(C_C_OPTS)

bin/pyon : bin $(PYON_OBJECT_FILES)
	$(HC) $(PYON_OBJECT_FILES) -o $@ $(L_OPTS)

###############################################################################
# Generic rules

$(BUILDDIR)/%.hs : $(SRCDIR)/%.hs
	mkdir -p $(dir $@)
	cp $< $@

%.hi : %.o ;
