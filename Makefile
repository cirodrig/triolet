
# Platform-specific settings
include config.mk

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

PYON_SCRIPTS=pyon_testsuite
PYON_GENERATED_SCRIPTS=$(foreach sc, $(PYON_SCRIPTS), build/scripts/$(sc))

PYON_TARGET=build/program/pyon

# Object files with full path
PYON_OBJECT_FILES=$(foreach obj, $(PYON_OBJECTS), $(BUILDDIR)/$(obj))

###############################################################################
# Targets

.PHONY : all install clean veryclean build_bin build_python build_scripts install_bin install_python install_scripts

all : build_bin build_python build_scripts

install : install_bin install_python install_scripts $(PYON_TARGET)

clean :
	rm src/pyon/data_dir.py		# Autogenerated
	if [ -d build ]; then rm -rf build; fi

veryclean : clean
	find src -name "*~" -exec rm {} ';'
	rm -f config.log
	rm -f config.status
	rm -f config.mk
	rm -f configure
	rm -rf autom4te.cache
	if [ -d bin ]; then rm -f bin/*; rmdir bin; fi

bin :
	mkdir bin

build :
	mkdir build

build_bin : $(PYON_TARGET)

build_python : src/pyon/data_dir.py
	python setup.py build

build_scripts : $(PYON_GENERATED_SCRIPTS)

install_bin : build_bin
	install -d $(bindir)
	install $(PYON_TARGET) $(bindir)/pyon

install_python : build_python
	python setup.py install --prefix=$(prefix) --exec-prefix=$(exec_prefix)

install_scripts : build_scripts
	install -d $(bindir)
	cd build/scripts; for sc in *; do install $${sc} $(bindir)/$${sc}; done

src/pyon/data_dir.py :
	echo "DATA_DIR=\"$(prefix)/share/pyon\" # Autogenerated" > src/pyon/data_dir.py

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
# Touch output files to ensure their timestamps are updated
$(BUILDDIR)/Parser/Driver_stub.c \
 $(BUILDDIR)/Parser/Driver_stub.h \
 $(BUILDDIR)/Parser/Driver.o : $(BUILDDIR)/Parser/Driver.hs
	$(HC) -c $< -o $(BUILDDIR)/Parser/Driver.o -i$(BUILDDIR) \
	 $(HS_C_OPTS)
	touch $(BUILDDIR)/Parser/Driver.hi
	touch $(BUILDDIR)/Parser/Driver_stub.c
	touch $(BUILDDIR)/Parser/Driver_stub.h

$(BUILDDIR)/Main_c.o : $(SRCDIR)/Main_c.c
	$(CC) -c $< -o $@ $(C_C_OPTS)

$(BUILDDIR)/Parser/Driver_stub.o : $(BUILDDIR)/Parser/Driver_stub.c
	$(CC) -c $< -o $@ $(C_C_OPTS)

$(PYON_TARGET) : bin $(PYON_OBJECT_FILES)
	$(HC) $(PYON_OBJECT_FILES) -o $@ $(L_OPTS)

###############################################################################
# Generic rules

# To build a script, insert a line telling the shell how to execute the script
build/scripts/% : src/scripts/%
	mkdir -p build/scripts
	echo "#! $(bindir)/pyon" > $@
	cat $< >> $@

$(BUILDDIR)/%.hs : $(SRCDIR)/%.hs
	mkdir -p $(dir $@)
	cp $< $@

%.hi : %.o ;
