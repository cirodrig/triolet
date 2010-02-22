# The main makefile.
#
# This makefile contains commands that run after dependency generation.
# Commands that run before dependency generation are in 'Makefile'.

include variables.mk

# GHC options passed to haddock.
HADDOCK_HC_OPTS=$(foreach opt, $(HS_C_OPTS), "--optghc=$(opt)")

# For each package, get the location of its haddock interface file
# using ghc-pkg
HADDOCK_INTERFACE_FILES=$(foreach pkg, $(PACKAGES), $(shell ghc-pkg describe $(pkg) --simple-output | $(ESED) -n "s/^haddock-interfaces: (.*)/\1/p"))
HADDOCK_INTERFACE_OPTS=$(foreach ifile, $(HADDOCK_INTERFACE_FILES), -i $(ifile))

###############################################################################
# Targets

.PHONY : default doc build install

default :
	@echo "No target specified"

doc : dist/doc/html/pyon/index.html

# Delegate documentation to a script
dist/doc/html/pyon/index.html : $(PYON_HS_SOURCE_FILES)
	@echo "Building documentation..."
	@env ESED="$(ESED)" HADDOCK_HC_OPTS="$(HADDOCK_HC_OPTS)" PYON_HS_SOURCE_FILES="$(PYON_HS_SOURCE_FILES)" PACKAGES="$(PACKAGES)" sh makedoc.sh

# Create executable and scripts; then run Python's setup script 
build : $(PYON_TARGET) $(PYON_GENERATED_SCRIPTS) src/pyon/data_dir.py
	python setup.py build

# Install Python library and files, pyon executable, and scripts
install : build
	python setup.py install --prefix=$(prefix) --exec-prefix=$(exec_prefix)
	install -d $(bindir)
	install $(PYON_TARGET) $(bindir)/pyon
	cd build/scripts; for sc in *; do install $${sc} $(bindir)/$${sc}; done

# Generate a Python file containing install path information
src/pyon/data_dir.py :
	echo "DATA_DIR=\"$(prefix)/share/pyon\" # Autogenerated" > src/pyon/data_dir.py

###############################################################################
# Compilation

# Compile a Haskell source file, found either in the source directory or in the
# build directory.
define COMPILE_HS_SOURCE
ifeq ($(shell test -f $(SRCDIR)/$(1) && echo yes),yes)
$(BUILDDIR)/$(1:.hs=.o) : $(SRCDIR)/$(1)
else
ifeq ($(shell test -f $(BUILDDIR)/$(1) && echo yes),yes)
$(BUILDDIR)/$(1:.hs=.o) : $(BUILDDIR)/$(1)
else
$(BUILDDIR)/$(1:.hs=.o) :
	echo "Cannot find file $(1)"
	exit 1
endif
endif
	mkdir -p $(BUILDDIR)/$(dir $(1))
	$(HC) -c $$< $(HS_C_OPTS)
	touch $(BUILDDIR)/$(patsubst %.hs,%.hi,$(1))

endef

# Compile a C source file, found either in the source directory or in the
# build directory.
define COMPILE_C_SOURCE
ifeq ($(shell test -f $(SRCDIR)/$(1) && echo yes),yes)
$(BUILDDIR)/$(1:.c=.o) : $(SRCDIR)/$(1)
else
ifeq ($(shell test -f $(BUILDDIR)/$(1) && echo yes),yes)
$(BUILDDIR)/$(1:.c=.o) : $(BUILDDIR)/$(1)
else
$(BUILDDIR)/$(1:.c=.o) :
	echo "Cannot find file $(1)"
	exit 1
endif
endif
	mkdir -p $(BUILDDIR)/$(dir $(1))
	$(CC) -c $$< -o $$@ $(C_C_OPTS)

endef

# Compile a C stub file generated by GHC.
define COMPILE_C_STUB
$(BUILDDIR)/$(1:.c=.o) : $(BUILDDIR)/$(1)
	$(CC) -c $$< -o $$@ $(C_C_OPTS)

endef

# Compile all Haskell files
$(foreach hssrc, $(PYON_HS_SRCS) $(PYON_HS_GENERATED_SRCS),$(eval $(call COMPILE_HS_SOURCE,$(hssrc))))

# Compile all C files
$(foreach csrc, $(PYON_C_SRCS),$(eval $(call COMPILE_C_SOURCE,$(csrc))))
$(foreach csrc, $(PYON_C_GENERATED_SRCS),$(eval $(call COMPILE_C_STUB,$(csrc))))

# Link all object files
$(PYON_TARGET) : bin $(PYON_OBJECT_FILES)
	$(HC) $(PYON_OBJECT_FILES) -o $@ $(L_OPTS)

###############################################################################
# Generic rules

# To build a script, insert a line telling the shell how to execute the script
build/scripts/% : src/scripts/%
	mkdir -p build/scripts
	echo "#! $(bindir)/pyon" > $@
	cat $< >> $@

%.hi : %.o ;
%_stub.c : %.o ;
%_stub.h : %.o ;

# Dependences
include depend_hs.mk
