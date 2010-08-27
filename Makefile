# The main makefile.
#
# This makefile contains commands that run after dependency generation.
# Commands that run before dependency generation are in 'Makefile'.

# Require a target
default :
	@echo "No target specified"
	@echo "(This file is not meant to be invoked directly)"

include variables.mk

# GHC options passed to haddock.
HADDOCK_HC_OPTS=$(foreach opt, $(HS_C_OPTS), "--optghc=$(opt)")

# For each package, get the location of its haddock interface file
# using ghc-pkg
HADDOCK_INTERFACE_FILES=$(foreach pkg, $(PACKAGES), $(shell ghc-pkg describe $(pkg) --simple-output | $(ESED) -n "s/^haddock-interfaces: (.*)/\1/p"))
HADDOCK_INTERFACE_OPTS=$(foreach ifile, $(HADDOCK_INTERFACE_FILES), -i $(ifile))

###############################################################################
# Targets

.PHONY : default doc build bootstrap_data data testcases

doc : dist/doc/html/pyon/index.html

# Delegate documentation to a script
dist/doc/html/pyon/index.html : $(PYON_HS_SOURCE_FILES)
	@echo "Building documentation..."
	@env ESED="$(ESED)" HADDOCK_HC_OPTS="$(HADDOCK_HC_OPTS)" PYON_HS_SOURCE_FILES="$(PYON_HS_SOURCE_FILES)" PACKAGES="$(PACKAGES)" sh makedoc.sh

# Create executable, library, and scripts; then run Python's setup script 
build : $(PYON_TARGET) $(RTS_TARGET) data

# Install a minimal set of data files into the local build directory, so that
# the compiler can be run out of the local directory.
bootstrap_data : $(BOOT_DATA_FILES) $(RTS_BUILD_DIR)/layout.h $(DATA_BUILD_DIR)/include/pyon_types.h

# Install all data files into the local build directory
data : bootstrap_data testcases $(DATA_BUILD_DIR)/include/pyon.h $(DATA_BUILD_DIR)/libpyonrts.so 

###############################################################################
# Compilation

# Link all object files
$(PYON_TARGET) : $(PYON_OBJECT_FILES)
	mkdir -p $(dir $(PYON_TARGET))
	$(HC) $(PYON_OBJECT_FILES) -o $@ $(PYON_L_OPTS)

# Generate layout info
$(CLAY_TARGET) : $(PYON_OBJECT_FILES) $(CLAY_SOURCE_FILES)
	mkdir -p $(dir $(CLAY_TARGET))
	$(HC) --make $(SRCDIR)/rts/ComputeLayout.hs -o $@ $(CLAY_L_OPTS)
	touch $@

# Autogenerated layout info
$(RTS_BUILD_DIR)/layout.h $(DATA_BUILD_DIR)/include/pyon_types.h : $(CLAY_TARGET)
	mkdir -p $(RTS_BUILD_DIR)
	mkdir -p $(DATA_BUILD_DIR)/include
	$(CLAY_TARGET) $(RTS_BUILD_DIR)/layout.h $(DATA_BUILD_DIR)/include/pyon_types.h

# Assemble global objects
$(RTS_BUILD_DIR)/rts_objects.o : $(SRCDIR)/rts/rts_objects.s
	mkdir -p $(RTS_BUILD_DIR)
	gcc -m32 -c -o $@ $< 

# Link RTS files into a dynamic library
$(RTS_TARGET) : $(BUILDDIR)/rts/layout.h $(CLAY_TARGET) $(RTS_OBJECT_FILES) $(RTS_BUILD_DIR)/rts_objects.o
	mkdir -p $(dir $(RTS_TARGET))
	$(LINKSHARED) -g -install_name libpyonrts.so $(RTS_OBJECT_FILES) $(RTS_BUILD_DIR)/rts_objects.o -o $(RTS_TARGET) -lc $(LINKFLAGS)

# Move the library into the data directory
$(DATA_BUILD_DIR)/libpyonrts.so : $(RTS_TARGET)
	cp $< $@

###############################################################################
# Generic rules

%.hi : %.o ;
%_stub.c : %.o ;
%_stub.h : %.o ;
%.hi-boot : %.o-boot ;

# Dependences
include .depend_hs.mk
include .depend.mk
