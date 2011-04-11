# The main makefile.
#
# This makefile is invoked from the Setup script to do tasks based on file
# existence or timestamps.

# Require a target
default :
	@echo "No target specified"
	@echo "(This file is not meant to be invoked directly)"

include variables.mk

###############################################################################
# Targets

.PHONY : default build bootstrap_data data

# Create executable, library, and scripts; then run Python's setup script 
build : $(PYON_TARGET) $(RTS_TARGET) data

# Install a minimal set of data files into the local build directory, so that
# the compiler can be run out of the local directory.
bootstrap_data : $(BOOT_DATA_FILES) \
	$(DATA_BUILD_DIR)/include/pyon.h

# Install all data files into the local build directory
data : bootstrap_data $(DATA_BUILD_DIR)/include/pyon.h $(DATA_BUILD_DIR)/libpyonrts.so $(INTERFACE_DATA_FILES)

###############################################################################
# Compilation

# Link all object files
$(PYON_TARGET) : $(PYON_OBJECT_FILES)
	mkdir -p $(dir $(PYON_TARGET))
	$(HC) $(PYON_L_OPTS) $(PYON_OBJECT_FILES) -o $@

# Link RTS files into a dynamic library
$(RTS_TARGET) : $(RTS_OBJECT_FILES)
	mkdir -p $(dir $(RTS_TARGET))
	$(LINKSHARED) $(RTS_LINK_OPTS) \
		-g $(RTS_OBJECT_FILES) -o $(RTS_TARGET) $(TARGET_LIBS)

# Move the library into the data directory
$(DATA_BUILD_DIR)/libpyonrts.so : $(RTS_TARGET)
	cp $< $@

###############################################################################
# Generic rules

%.hi : %.o ;
%.p_hi : %.hi %.p_o ;
%_stub.c : %.o ;
%_stub.h : %.o ;
%.hi-boot : %.o-boot ;
%.p_hi-boot : %.hi-boot %.p_o-boot ;

# Dependences
include .depend_hs.mk
include .depend_hs_p.mk
include .depend.mk
