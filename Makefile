# The entry-point Makefile.
#
# This makefile contains commands that run before dependency generation.
# Commands that rely on auto-generated dependences are in 'build.mk'.

include variables.mk

DEPEND_DEPENDENCES=$(PYON_HS_GENERATED_FILES) depend

###############################################################################
# Targets

.PHONY : all depend clean veryclean doc build install

all : build

doc : $(DEPEND_DEPENDENCES)
	$(MAKE) -f build.mk doc

build : $(DEPEND_DEPENDENCES)
	$(MAKE) -f build.mk build

install : $(DEPEND_DEPENDENCES)
	$(MAKE) -f build.mk install

clean :
	rm -f src/pyon/data_dir.py
	rm -f depend_hs.mk
	rm -f depend_hs.mk.bak
	if [ -d build ]; then rm -rf build; fi

veryclean : clean
	find src -name "*~" -exec rm {} ';'
	rm -f config.log
	rm -f config.status
	rm -f config.mk
	rm -f configure
	rm -rf autom4te.cache

depend : depend_hs.mk

depend_hs.mk : $(PYON_HS_GENERATED_FILES)
	sh makedepend.sh

###############################################################################
# Autogenerated files and preprocessors

# Preprocess HSC files
$(BUILDDIR)/PythonInterface/Python.hs : $(SRCDIR)/PythonInterface/Python.hsc
	mkdir -p $(BUILDDIR)/PythonInterface
	$(HSC2HS) $(HS_HSC2HS_OPTS) $< -o $@

$(BUILDDIR)/PythonInterface/HsObject.hs : $(SRCDIR)/PythonInterface/HsObject.hsc
	mkdir -p $(BUILDDIR)/PythonInterface
	$(HSC2HS) $(HS_HSC2HS_OPTS) $< -o $@

# Generate a file with path information
$(BUILDDIR)/Paths_pyon.hs :
	mkdir -p $(BUILDDIR)	
	echo "{- Auto-generated source file -} module Paths_pyon where { import System.FilePath; getDataFileName :: String -> IO String; getDataFileName n = return (\"$(prefix)/share/pyon\" </> n) }" > $@
