#!/bin/bash
# Compute dependences among Haskell files.  All source files must exist so that
# they can be scanned.  This entails running preprocessors in some cases.

# Consider dependences from Main, and also from each source file
# that exports symbols to C.
SRCS=""
for sourcefile in \
    Main.hs \
    Parser/Driver.hs \
    Pyon/Exports/Gluon.hs \
    Pyon/Exports/SystemF.hs
  do
    # The file must be found in one of these paths.
    for basepath in src/program build/program
      do
        if [ -f ${basepath}/${sourcefile} ]
          then
	    SRCS="$SRCS ${basepath}/${sourcefile}"
	    continue 2
	fi
    done
    echo "Dependency generation failed: could not find file" ${sourcefile}
    exit 1
done

# Run GHC in dependency generation mode
ghc -M -dep-makefile depend_hs.mk \
 -ibuild/program -isrc/program -hidir build/program -odir build/program \
 $SRCS
