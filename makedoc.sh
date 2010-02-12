#!/bin/bash
# Generate Haddock documentation.

# Parameters (from environment):
#  $PYON_SOURCE_FILES: Space-seprated list of all source files
#  $PACKAGES: Space-separated list of all packages
#  $ESED: Extended SED command
#  $HADDOCK_HC_OPTS: Options to be passed to GHC

if [ "$ESED" == "" ];
  then
    echo "Extended sed command is not set"
    exit 1
fi

# Read one field from the package information produced by ghc-pkg
function readpkgfield()
{
    # Get package description; find field; print value; stop
    ghc-pkg describe --simple-output $1 | ${ESED} -n "/^$2:/{s/^$2: (.*)/\1/p;q;}"
}

# Construct a list of interface file parameters, giving the file name and
# path of each installed HTML documentation tree
INTERFACE_OPTS=""
for pkg in $PACKAGES
  do
    PKG_INTERFACE_FILES=`readpkgfield ${pkg} haddock-interfaces`
    PKG_PATH=`readpkgfield ${pkg} haddock-html`

    for ifile in $PKG_INTERFACE_FILES
      do
        INTERFACE_OPTS="$INTERFACE_OPTS -i${PKG_PATH},${ifile}"
    done
done

# Create output directory
mkdir -p dist/doc/html/pyon

# Run haddock
haddock -h -o dist/doc/html/pyon ${HADDOCK_HC_OPTS} ${INTERFACE_OPTS} ${PYON_SOURCE_FILES}
