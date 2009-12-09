
# Directories
BUILDDIR=build/program
SRCDIR=src/program

## System-dependent programs

CC=gcc
HC=ghc
HSC2HS=hsc2hs

## System-dependent flags

# Compiler and linker flags
HSC2HSFLAGS=
HCFLAGS=
CCFLAGS=
LFLAGS=

# Include directories
# Python include path: distutils.sysconfig.get_python_inc()
INCLUDEDIRS=/usr/include/python2.4 /usr/local/lib/ghc-6.10.4/include

# Library directories
LIBDIRS=

# Haskell package names
PACKAGES=language-python-0.1.1 mtl

# Library names
LIBS=python2.4
