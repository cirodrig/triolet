
# Directories
BUILDDIR=build/program
SRCDIR=src/program

## System-dependent programs

CC=gcc
HC=ghc
HSC2HS=hsc2hs

## System-dependent flags

# Compiler and linker flags
HSC2HSFLAGS=--cflag=-m32 --lflag=-m32
HCFLAGS=
CCFLAGS=-m32
LFLAGS=-optl-m32

# Include directories
# Python include path: distutils.sysconfig.get_python_inc()
INCLUDEDIRS=/Library/Frameworks/GHC.framework/Versions/Current/usr/lib/ghc-6.10.4/include /Developer/SDKs/MacOSX10.6.sdk/System/Library/Frameworks/Python.framework/Versions/2.6/include/python2.6/

# Library directories
LIBDIRS=

# Haskell package names
PACKAGES=language-python-0.1.1 mtl

# Library names
LIBS=python2.6
