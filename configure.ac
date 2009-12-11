
AC_INIT(pyon, 0.1)
AC_CANONICAL_HOST

## Check for programs

AC_PROG_CC
AC_PROG_CPP
AC_CHECK_PROG([HAVE_HC], [ghc], [yes], [no])
AC_CHECK_PROG([HAVE_HSC2HS], [hsc2hs], [yes], [no])
AC_PATH_PROG([cir_ghc_pkg], [ghc-pkg])
CIR_PROG_PYTHON()
CIR_PY_VERSION()

## Find paths to libraries

CIR_HS_LIBDIR()
CIR_PY_LIBDIR()

## Check for libraries

CIR_HS_CHECK_PACKAGE([[mtl]])
CIR_HS_CHECK_PACKAGE([[language-python-0.1.1]])

## Check for header files

CIR_PY_INCDIR()

## Output

# Force 32-bit build on darwin.
echo $host
case $host in
  i?86-*-darwin*) BUILD_32BIT=yes;;
  *)              BUILD_32BIT=no;;
esac

AC_SUBST(cir_hs_libdir)
AC_SUBST(cir_python_version)
AC_SUBST(cir_python_incdir)
AC_SUBST(cir_python_libdir)
AC_SUBST(BUILD_32BIT)

AC_CONFIG_FILES([config.mk])
AC_OUTPUT()
