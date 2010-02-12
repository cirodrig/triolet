
AC_INIT(pyon, 0.1)
AC_CANONICAL_HOST

## Check for programs

AC_PROG_CC
AC_PROG_CPP
AC_CHECK_PROG([HAVE_HC], [ghc], [yes], [no])
if test "$HAVE_HC" != "yes"; then AC_MSG_ERROR([Cannot find ghc]); fi
AC_CHECK_PROG([HAVE_HSC2HS], [hsc2hs], [yes], [no])
if test "$HAVE_HSC2HS" != "yes"; then AC_MSG_ERROR([Cannot find hsc2hs]); fi
AC_PATH_PROG([cir_ghc_pkg], [ghc-pkg])
CIR_PROG_PYTHON()
CIR_PY_VERSION()
CIR_HS_VERSION()

case $((($cir_hs_major_version == 6 && $cir_hs_minor_version >= 10) || $cir_hs_major_version > 6)) in
  1) ;;
  *) AC_MSG_ERROR([need ghc 6.10 or above; found $cir_hs_version]) ;;
esac

## Find paths to libraries

CIR_HS_LIBDIR()
CIR_PY_LIBDIR()

## Check for libraries

CIR_HS_CHECK_PACKAGE([base])
CIR_HS_CHECK_PACKAGE([containers])
CIR_HS_CHECK_PACKAGE([mtl])
CIR_HS_CHECK_PACKAGE([fgl])
CIR_HS_CHECK_PACKAGE([language-python-pyon])
CIR_HS_CHECK_PACKAGE([gluon])

## Check for header files

CIR_PY_INCDIR()

## Output

# Force 32-bit build on x86_64 darwin.
case $host in
  x86_64-*-darwin*) BUILD_32BIT=yes;;
  *)                BUILD_32BIT=no;;
esac

AC_SUBST(cir_hs_libdir)
AC_SUBST(cir_python_version)
AC_SUBST(cir_python_incdir)
AC_SUBST(cir_python_libdir)
AC_SUBST(BUILD_32BIT)
AC_SUBST(cir_esed)

AC_CONFIG_FILES([config.mk])
AC_OUTPUT()
