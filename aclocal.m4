
########################################
# CIR_SED_EXTENDED_COMMAND()
# Figure out how to run sed with extended regexp
# The command is assigned to variable 'cir_esed'
AC_DEFUN([CIR_SED_EXTENDED_COMMAND],[
AC_MSG_CHECKING([how to use extended regexps with sed])
if   (echo x | sed    's/x+/yes/p' | grep yes) >/dev/null 2>&1; then
  cir_esed="sed"
elif (echo x | sed -r 's/x+/yes/p' | grep yes) >/dev/null 2>&1; then
  cir_esed="sed -r"
elif (echo x | sed -E 's/x+/yes/p' | grep yes) >/dev/null 2>&1; then
  cir_esed="sed -E"
fi
if test -n "$cir_esed"; then
  AC_MSG_RESULT([$cir_esed])
else
  AC_MSG_ERROR([cannot use extended regexps])
fi
])

########################################
# CIR_PROG_PYTHON()
# Find an installed 'python'
AC_DEFUN([CIR_PROG_PYTHON],[
AC_PATH_PROG([cir_python],[python])
])

########################################
# CIR_PY_EXCEPTION_IFELSE([python-line],[if-pass],[if-fail])
# Run a one-line python command and perform one action if it terminates
# normally, or another action if it terminates with an error.
#
# The python command will be in quotes, so it must not contain double quotes.
AC_DEFUN([CIR_PY_EXCEPTION_IFELSE],[
AC_REQUIRE([CIR_PROG_PYTHON])
dnl Python executable must exist
if test -z $cir_python; then
  AC_MSG_ERROR([Need python to continue])
fi
if $cir_python -c "$1" >/dev/null 2>&1; then
  $2
else
  $3
fi
])

########################################
# CIR_PY_COMMAND([python-line],[variable-name])
# Run a one-line python command and assign its output to a variable
AC_DEFUN([CIR_PY_COMMAND],[
AC_REQUIRE([CIR_PROG_PYTHON])
dnl Python executable must exist
if test -z $cir_python; then
  AC_MSG_ERROR([Need python to continue])
fi
$2=`$cir_python -c "$1"`
if test "$?" != "0"; then
  AC_MSG_ERROR([Command failed: $1])
fi
])

########################################
# CIR_PY_VERSION()
# Get the python version and put it into 'cir_python_version'
# The version is a string such as "2.4.4"
AC_DEFUN([CIR_PY_VERSION],[
AC_REQUIRE([CIR_PROG_PYTHON])
AC_MSG_CHECKING([python version])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_python_version()]],[cir_python_version])
AC_MSG_RESULT([$cir_python_version])
])

########################################
# CIR_PY_INCDIR()
# Get the python include directory and put it into 'cir_python_incdir'
AC_DEFUN([CIR_PY_INCDIR],[
AC_REQUIRE([CIR_PROG_PYTHON])

# Find include directory
AC_MSG_CHECKING([python include directory])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_python_inc()]],[cir_python_incdir])
if test ! -d "$cir_python_incdir"; then
  AC_MSG_ERROR([registered with Python distutils as $cir_python_incdir, but this directory does not exist])
fi
AC_MSG_RESULT([$cir_python_incdir])

# Make sure the directory exists and contains Python.h
AC_MSG_CHECKING([whether $cir_python_incdir/Python.h exists])
if test ! -f "$cir_python_incdir/Python.h"; then
  AC_MSG_ERROR([not found])
fi
AC_MSG_RESULT([found])
])

########################################
# CIR_PY_LIBDIR()
# Get the directory containing the python library and put it into 'cir_python_libdir'
AC_DEFUN([CIR_PY_LIBDIR],[
AC_REQUIRE([CIR_PROG_PYTHON])
AC_MSG_CHECKING([python library directory])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_config_var('LIBPL')]],[cir_python_libdir])
AC_MSG_RESULT([$cir_python_libdir])
])

########################################
# CIR_HS_VERSION()
# Get the version of GHC
# Search for a string like "version 1.2.3.4" in the output of 'ghc --version'
# Put the version number in cir_hs_version,
# the major version in cir_hs_major_version,
# and the minor version in cir_hs_minor_version
AC_DEFUN([CIR_HS_VERSION],[
AC_REQUIRE([CIR_SED_EXTENDED_COMMAND])
AC_MSG_CHECKING([version of GHC])
cir_hs_version=`ghc --numeric-version`
if test $? != 0 -o -z "$cir_hs_version"; then
  AC_MSG_ERROR([failed to identify GHC version])
else
  AC_MSG_RESULT([$cir_hs_version])
fi
cir_hs_major_version=`echo $cir_hs_version | $cir_esed -n 's/(@<:@0-9@:>@+)\.(@<:@0-9.@:>@+)*/\1/p'`
cir_hs_minor_version=`echo $cir_hs_version | $cir_esed -n 's/@<:@0-9@:>@+\.(@<:@0-9@:>@+)(\..*)?/\1/p'`
if test -z "$cir_hs_major_version" -o -z "$cir_hs_minor_version"; then
  AC_MSG_FAILURE([malformed GHC version string])
fi
])

########################################
# CIR_HS_LIBDIR()
# Find the GHC library directory
AC_DEFUN([CIR_HS_LIBDIR],[
AC_REQUIRE([CIR_SED_EXTENDED_COMMAND])
AC_MSG_CHECKING([path to GHC library directory])
dnl We look at the verbose output of ghc.
dnl One of the lines in there is the full path to the package.conf file,
dnl which is also the library directory.
cir_hs_libdir=`ghc --print-libdir`
if test $? != 0 -o -z "$cir_hs_libdir"; then
  AC_MSG_ERROR([cannot find GHC library path])
else
  AC_MSG_RESULT([$cir_hs_libdir])
fi
])

########################################
# CIR_REQUIRE_GHC_PKG()
# Check that ghc-pkg is installed, and put its path into cir_ghc_pkg
AC_DEFUN([CIR_REQUIRE_GHC_PKG],[
AC_PATH_PROG([cir_ghc_pkg], [ghc-pkg])
])

########################################
# CIR_HS_CHECK_PACKAGE([lib-name])
# Check that a package is installed
#
# Call ghc-pkg and check whether the package name is present
# in the output
AC_DEFUN([CIR_HS_CHECK_PACKAGE],[
AC_REQUIRE([CIR_REQUIRE_GHC_PKG])
AC_MSG_CHECKING([for package $1])
cir_hs_check_package_val=`$cir_ghc_pkg list $1 | grep -e "$1" -`
if test -z "$cir_hs_check_package_val"; then
  AC_MSG_RESULT([not found])
  AC_MSG_ERROR([GHC Haskell package not available: $1])
else
  AC_MSG_RESULT([found])
fi
])
