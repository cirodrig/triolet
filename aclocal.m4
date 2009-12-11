
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
dnl Python executable must exist
if test -z $cir_python; then
  AC_MSG_ERROR([Must find python executable before using it])
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
dnl Python executable must exist
if test -z $cir_python; then
  AC_MSG_ERROR([Must find python executable before using it])
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
AC_MSG_CHECKING([[python version]])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_python_version()]],[[cir_python_version]])
AC_MSG_RESULT([[$cir_python_version]])
])

########################################
# CIR_PY_INCDIR()
# Get the python include directory and put it into 'cir_python_incdir'
AC_DEFUN([CIR_PY_INCDIR],[
AC_MSG_CHECKING([[python include directory]])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_python_inc()]],[[cir_python_incdir]])
AC_MSG_RESULT([[$cir_python_incdir]])
])

########################################
# CIR_PY_LIBDIR()
# Get the directory containing the python library and put it into 'cir_python_libdir'
AC_DEFUN([CIR_PY_LIBDIR],[
AC_MSG_CHECKING([[python library directory]])
CIR_PY_COMMAND([[import distutils.sysconfig; print distutils.sysconfig.get_config_var('LIBPL')]],[[cir_python_libdir]])
AC_MSG_RESULT([[$cir_python_libdir]])
])

########################################
# CIR_HS_LIBDIR()
# Find the GHC library directory
AC_DEFUN([CIR_HS_LIBDIR],[
AC_MSG_CHECKING([path to GHC library directory])
dnl We look at the verbose output of ghc.
dnl One of the lines in there is the full path to the package.conf file,
dnl which is also the library directory.
cir_hs_libdir=`ghc -v 2>&1 | sed -n 's/.* \(.*\)\/package\.conf/\1/p' | head -n1`
if test -z "$cir_hs_libdir"; then
  AC_MSG_ERROR([cannot find GHC library path])
else
  AC_MSG_RESULT([$cir_hs_libdir])
fi
])

########################################
# CIR_HS_CHECK_PACKAGE([lib-name])
# Check that a package is installed
AC_DEFUN([CIR_HS_CHECK_PACKAGE],[
AC_MSG_CHECKING([for package $1])
cir_hs_check_package_val=`$cir_ghc_pkg list $1 | grep -e "$1" -`
if test -z "$cir_hs_check_package_val"; then
  AC_MSG_RESULT([not found])
  AC_MSG_ERROR([[GHC Haskell package not available: $1]])
else
  AC_MSG_RESULT([found])
fi
])