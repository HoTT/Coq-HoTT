AC_INIT([hott],[1.0])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

AC_PROG_COQ

if test "$COQTOP" = "no"; then
  AC_MSG_ERROR([You must install Coq first])
fi

hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
