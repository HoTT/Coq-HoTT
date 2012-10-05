AC_INIT([hott],[1.0])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

AC_PROG_COQ

if test "$COQTOP" = "no"; then
  AC_MSG_ERROR([You must install Coq first])
fi

relevantequality=`$COQTOP -help 2>&1 | grep -c -- -relevant-equality`
if test "$relevantequality" = "0"; then
  AC_MSG_ERROR([You need a version of Coq which supports -relevant-equality])
fi

warnuniverse=`$COQTOP -help 2>&1 | grep -c -- -warn-universe-inconsistency`
if test "$warnuniverse" = "0"; then
  AC_MSG_ERROR([You need a version of Coq which supports -warn-universe-inconsistency])
fi

hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
