dnl This file is used by autoconf to generate the configure script
dnl by the HoTT development team. Unless you already know what the
dnl things below mean, you probably do not want to touch anything.

AC_INIT([hott],[1.0])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

# checking for coqtop
AC_PATH_PROG([COQTOP],[coqtop],[no])
AC_MSG_RESULT([found $COQTOP.])
if test "$COQTOP" != "no"; then
   COQVERSION=`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
   AC_MSG_RESULT([Coq version is $COQVERSION.])
   COQLIB=`$COQTOP -where 2>/dev/null`
   AC_MSG_RESULT([Coq library path is $COQLIB])
   AC_SUBST([COQVERSION])
   AC_SUBST([COQLIB])
fi

AC_PATH_PROG([COQC],[coqc],[no])
AC_MSG_RESULT([found $COQC.])
if test "$COQC" != "no"; then
  COQCVERSION=`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
  AC_MSG_RESULT([Coqc version is $COQCVERSION.])
  AC_SUBST([COQCVERSION])
fi

# checking for coqdep
AC_PATH_TOOL([COQDEP],[coqdep],[no])

# checking for coqdoc
AC_PATH_TOOL([COQDOC],[coqdoc],[no])

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

dnl Create symbolic links to the Coq library
AC_MSG_RESULT([Creating symbolic links into Coq standard library.])
rm -f $srcdir/coq/plugins $srcdir/coq/dev
ln -s $COQLIB/plugins $COQLIB/dev $srcdir/coq

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoqtop], [chmod +x hoqtop])
AC_CONFIG_FILES([hoqc], [chmod +x hoqc])
AC_OUTPUT
