dnl This file is used by autoconf to generate the configure script
dnl by the HoTT development team. Unless you already know what the
dnl things below mean, you probably do not want to touch anything.

AC_INIT([hott],[1.0])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

# Check to see if COQBIN was set
AC_ARG_VAR([COQBIN], [the directory which contains the Coq executables])
if test -n "$COQBIN"; then
   AC_MSG_RESULT([Will first look for Coq executables in $COQBIN.])
   PATH=$COQBIN:$PATH
fi

# Checking for coqtop
AC_ARG_VAR([COQTOP], [the absolute path of the coqtop executable])
if test -n "$COQTOP"; then
   AC_MSG_RESULT([COQTOP was preset to $COQTOP])
   AC_SUBST([COQTOP])
else
   AC_PATH_PROG([COQTOP],[coqtop],[no])
fi

if test "$COQTOP" = "no"; then
   AC_MSG_ERROR([Could not find coqtop.])
else
   COQVERSION=`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
   AC_MSG_RESULT([coqtop version is $COQVERSION.])
   COQLIB=`$COQTOP -where 2>/dev/null`
   AC_MSG_RESULT([Coq library path is $COQLIB])
   AC_SUBST([COQVERSION])
   AC_SUBST([COQLIB])

   relevantequality=`$COQTOP -help 2>&1 | grep -c -- -relevant-equality`
   if test "$relevantequality" = "0"; then
       AC_MSG_ERROR([You need a version of Coq which supports -relevant-equality])
   fi 

   warnuniverse=`$COQTOP -help 2>&1 | grep -c -- -warn-universe-inconsistency`
   if test "$warnuniverse" = "0"; then
      AC_MSG_ERROR([You need a version of Coq which supports -warn-universe-inconsistency])
   fi
fi

# Checking for coqc
AC_ARG_VAR([COQC], [the absolute path of the coqc executable])
if test -n "$COQC"; then
   AC_MSG_RESULT([COQC was preset to $COQC])
   AC_SUBST([COQC])
else
   AC_PATH_PROG([COQC],[coqc],[no])
fi

if test "$COQC" = "no"; then
   AC_MSG_ERROR([Could not find coqc.])
else
  COQCVERSION=`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
  AC_MSG_RESULT([coqc version is $COQCVERSION.])
  AC_SUBST([COQCVERSION])
  if test "$COQCVERSION" != "$COQVERSION"; then
     AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQCVERSION.])
  fi
fi

# Checking for coqide, which can be optional
without_coqide="no"
AC_ARG_WITH([coqide],
 [AS_HELP_STRING([--without-coqide], [disable support for coqide])],
 [],
 [with_coqide=yes])
AM_CONDITIONAL(make_hoqide, [test "$with_coqide" = "yes"])

if test "$with_coqide" != "yes"; then
   AC_MSG_RESULT([Skipping coqide support, as requested.])
else
   AC_ARG_VAR([COQIDE], [the absolute path of the coqide executable])
   if test -n "$COQIDE"; then
      AC_MSG_RESULT([COQIDE was preset to $COQIDE])
      AC_SUBST([COQIDE])
   else
      AC_PATH_PROG([COQIDE],[coqide],[no])
   fi
   if test "$COQIDE" = "no"; then
      AC_MSG_ERROR([Could not find coqide (configure using --without-coqide).])
   else
     AC_MSG_RESULT([Trusting that coqide version is $COQVERSION.])
     COQIDEVERSION=$COQVERSION
     AC_SUBST([COQIDEVERSION])
     if test "$COQIDEVERSION" != "$COQVERSION"; then
        AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQIDEVERSION.])
     fi
  fi
fi

# checking for coqdep
AC_ARG_VAR([COQDEP], [the absolute path of the coqdep executable])
if test -n "$COQDEP"; then
   AC_MSG_RESULT([COQDEP was preset to $COQDEP])
   AC_SUBST([COQCDEP])
else
   AC_PATH_PROG([COQDEP],[coqdep],[no])
fi
if test "$COQDEP" = "no"; then
   AC_MSG_ERROR([Could not find coqdep.])
fi

# checking for coqdoc
AC_ARG_VAR([COQDOC], [the absolute path of the coqdoc executable])
if test -n "$COQDOC"; then
   AC_MSG_RESULT([COQDOC was preset to $COQDOC])
   AC_SUBST([COQCDOC])
else
   AC_PATH_PROG([COQDOC],[coqdoc],[no])
fi
if test "$COQDOC" = "no"; then
   AC_MSG_ERROR([Could not find coqdoc.])
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
if test "x$without_coqide" != "xyes" ; then
   AC_CONFIG_FILES([hoqide], [chmod +x hoqide])
fi

AC_OUTPUT
