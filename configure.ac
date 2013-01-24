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

   indicesmatter=`$COQTOP -help 2>&1 | grep -c -- -indices-matter`
   if test "$indicesmatter" = "0"; then
       AC_MSG_ERROR([You need a version of Coq which supports -indices-matter])
   fi 
fi

# Checking for bytecode version of coqtop
AM_CONDITIONAL(make_hoqtopbyte, [test -n "$COQTOP.byte"])

# Now set COQBIN if it has not been set yet. We need COQBIN because Makefiles
# produces by coq_makefile insist on running coqtop as $(COQBIN)coqtop, and
# ssreflect uses coq_makefile
if test ! -n "$COQBIN" ; then
   COQBIN=`dirname $COQTOP`
fi
AC_MSG_RESULT([COQBIN is $COQBIN.])

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

# Should we compile ssrfelect?
compile_ssreflect="no"
AC_ARG_WITH([ssreflect],
 [AS_HELP_STRING([--with-ssreflect], [compile the ssreflect libary])],
 [compile_ssreflect="yes"],
 [])

if test "$compile_ssreflect" = "no"
then
   AC_MSG_RESULT([Will not compile ssreflect.])
else
   AC_MSG_RESULT([Will compile ssreflect.])
fi
AM_CONDITIONAL(make_ssreflect, [test "$compile_ssreflect" = "yes"])
AC_SUBST([compile_ssreflect])

# Checking for coqide, which can be optional
make_coqide="no"
AC_ARG_WITH([coqide],
 [AS_HELP_STRING([--without-coqide], [disable support for coqide])],
 [],
 [make_coqide="yes"])

if test "$make_coqide" = "no"
then
   AC_MSG_RESULT([Will not make hoqide.])
else
   AC_ARG_VAR([COQIDE], [the absolute path of the coqide executable])
   if test -n "$COQIDE"; then
      AC_MSG_RESULT([COQIDE was preset to $COQIDE])
      AC_SUBST([COQIDE])
   else
      AC_PATH_PROG([COQIDE],[coqide],[no])
   fi
   if test "$COQIDE" = "no"; then
      AC_MSG_RESULT([Could not find coqide, will not make hoqide.])
      make_coqide="no"
   else
     AC_MSG_RESULT([Trusting that coqide version is $COQVERSION.])
     COQIDEVERSION=$COQVERSION
     AC_SUBST([COQIDEVERSION])
     if test "$COQIDEVERSION" != "$COQVERSION"; then
        AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQIDEVERSION.])
     fi
  fi
fi

AM_CONDITIONAL(make_hoqide, [test "$make_coqide" = "yes"])

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

# checking for coq_makefile
AC_ARG_VAR([COQMAKEFILE], [the absolute path of the coq_makefile executable])
if test -n "$COQMAKEFILE"; then
   AC_MSG_RESULT([COQMAKEFILE was preset to $COQMAKEFILE])
   AC_SUBST([COQMAKEFILE])
else
   AC_PATH_PROG([COQMAKEFILE],[coq_makefile],[no])
fi
if test "$COQMAKEFILE" = "no"; then
   AC_MSG_ERROR([Could not find coq_makefile.])
fi

hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

dnl Create symbolic links to the Coq library
AC_MSG_RESULT([Creating symbolic links into Coq standard library.])
rm -f $srcdir/coq/plugins $srcdir/coq/dev
ln -s $COQLIB/plugins $COQLIB/dev $srcdir/coq

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoqtop], [chmod +x hoqtop])
AC_CONFIG_FILES([hoqtop.byte], [chmod +x hoqtop.byte])
AC_CONFIG_FILES([hoqc], [chmod +x hoqc])
if test "$make_coqide" != "yes" ; then
   AC_CONFIG_FILES([hoqide], [chmod +x hoqide])
fi

AC_OUTPUT
