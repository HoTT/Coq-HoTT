dnl This file is used by autoconf to generate the configure script
dnl by the HoTT development team. Unless you already know what the
dnl things below mean, you probably do not want to touch anything.

AC_INIT([hott],[1.0])
AC_PREREQ([2.67])
AC_CONFIG_SRCDIR([theories/Overture.v])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
# If we ever remove Makefile.in and configure from version control,
# and depend on autoconf, we should replace "AM_MAINTAINER_MODE" with
# "AM_MAINTAINER_MODE([enable])".  Possibly even before then.
AM_MAINTAINER_MODE
AM_INIT_AUTOMAKE([foreign no-dependencies])

# Check for programs
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P

# Check to see if COQBIN was set
AC_ARG_VAR([COQBIN], [the directory which contains the Coq executables])
# use 'test "x$foo" != "x"' rather than 'test -n "$foo"' as per
# http://www.gnu.org/software/automake/manual/autoconf.html#Limitations-of-Builtins;
# some shells get confused if $foo is a weird character like '!' or
# '-n'
if test "x$COQBIN" != "x"; then
   AC_MSG_NOTICE([Will first look for Coq executables in $COQBIN.])
   PATH=$COQBIN$PATH_SEPARATOR$PATH
fi

# Checking for coqtop
AC_ARG_VAR([COQTOP], [the absolute path of the coqtop executable])
if test "x$COQTOP" != "x"; then
   AC_MSG_NOTICE([COQTOP was preset to $COQTOP])
   AC_SUBST([COQTOP])
else
   AC_PATH_PROG([COQTOP],[coqtop],[no])
fi

if test "x$COQTOP" = "xno"; then
   AC_MSG_ERROR([Could not find coqtop.])
else
   AC_MSG_CHECKING([coqtop version])
   COQVERSION="`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
   AC_MSG_RESULT([$COQVERSION])
   AC_MSG_CHECKING([Coq library path])
   COQLIB="`$COQTOP -where 2>/dev/null`"
   AC_MSG_RESULT([$COQLIB])
   AC_SUBST([COQVERSION])
   AC_SUBST([COQLIB])

   indicesmatter="`$COQTOP -help 2>&1 | grep -c -- -indices-matter`"
   if test "$indicesmatter" = "0"; then
       AC_MSG_ERROR([You need a version of Coq which supports -indices-matter])
   fi
fi

# Checking for bytecode version of coqtop
AM_CONDITIONAL(make_hoqtopbyte, [test -x "$COQTOP.byte"])

# Now set COQBIN if it has not been set yet. We need COQBIN because Makefiles
# produces by coq_makefile insist on running coqtop as $(COQBIN)coqtop, and
# ssreflect uses coq_makefile
if test "x$COQBIN" = "x" ; then
   COQBIN=`AS_DIRNAME(["$COQTOP"])`
fi
AC_MSG_NOTICE([COQBIN is $COQBIN.])

# Checking for coqc
AC_ARG_VAR([COQC], [the absolute path of the coqc executable])
if test "x$COQC" != "x"; then
   AC_MSG_NOTICE([COQC was preset to $COQC])
   AC_SUBST([COQC])
else
   AC_PATH_PROG([COQC],[coqc],[no])
fi

if test "x$COQC" = "xno"; then
   AC_MSG_ERROR([Could not find coqc.])
else
   AC_MSG_CHECKING([coqc version])
   COQCVERSION="`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
   AC_MSG_RESULT([$COQCVERSION])
   AC_SUBST([COQCVERSION])
   if test "x$COQCVERSION" != "x$COQVERSION"; then
      AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQCVERSION.])
   fi
fi

# Should we compile ssrfelect?
compile_ssreflect="no"
AC_ARG_WITH([ssreflect],
 [AS_HELP_STRING([--with-ssreflect], [compile the ssreflect libary])],
 [compile_ssreflect="yes"],
 [])

if test "x$compile_ssreflect" = "xno"
then
   AC_MSG_NOTICE([Will not compile ssreflect.])
else
   AC_MSG_NOTICE([Will compile ssreflect.])
fi
AM_CONDITIONAL(make_ssreflect, [test "x$compile_ssreflect" = "xyes"])
AC_SUBST([compile_ssreflect])

# Checking for coqide, which can be optional
make_coqide="no"
AC_ARG_WITH([coqide],
 [AS_HELP_STRING([--without-coqide], [disable support for coqide])],
 [],
 [make_coqide="yes"])

if test "x$make_coqide" = "xno"
then
   AC_MSG_NOTICE([Will not make hoqide.])
else
   AC_ARG_VAR([COQIDE], [the absolute path of the coqide executable])
   if test "x$COQIDE" != "x"; then
      AC_MSG_NOTICE([COQIDE was preset to $COQIDE])
      AC_SUBST([COQIDE])
   else
      AC_PATH_PROG([COQIDE],[coqide],[no])
   fi
   if test "x$COQIDE" = "xno"; then
      AC_MSG_NOTICE([Could not find coqide, will not make hoqide.])
      make_coqide="no"
   else
     AC_MSG_NOTICE([Trusting that coqide version is $COQVERSION.])
     COQIDEVERSION="$COQVERSION"
     AC_SUBST([COQIDEVERSION])
     if test "x$COQIDEVERSION" != "x$COQVERSION"; then
        AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQIDEVERSION.])
     fi
  fi
fi

AM_CONDITIONAL(make_hoqide, [test "$make_coqide" = "yes"])

# checking for coqdep
AC_ARG_VAR([COQDEP], [the absolute path of the coqdep executable])
if test "x$COQDEP" != "x"; then
   AC_MSG_NOTICE([COQDEP was preset to $COQDEP])
   AC_SUBST([COQCDEP])
else
   AC_PATH_PROG([COQDEP],[coqdep],[no])
fi
if test "x$COQDEP" = "xno"; then
   AC_MSG_ERROR([Could not find coqdep.])
fi

# checking for coqdoc
AC_ARG_VAR([COQDOC], [the absolute path of the coqdoc executable])
if test "x$COQDOC" != "x"; then
   AC_MSG_NOTICE([COQDOC was preset to $COQDOC])
   AC_SUBST([COQCDOC])
else
   AC_PATH_PROG([COQDOC],[coqdoc],[no])
fi
if test "x$COQDOC" = "xno"; then
   AC_MSG_ERROR([Could not find coqdoc.])
fi

# checking for coq_makefile
AC_ARG_VAR([COQMAKEFILE], [the absolute path of the coq_makefile executable])
if test "x$COQMAKEFILE" != "x"; then
   AC_MSG_NOTICE([COQMAKEFILE was preset to $COQMAKEFILE])
   AC_SUBST([COQMAKEFILE])
else
   AC_PATH_PROG([COQMAKEFILE],[coq_makefile],[no])
fi
if test "x$COQMAKEFILE" = "xno"; then
   AC_MSG_ERROR([Could not find coq_makefile.])
fi

hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

AC_CHECK_PROGS(ETAGS,etags,[: skipping etags])

dnl Create symbolic links to the Coq library
AC_MSG_NOTICE([Creating symbolic links into Coq standard library.])
# We must have these links in the source directory, not in the build
# directory, because the replacement standard library lives in the source
# directory, and these links are required to make Coq accept it.
rm -f $srcdir/coq/plugins $srcdir/coq/dev
ln -s $COQLIB/plugins $COQLIB/dev $srcdir/coq
# TODO(jgross): Should we use AC_CONFIG_LINKS?  But $COQLIB/dev
# doesn't exist in my installation, and that would make configure
# error...
#AC_CONFIG_LINKS([$srcdir/coq/plugins:$COQLIB/plugins
#                 $srcdir/coq/dev:$COQLIB/dev])

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoqtop], [chmod +x hoqtop])
AC_CONFIG_FILES([hoqtop.byte], [chmod +x hoqtop.byte])
AC_CONFIG_FILES([hoqc], [chmod +x hoqc])
if test "x$make_coqide" = "xyes" ; then
   AC_CONFIG_FILES([hoqide], [chmod +x hoqide])
fi

AC_OUTPUT
