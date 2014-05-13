dnl This file is used by autoconf to generate the configure script
dnl by the HoTT development team. Unless you already know what the
dnl things below mean, you probably do not want to touch anything.

AC_INIT([hott],[1.0])
AC_PREREQ([2.67])
AC_CONFIG_SRCDIR([theories/Overture.v])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
# Autoregenerate Makefile if needed
AM_MAINTAINER_MODE([enable])
AM_INIT_AUTOMAKE([foreign no-dependencies])

# Check for programs
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P

# Check to see if COQBIN was set
AC_ARG_VAR([COQBIN], [the directory that contains the Coq executables])
# use 'test "x$foo" != "x"' rather than 'test -n "$foo"' as per
# http://www.gnu.org/software/automake/manual/autoconf.html#Limitations-of-Builtins;
# some shells get confused if $foo is a weird character like '!' or
# '-n'
AS_IF([test "x$COQBIN" != "x"],
      [AC_MSG_NOTICE([Will look for Coq executables only in $COQBIN])
       COQBIN_PATH="$COQBIN"],
      [COQBIN_PATH="$PATH"])

# Checking for coqtop
AC_ARG_VAR([COQTOP], [the absolute path of the coqtop executable])
AS_IF([test "x$COQTOP" != "x"],
      [AC_MSG_CHECKING([for coqtop])
       AC_MSG_RESULT([(preset) $COQTOP])
       AC_SUBST([COQTOP])],
      [AC_PATH_PROG([COQTOP],[coqtop],[no],[$COQBIN_PATH])])

AS_IF([test "x$COQTOP" = "xno"],
      [AC_MSG_ERROR([Could not find coqtop])],
      [AC_MSG_CHECKING([coqtop version])
       COQVERSION="`"$COQTOP" -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
       AC_MSG_RESULT([$COQVERSION])
       AC_MSG_CHECKING([Coq library path])
       COQLIB="`"$COQTOP" -where 2>/dev/null | tr -d '\r'`"
       AC_MSG_RESULT([$COQLIB])
       AC_SUBST([COQVERSION])
       AC_SUBST([COQLIB])

       indicesmatter="`"$COQTOP" -help 2>&1 | grep -c -- -indices-matter`"
       AS_IF([test "$indicesmatter" = "0"],
             [AC_MSG_ERROR([You need a version of Coq which supports -indices-matter])
             ])
      ])

# Checking for bytecode version of coqtop
AM_CONDITIONAL(make_hoqtopbyte, [test -x "$COQTOP.byte"])

# Now set COQBIN if it has not been set yet. We need COQBIN because Makefiles
# produced by coq_makefile insist on running coqtop as $(COQBIN)coqtop.
AS_IF([test "x$COQBIN" = "x"],
      [COQBIN=`AS_DIRNAME(["$COQTOP"])`])
AC_MSG_NOTICE([COQBIN is $COQBIN])

# Checking for coqc
AC_ARG_VAR([COQC], [the absolute path of the coqc executable])
AS_IF([test "x$COQC" != "x"],
      [AC_MSG_CHECKING([for coqc])
       AC_MSG_RESULT([(preset) $COQC])
       AC_SUBST([COQC])],
      [AC_PATH_PROG([COQC],[coqc],[no],[$COQBIN_PATH])])

AS_IF([test "x$COQC" = "xno"],
      [AC_MSG_ERROR([Could not find coqc])],
      [AC_MSG_CHECKING([coqc version])
       COQCVERSION=`"$COQC" -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
       AC_MSG_RESULT([$COQCVERSION])
       AC_SUBST([COQCVERSION])
       AS_IF([test "x$COQCVERSION" != "x$COQVERSION"],
             [AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQCVERSION])])
      ])

# Checking for coqide, which can be optional
make_coqide="no"
AC_ARG_WITH([coqide],
            [AS_HELP_STRING([--without-coqide], [disable support for coqide])],
            [],
            [make_coqide="yes"])

AS_IF([test "x$make_coqide" = "xno"],
      [AC_MSG_NOTICE([Will not make hoqide])],
      [AC_ARG_VAR([COQIDE], [the absolute path of the coqide executable])
       AS_IF([test "x$COQIDE" != "x"],
             [AC_MSG_CHECKING([for coqide])
              AC_MSG_RESULT([(preset) $COQIDE])
              AC_SUBST([COQIDE])],
             [AC_PATH_PROG([COQIDE],[coqide],[no],[$COQBIN_PATH])])
       AS_IF([test "x$COQIDE" = "xno"],
             [AC_MSG_NOTICE([Could not find coqide, will not make hoqide])
              make_coqide="no"],
             [AC_MSG_NOTICE([Trusting that coqide version is $COQVERSION])
              COQIDEVERSION="$COQVERSION"
              AC_SUBST([COQIDEVERSION])
              AS_IF([test "x$COQIDEVERSION" != "x$COQVERSION"],
                    [AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQIDEVERSION])])
             ])
      ])

AM_CONDITIONAL(make_hoqide, [test "$make_coqide" = "yes"])

# checking for coqdep
AC_ARG_VAR([COQDEP], [the absolute path of the coqdep executable])
AS_IF([test "x$COQDEP" != "x"],
      [AC_MSG_CHECKING([for coqdep])
       AC_MSG_RESULT([(preset) $COQDEP])
       AC_SUBST([COQDEP])],
      [AC_PATH_PROG([COQDEP],[coqdep],[no],[$COQBIN_PATH])])

AS_IF([test "x$COQDEP" = "xno"],
      [AC_MSG_ERROR([Could not find coqdep])])


# checking for coqdoc
AC_ARG_VAR([COQDOC], [the absolute path of the coqdoc executable])
AS_IF([test "x$COQDOC" != "x"],
      [AC_MSG_CHECKING([for coqdoc])
       AC_MSG_RESULT([(preset) $COQDOC])
       AC_SUBST([COQDOC])],
      [AC_PATH_PROG([COQDOC],[coqdoc],[no],[$COQBIN_PATH])])

AS_IF([test "x$COQDOC" = "xno"],
      [AC_MSG_ERROR([Could not find coqdoc])])

# checking for coq_makefile
AC_ARG_VAR([COQMAKEFILE], [the absolute path of the coq_makefile executable])
AS_IF([test "x$COQMAKEFILE" != "x"],
      [AC_MSG_CHECKING([for coq_makefile])
       AC_MSG_RESULT([(preset) $COQMAKEFILE])
       AC_SUBST([COQMAKEFILE])],
      [AC_PATH_PROG([COQMAKEFILE],[coq_makefile],[no],[$COQBIN_PATH])])

AS_IF([test "x$COQMAKEFILE" = "xno"],
      [AC_MSG_ERROR([Could not find coq_makefile])])


hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

AC_CHECK_PROGS(ETAGS,etags,[: skipping etags])

AC_ARG_VAR([TIME], [the absolute path of a 'time' command])
AC_PATH_PROG([TIME],[time],[no])
AS_IF([test "x$TIME" = "xno"],
      [STDTIME=""],
      [STDTIME="\"$TIME\" -f \"\$* (user: %U mem: %M ko)\""])
AC_SUBST([STDTIME])

dnl Create symbolic links to the Coq library
AC_MSG_NOTICE([Creating symbolic links into Coq standard library])
# We must have these links in the source directory, not in the build
# directory, because the replacement standard library lives in the source
# directory, and these links are required to make Coq accept it.
# First remove existing links.  If they are symlinks, use -f.  If they are
# physical directories, use -rf.  This ensures that we don't delete the
# contents of symlinked directories.
AS_IF([test -h "$srcdir/coq/dev"], [rm -f "$srcdir/coq/dev"],
      [test -d "$srcdir/coq/dev"], [rm -rf "$srcdir/coq/dev"])
AS_IF([test -h "$srcdir/coq/kernel"], [rm -f "$srcdir/coq/kernel"],
      [test -d "$srcdir/coq/kernel"], [rm -rf "$srcdir/coq/kernel"])
AS_IF([test -h "$srcdir/coq/library"], [rm -f "$srcdir/coq/library"],
      [test -d "$srcdir/coq/library"], [rm -rf "$srcdir/coq/library"])
AS_IF([test -h "$srcdir/coq/plugins"], [rm -f "$srcdir/coq/plugins"],
      [test -d "$srcdir/coq/plugins"], [rm -rf "$srcdir/coq/plugins"])
ln -s "$COQLIB/dev" "$COQLIB/kernel" "$COQLIB/library" "$COQLIB/plugins" "$srcdir/coq"
# TODO(jgross): Should we use AC_CONFIG_LINKS?  But $COQLIB/dev
# doesn't exist in my installation, and that would make configure
# error...
#AC_CONFIG_LINKS([$srcdir/coq/plugins:$COQLIB/plugins
#                 $srcdir/coq/dev:$COQLIB/dev])
AC_MSG_CHECKING([whether your coqtop supports directory symlinks to the stdlib])
coqtop_out="$("$COQTOP" -coqlib "$srcdir/coq" < /dev/null 2>&1 | grep -c 'Warning: Cannot open')"
AS_IF([test "$coqtop_out" = 0],
      [AC_MSG_RESULT([yes])],
      [AC_MSG_RESULT([no])
       AC_MSG_NOTICE([Falling back on making physical copies of the stdlib])
       rm -f "$srcdir/coq/dev" "$srcdir/coq/kernel" "$srcdir/coq/library" "$srcdir/coq/plugins"
       cp -R "$COQLIB/dev" "$COQLIB/kernel" "$COQLIB/library" "$COQLIB/plugins" "$srcdir/coq"])


AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoq-run])

AC_OUTPUT
