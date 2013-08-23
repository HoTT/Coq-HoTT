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
AC_ARG_VAR([COQBIN], [the directory that contains the Coq executables])
# use 'test "x$foo" != "x"' rather than 'test -n "$foo"' as per
# http://www.gnu.org/software/automake/manual/autoconf.html#Limitations-of-Builtins;
# some shells get confused if $foo is a weird character like '!' or
# '-n'
AS_IF([test "x$COQBIN" != "x"],
      [AC_MSG_NOTICE([Will first look for Coq executables in $COQBIN])
       COQBIN_WITH_SEP="$COQBIN$PATH_SEPARATOR"],
      [COQBIN_WITH_SEP=""])

# Checking for coqtop
AC_ARG_VAR([COQTOP], [the absolute path of the coqtop executable])
AS_IF([test "x$COQTOP" != "x"],
      [AC_MSG_CHECKING([for coqtop])
       AC_MSG_RESULT([(preset) $COQTOP])
       AC_SUBST([COQTOP])],
      [AC_PATH_PROG([COQTOP],[coqtop],[no],[$COQBIN_WITH_SEP$PATH])])

AS_IF([test "x$COQTOP" = "xno"],
      [AC_MSG_ERROR([Could not find coqtop])],
      [AC_MSG_CHECKING([coqtop version])
       COQVERSION="`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
       AC_MSG_RESULT([$COQVERSION])
       AC_MSG_CHECKING([Coq library path])
       COQLIB="`$COQTOP -where 2>/dev/null`"
       AC_MSG_RESULT([$COQLIB])
       AC_SUBST([COQVERSION])
       AC_SUBST([COQLIB])

       indicesmatter="`$COQTOP -help 2>&1 | grep -c -- -indices-matter`"
       AS_IF([test "$indicesmatter" = "0"],
             [AC_MSG_ERROR([You need a version of Coq which supports -indices-matter])
             ])
      ])

# Checking for bytecode version of coqtop
AM_CONDITIONAL(make_hoqtopbyte, [test -x "$COQTOP.byte"])

# Now set COQBIN if it has not been set yet. We need COQBIN because Makefiles
# produces by coq_makefile insist on running coqtop as $(COQBIN)coqtop, and
# ssreflect uses coq_makefile
AS_IF([test "x$COQBIN" = "x"],
      [COQBIN=`AS_DIRNAME(["$COQTOP"])`])
AC_MSG_NOTICE([COQBIN is $COQBIN])

# Checking for coqc
AC_ARG_VAR([COQC], [the absolute path of the coqc executable])
AS_IF([test "x$COQC" != "x"],
      [AC_MSG_CHECKING([for coqc])
       AC_MSG_RESULT([(preset) $COQC])
       AC_SUBST([COQC])],
      [AC_PATH_PROG([COQC],[coqc],[no],[$COQBIN$PATH_SEPARATOR$PATH])])

AS_IF([test "x$COQC" = "xno"],
      [AC_MSG_ERROR([Could not find coqc])],
      [AC_MSG_CHECKING([coqc version])
       COQCVERSION="`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
       AC_MSG_RESULT([$COQCVERSION])
       AC_SUBST([COQCVERSION])
       AS_IF([test "x$COQCVERSION" != "x$COQVERSION"],
             [AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQCVERSION])])
      ])

# Should we compile ssrfelect?
compile_ssreflect="no"
AC_ARG_WITH([ssreflect],
            [AS_HELP_STRING([--with-ssreflect], [compile the ssreflect libary])],
            [compile_ssreflect="yes"],
            [])

AS_IF([test "x$compile_ssreflect" = "xno"],
      [AC_MSG_NOTICE([Will not compile ssreflect])],
      [AC_MSG_NOTICE([Will compile ssreflect])])
AM_CONDITIONAL(make_ssreflect, [test "x$compile_ssreflect" = "xyes"])
AC_SUBST([compile_ssreflect])

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
             [AC_PATH_PROG([COQIDE],[coqide],[no],[$COQBIN$PATH_SEPARATOR$PATH])])
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
      [AC_PATH_PROG([COQDEP],[coqdep],[no],[$COQBIN$PATH_SEPARATOR$PATH])])

AS_IF([test "x$COQDEP" = "xno"],
      [AC_MSG_ERROR([Could not find coqdep])])


# checking for coqdoc
AC_ARG_VAR([COQDOC], [the absolute path of the coqdoc executable])
AS_IF([test "x$COQDOC" != "x"],
      [AC_MSG_CHECKING([for coqdoc])
       AC_MSG_RESULT([(preset) $COQDOC])
       AC_SUBST([COQDOC])],
      [AC_PATH_PROG([COQDOC],[coqdoc],[no],[$COQBIN$PATH_SEPARATOR$PATH])])

AS_IF([test "x$COQDOC" = "xno"],
      [AC_MSG_ERROR([Could not find coqdoc])])

# checking for coq_makefile
AC_ARG_VAR([COQMAKEFILE], [the absolute path of the coq_makefile executable])
AS_IF([test "x$COQMAKEFILE" != "x"],
      [AC_MSG_CHECKING([for coq_makefile])
       AC_MSG_RESULT([(preset) $COQMAKEFILE])
       AC_SUBST([COQMAKEFILE])],
      [AC_PATH_PROG([COQMAKEFILE],[coq_makefile],[no],[$COQBIN$PATH_SEPARATOR$PATH])])

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
rm -f $srcdir/coq/plugins $srcdir/coq/dev
ln -s $COQLIB/plugins $COQLIB/dev $srcdir/coq
# TODO(jgross): Should we use AC_CONFIG_LINKS?  But $COQLIB/dev
# doesn't exist in my installation, and that would make configure
# error...
#AC_CONFIG_LINKS([$srcdir/coq/plugins:$COQLIB/plugins
#                 $srcdir/coq/dev:$COQLIB/dev])

AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoq-config])

AC_OUTPUT

# configure Coq

COQ_ARGS=()
AS_IF([test "x$exec_prefix" != xNONE],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -prefix "$exec_prefix")],
      [test "x$prefix" != xNONE],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -prefix "$prefix")],
      [COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -prefix "$ac_default_prefix")])
AS_IF([test "x$bindir" != x'${exec_prefix}/bin'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -bindir "$bindir")])
AS_IF([test "x$libdir" != x'${exec_prefix}/lib'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -libdir "$libdir")])
AS_IF([test "x$datadir" != x'${datarootdir}'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -datadir "$datadir")],
      [test "x$datarootdir" != x'${prefix}/share'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -datadir "$datarootdir")])
AS_IF([test "x$mandir" != x'${datarootdir}/man'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -mandir "$mandir")])
AS_IF([test "x$docdir" != x'${datarootdir}/doc/${PACKAGE_TARNAME}'],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -docdir "$docdir")])


AC_ARG_ENABLE([annotate],[AS_HELP_STRING([--enable-annotate],[Compiles Coq with -dtypes option])])
AS_IF([test "x$enable_annotate" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -annotate)])

AC_ARG_ENABLE([byte-only],[AS_HELP_STRING([--enable-byte-only],[Compiles only bytecode version of Coq])])
AS_IF([test "x$enable_byte_only" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -byte-only)])

AC_ARG_ENABLE([camlp4],[AS_HELP_STRING([--enable-camlp4],[Specifies to use camlp4 instead of camlp5])])
AS_IF([test "x$enable_camlp4" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -usecamlp4)])

AC_ARG_ENABLE([camlp5],[AS_HELP_STRING([--enable-camlp5],[Specifies to use camlp5 instead of camlp4])])
AS_IF([test "x$enable_camlp5" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -usecamlp5)])

AC_ARG_ENABLE([coqide],[AS_HELP_STRING([--enable-coqide=opt/byte/no],[Specifies whether or not to compile Coqide])])
AS_IF([test "x$enable_coqide" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqide "$enable_coqide")])

AC_ARG_ENABLE([custom],[AS_HELP_STRING([--enable-custom],[Generate all bytecode executables with -custom (not recommended)])])
AS_IF([test "x$enable_custom" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -custom)])

AC_ARG_ENABLE([debug],[AS_HELP_STRING([--enable-debug],[Add debugging information in the Coq executables])])
AS_IF([test "x$enable_debug" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -debug)])

AC_ARG_ENABLE([doc],[AS_HELP_STRING([--disable-doc],[Specifies to not compile the documentation])])
AS_IF([test "x$enable_doc" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -nodoc)])

AC_ARG_ENABLE([geoproof],[AS_HELP_STRING([--enable-geoproof],[Specifies whether or not to use Geoproof binding])])
AS_IF([test "x$enable_geoproof" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -with-geoproof no)],
      [test "x$enable_geoproof" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -with-geoproof yes)])

AC_ARG_ENABLE([macintegration],[AS_HELP_STRING([--disable-macintegration],[Specifies to not try to build coqide mac integration])])
AS_IF([test "x$enable_macintegration" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -nomacintegration)])

AC_ARG_ENABLE([natdynlink],[AS_HELP_STRING([--enable-natdynlink],[Specifies whether or not to use dynamic loading of native code])])
AS_IF([test "x$enable_natdynlink" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -natdynlink no)],
      [test "x$enable_natdynlink" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -natdynlink yes)])

AC_ARG_ENABLE([native-compiler],[AS_HELP_STRING([--disable-native-compiler],[Disables compilation to native code for conversion and normalization])])
AS_IF([test "x$enable_native_compiler" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -no-native-compiler)])

AC_ARG_ENABLE([opt],[AS_HELP_STRING([--enable-opt],[Specifies whether or not to use OCaml *.opt optimized compilers])])
AS_IF([test "x$enable_opt" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -opt)])

AC_ARG_ENABLE([profile],[AS_HELP_STRING([--enable-profile],[Add profiling information in the Coq executables])])
AS_IF([test "x$enable_profile" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -profile)])

AC_ARG_ENABLE([typerex],[AS_HELP_STRING([--enable-typerex],[Compiles Coq using typerex wrapper])])
AS_IF([test "x$enable_typerex" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -typerex)])

AC_ARG_WITH([browser],[AS_HELP_STRING([--with-browser=COMMAND],[Use COMMAND to open URL %s])])
AS_IF([test "x$with_browser" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -browser "$with_browser")])

AC_ARG_WITH([caml],[AS_HELP_STRING([--with-caml=DIR],[Specifies the path to the OCaml library])])
AS_IF([test "x$with_caml" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -camldir "$with_caml")])

AC_ARG_WITH([camlp5],[AS_HELP_STRING([--with-camlp5=DIR],[Specifies where to look for the Camlp5 library and tells to use it])])
AS_IF([test "x$enable_camlp5" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -camlp5dir "$enable_camlp5")])

AC_ARG_WITH([coqdocdir],[AS_HELP_STRING([--with-coqdocdir=DIR],[Specifies where Coqdoc style files are to be installed])])
AS_IF([test "x$with_coqdocdir" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqdocdir "$with_coqdocdir")])

AC_ARG_WITH([coqrunbyteflags],[AS_HELP_STRING([--with-coqrunbyteflags=FLAGS],[Set link flags for VM-dependent bytecode (coqtop)])])
AS_IF([test "x$with_coqrunbyteflags" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqrunbyteflags "$with_coqrunbyteflags")])

AC_ARG_WITH([coqtoolsbyteflags],[AS_HELP_STRING([--with-coqtoolsbyteflags=FLAGS],[Set link flags for VM-independant bytecode (coqdep, coqdoc, ...)])])
AS_IF([test "x$with_coqtoolsbyteflags" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqtoolsbyteflags "$with_coqtoolsbyteflags")])

AC_ARG_WITH([emacslib],[AS_HELP_STRING([--with-emacslib=DIR],[Specifies where emacs files are to be installed])])
AS_IF([test "x$with_emacslib" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -emacslib "$with_emacslib")])

AC_ARG_WITH([lablgtk],[AS_HELP_STRING([--with-lablgtk=DIR],[Specifies the path to the Lablgtk library])])
AS_IF([test "x$with_lablgtk" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -lablgtkdir "$with_lablgtk")])

# Should we have an argument for this?
#-arch <arch>
#	Specifies the architecture

COQ_HOTT_DIR=`(cd coq-HoTT && pwd)`
AS_ECHO("=== configuring in coq-HoTT ($COQ_HOTT_DIR)")
(cd "$COQ_HOTT_DIR"; exec ./configure "${COQ_ARGS@<:@@@:>@}")
AS_ECHO("*Warning* To compile the system for a new architecture")
AS_ECHO("          don't forget to do a 'cd coq-HoTT; make clean' before './configure'.")
