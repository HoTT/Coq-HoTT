dnl This file is used by autoconf to generate the configure script
dnl by the HoTT development team. Unless you already know what the
dnl things below mean, you probably do not want to touch anything.

AC_INIT([hott],[1.0])
AC_PREREQ([2.67])
AC_CONFIG_SRCDIR([theories/Overture.v])
AC_CONFIG_AUX_DIR([etc])
AC_CONFIG_MACRO_DIR([etc])
AM_MAINTAINER_MODE([enable])
AM_INIT_AUTOMAKE([foreign no-dependencies])

# Check for programs
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AC_PROG_MKDIR_P

# Check to see if COQBIN was set
AC_ARG_VAR([COQBIN], [the directory which contains the Coq executables @<:@BINDIR@:>@])
# we are using the bundled coq only if the user does not pass COQBIN
AM_CONDITIONAL([BUNDLE_COQ], [test "x$COQBIN" = x])
# use 'test "x$foo" != "x"' rather than 'test -n "$foo"' as per
# http://www.gnu.org/software/automake/manual/autoconf.html#Limitations-of-Builtins;
# some shells get confused if $foo is a weird character like '!' or
# '-n'
AS_IF([test "x$COQBIN" != "x"],
      [AC_MSG_NOTICE([Will look for Coq executables in $COQBIN])
       COQTOP="$COQBIN/coqtop"
       COQIDE="$COQBIN/coqide"
       COQC="$COQBIN/coqc"
       COQDEP="$COQBIN/coqdep"
       COQDOC="$COQBIN/coqdoc"
       COQMAKEFILE="$COQBIN/coq_makefile"

       # checking for coqtop
       AC_MSG_CHECKING([for an executable coqtop in $COQBIN which supports -indices-matter])
       AS_IF([test ! -x "$COQTOP"],
              [AC_MSG_RESULT([no])
               AC_MSG_ERROR([Could not find executable coqtop in $COQBIN])],
             [test "`$COQTOP -help 2>&1 | grep -c -- -indices-matter`" = "0"],
              [AC_MSG_RESULT([does not support -indices-matter])
               AC_MSG_ERROR([You need a version of Coq which supports -indices-matter])],
             [AC_MSG_RESULT([yes])])
       AC_MSG_CHECKING([coqtop version])
       COQVERSION="`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
       AC_MSG_RESULT([$COQVERSION])

       # checking for coqc
       AC_MSG_CHECKING([for an executable coqc in $COQBIN])
       AS_IF([test ! -x "$COQC"],
             [AC_MSG_RESULT([no])
              AC_MSG_ERROR([Could not find executable coqc in $COQBIN])],
             [AC_MSG_RESULT([yes])])
       AC_MSG_CHECKING([coqc version])
       COQCVERSION="`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`"
       AC_MSG_RESULT([$COQCVERSION])
       AS_IF([test "x$COQCVERSION" != "x$COQVERSION"],
             [AC_MSG_ERROR([Version mismatch between coqtop $COQVERSION and coqc $COQCVERSION])])

       # checking for coqdep
       AC_MSG_CHECKING([for an executable coqdep in $COQBIN])
       AS_IF([test ! -x "$COQDEP"],
             [AC_MSG_RESULT([no])
              AC_MSG_ERROR([Could not find executable coqdep in $COQBIN])]
             [AC_MSG_RESULT([yes])])

       # checking for coqdoc
       AC_MSG_CHECKING([for an executable coqdoc in $COQBIN])
       AS_IF([test ! -x "$COQDOC"],
             [AC_MSG_RESULT([no])
              AC_MSG_ERROR([Could not find executable coqdoc in $COQBIN])],
             [AC_MSG_RESULT([yes])])

       # checking for coq_makefile
       AC_MSG_CHECKING([for an executable coq_makefile in $COQBIN])
       AS_IF([test ! -x "$COQMAKEFILE"],
             [AC_MSG_RESULT([no])
              AC_MSG_ERROR([Could not find executable coq_makefile in $COQBIN])],
             [AC_MSG_RESULT([yes])])
      ],
      [COQBIN="$bindir"
       COQTOP="$bindir/coqtop"
       COQIDE="$bindir/coqide"
       COQC="$bindir/coqc"
       COQDEP="$bindir/coqdep"
       COQDOC="$bindir/coqdoc"
       COQMAKEFILE="$bindir/coq_makefile"])

AC_SUBST([COQBIN])
AC_SUBST([COQTOP])
AC_SUBST([COQIDE])
AC_SUBST([COQC])
AC_SUBST([COQDEP])
AC_SUBST([COQDOC])
AC_SUBST([COQMAKEFILE])

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

hottdir="$datarootdir/hott"
AC_SUBST([hottdir])

AC_CHECK_PROGS(ETAGS,etags,[: skipping etags])

AC_ARG_VAR([TIME], [the absolute path of a 'time' command])
AC_PATH_PROG([TIME],[time],[no])
AS_IF([test "x$TIME" = "xno"],
      [STDTIME=""],
      [STDTIME="\"$TIME\" -f \"\$* (user: %U mem: %M ko)\""])
AC_SUBST([STDTIME])

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

AC_ARG_WITH([browser],[AS_HELP_STRING([--with-browser=COMMAND],[Use COMMAND to open URL %s])])
AS_IF([test "x$with_browser" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -browser "$with_browser")])

AC_ARG_ENABLE([byte-only],[AS_HELP_STRING([--enable-byte-only],[Compiles only bytecode version of Coq])])
AS_IF([test "x$enable_byte_only" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -byte-only)])

AC_ARG_WITH([caml],[AS_HELP_STRING([--with-caml=DIR],[Specifies the path to the OCaml library])])
AS_IF([test "x$with_caml" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -camldir "$with_caml")])

AC_ARG_ENABLE([camlp4],[AS_HELP_STRING([--enable-camlp4],[Specifies to use camlp4 instead of camlp5])])
AS_IF([test "x$enable_camlp4" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -usecamlp4)])

AC_ARG_ENABLE([camlp5],[AS_HELP_STRING([--enable-camlp5],[Specifies to use camlp5 instead of camlp4])])
AS_IF([test "x$enable_camlp5" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -usecamlp5)])

AC_ARG_WITH([camlp5],[AS_HELP_STRING([--with-camlp5=DIR],[Specifies where to look for the Camlp5 library and tells to use it])])
AS_IF([test "x$enable_camlp5" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -camlp5dir "$enable_camlp5")])

AC_ARG_WITH([coqdocdir],[AS_HELP_STRING([--with-coqdocdir=DIR],[Specifies where Coqdoc style files are to be installed])])
AS_IF([test "x$with_coqdocdir" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqdocdir "$with_coqdocdir")])

AC_ARG_WITH([coqide],[AS_HELP_STRING([--with-coqide=opt/byte/no],[Specifies whether or not to compile Coqide])])
AS_IF([test "x$with_coqide" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqide "$with_coqide")])

AC_ARG_WITH([coqrunbyteflags],[AS_HELP_STRING([--with-coqrunbyteflags=FLAGS],[Set link flags for VM-dependent bytecode (coqtop)])])
AS_IF([test "x$with_coqrunbyteflags" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqrunbyteflags "$with_coqrunbyteflags")])

AC_ARG_WITH([coqtoolsbyteflags],[AS_HELP_STRING([--with-coqtoolsbyteflags=FLAGS],[Set link flags for VM-independant bytecode (coqdep, coqdoc, ...)])])
AS_IF([test "x$with_coqtoolsbyteflags" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -coqtoolsbyteflags "$with_coqtoolsbyteflags")])

AC_ARG_ENABLE([custom],[AS_HELP_STRING([--enable-custom],[Generate all bytecode executables with -custom (not recommended)])])
AS_IF([test "x$enable_custom" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -custom)])

AC_ARG_ENABLE([debug],[AS_HELP_STRING([--enable-debug],[Add debugging information in the Coq executables])])
AS_IF([test "x$enable_debug" = xyes],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -debug)])

AC_ARG_ENABLE([doc],[AS_HELP_STRING([--disable-doc],[Specifies to not compile the documentation])])
AS_IF([test "x$enable_doc" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -nodoc)])

AC_ARG_WITH([emacslib],[AS_HELP_STRING([--with-emacslib=DIR],[Specifies where emacs files are to be installed])])
AS_IF([test "x$with_emacslib" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -emacslib "$with_emacslib")])

AC_ARG_ENABLE([geoproof],[AS_HELP_STRING([--enable-geoproof],[Specifies whether or not to use Geoproof binding])])
AS_IF([test "x$enable_geoproof" = xno],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -with-geoproof no)],
      [test "x$enable_geoproof" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -with-geoproof yes)])

AC_ARG_WITH([lablgtk],[AS_HELP_STRING([--with-lablgtk=DIR],[Specifies the path to the Lablgtk library])])
AS_IF([test "x$with_lablgtk" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -lablgtkdir "$with_lablgtk")])

AC_ARG_WITH([lablgtk],[AS_HELP_STRING([--with-lablgtk=DIR],[Specifies the path to the Lablgtk library])])
AS_IF([test "x$with_lablgtk" != x],[COQ_ARGS=("${COQ_ARGS@<:@@@:>@}" -lablgtkdir "$with_lablgtk")])

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

# Should we have an argument for this?
#-arch <arch>
#	Specifies the architecture


AM_CONDITIONAL(make_hoqide, [test "x$with_coqide" != xno])
AM_CONDITIONAL(make_hoqtopbyte, [true]) #test -x "$COQTOP.byte"])
AC_CONFIG_FILES([Makefile])
AC_CONFIG_FILES([hoq-config])

AC_OUTPUT

COQ_HOTT_DIR=`(cd coq-HoTT && pwd)`
AS_ECHO("=== configuring in coq-HoTT ($COQ_HOTT_DIR)")
echo "configure ${COQ_ARGS@<:@@@:>@}"
(cd "$COQ_HOTT_DIR"; exec ./configure "${COQ_ARGS@<:@@@:>@}")
AS_ECHO("*Warning* To compile the system for a new architecture")
AS_ECHO("          don't forget to do a 'cd coq-HoTT; make clean' before './configure'.")
