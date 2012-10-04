dnl autoconf macros for Coq
dnl
dnl Adapted from ocaml.m4 see LICENSE-ocaml.m4 for copyright and licensing.
dnl
dnl Copyright © 2009      Richard W.M. Jones
dnl Copyright © 2009      Stefano Zacchiroli
dnl Copyright © 2000-2005 Olivier Andrieu
dnl Copyright © 2000-2005 Jean-Christophe Filliâtre
dnl Copyright © 2000-2005 Georges Mariano
dnl
dnl For documentation, please read the ocaml.m4 man page.

AC_DEFUN([AC_PROG_COQ],
[dnl

  # checking for coqtop
  AC_CHECK_TOOL([COQTOP],[coqtop],[no])

  if test "$COQTOP" != "no"; then
     COQVERSION=`$COQTOP -v | sed -n -e 's|.*version *\([^ ]*\) .*$|\1|p'`
     AC_MSG_RESULT([Coq version is $COQVERSION])
     # If COQLIB is set, use it
     if test "$COQLIB" = ""; then
        COQLIB=`$COQTOP -where 2>/dev/null`
     else
        AC_MSG_RESULT([COQLIB previously set; preserving it.])
     fi
     AC_MSG_RESULT([Coq library path is $COQLIB])

     AC_SUBST([COQVERSION])
     AC_SUBST([COQLIB])

     # checking for coqc
     AC_CHECK_TOOL([COQC],[coqc],[no])
     if test "$COQC" != "no"; then
         TMPVERSION=`$COQC -v | sed -n -e 's|.*version *\([^ ]*\) .*$|\1|p'`
         if test "$TMPVERSION" != "$COQVERSION"; then
             AC_MSG_RESULT([version differs from coqop, coqc is discarded.])
             COQC=no
         fi
     fi

     AC_SUBST([COQC])
  fi
 
  # checking for coqdep
  AC_CHECK_TOOL([COQDEP],[coqdep],[no])
  AC_SUBST([COQDEP])

  # checking for coqdoc
  AC_CHECK_TOOL([COQDOC],[coqdoc],[no])
  AC_SUBST([COQDOC])
])
