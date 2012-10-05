dnl autoconf macros for Coq
AC_DEFUN([AC_PROG_COQ],
[dnl

  # checking for coqtop
  AC_CHECK_TOOL([COQTOP],[coqtop],[no])

  if test "$COQTOP" != "no"; then
     COQVERSION=`$COQTOP -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
     AC_MSG_RESULT([Coq version is $COQVERSION.])
     # If COQLIB is set, use it
     if test "$COQLIB" = ""; then
        COQLIB=`$COQTOP -where 2>/dev/null`
     else
        AC_MSG_RESULT([COQLIB previously set; preserving it.])
     fi
     AC_MSG_RESULT([Coq library path is $COQLIB])

     AC_SUBST([COQVERSION])
     AC_SUBST([COQLIB])
  fi


  AC_CHECK_TOOL([COQC],[coqc],[no])
  if test "$COQC" != "no"; then
    COQCVERSION=`$COQC -v | sed -n -e 's|^.*version \(@<:@^ @:>@*\) .*$|\1|p'`
    AC_MSG_RESULT([Coqc version is $TMPVERSION.])
    AC_SUBST([COQCVERSION])
  fi
 
  # checking for coqdep
  AC_PATH_TOOL([COQDEP],[coqdep],[no])

  # checking for coqdoc
  AC_PATH_TOOL([COQDOC],[coqdoc],[no])
])
