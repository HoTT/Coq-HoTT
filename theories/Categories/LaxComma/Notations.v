(** * Notations for lax comma categories *)
Require HoTT.Categories.LaxComma.Core.

Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Include LaxComma.Core.LaxCommaCoreNotations.
