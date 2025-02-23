(** * Notations for comma categories *)
Require Import Basics.Notations.
Require Comma.Core.

Local Set Warnings "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Include Comma.Core.CommaCoreNotations.
