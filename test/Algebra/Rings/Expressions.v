From HoTT Require Import Basics.Overture Algebra.Rings.Ring.

Set Universe Minimization ToSet.

(** In this file, we test various aspects of writing group expressions. These kinds of expressions appear throughout the library, but since mathclasses is quite sensitive to subtle changes, we keep this file to document and enforce certain behaviours.

We use the [Type] vernacular command which is like [Check] but doesn't allow for evars. *)

Section Rings.

  Context {R : Ring@{Set}} (x y : R).

  (** [mc_scope] is appropriate for rings. *)

  Local Open Scope mc_scope.

  Succeed Type (x + y : R).
  Succeed Type (x - y : R).
  Succeed Type (x * y * x - x * y : R).
  Succeed Type (x - y : R).
  Succeed Type (x - y : R).

  Local Close Scope mc_scope.
End Rings.
