Require Import Basics.Overture Basics.Tactics.

Set Universe Minimization ToSet.

(** * Propositional resizing *)

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

(** Mark this axiom as a "global axiom", which some of our tactics will automatically handle. *)
Global Instance is_global_axiom_propresizing : IsGlobalAxiom PropResizing := {}.

(** Propositional resizing says that every (-1)-truncated type is small. *)
Axiom issmall_hprop@{i j | } : forall `{PropResizing} (X : Type@{j})
  (T : IsHProp X), IsSmall@{i j} X.
Existing Instance issmall_hprop.
