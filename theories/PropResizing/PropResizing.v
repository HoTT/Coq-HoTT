Require Import Basics.Overture Basics.Tactics Basics.Trunc Basics.Equivalences
  Types.Universe Nat.Core.

Set Universe Minimization ToSet.

(** * Propositional resizing *)

Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

(** Mark this axiom as a "global axiom", which some of our tactics will automatically handle. *)
Global Instance is_global_axiom_propresizing : IsGlobalAxiom PropResizing := {}.

(** Propositional resizing says that every (-1)-truncated type is small. *)
Axiom issmall_hprop@{i j | } : forall `{PropResizing} (X : Type@{j})
  (T : IsHProp X), IsSmall@{i j} X.

(** TODO: inline and remove *)
Definition resize_hprop@{j i | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : Type@{i}
  := smalltype@{i j} (issmall_hprop@{i j} A _).

(** TODO: inline and remove *)
Definition equiv_resize_hprop@{j i | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : A <~> resize_hprop A
  := (equiv_smalltype@{i j} (issmall_hprop@{i j} A _))^-1%equiv.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := istrunc_equiv_istrunc A (equiv_resize_hprop A).
