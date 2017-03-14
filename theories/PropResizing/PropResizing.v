(* -*- mode: coq; mode: visual-line -*-  *)
(** * Propositional resizing *)

Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext HProp.
Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.
Axiom resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A}, Type@{j}.
Axiom equiv_resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A},
    A <~> resize_hprop A.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := trunc_equiv A (equiv_resize_hprop A).
