(* -*- mode: coq; mode: visual-line -*-  *)
(** * Propositional resizing *)

Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext HProp.
Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Class PropResizing.
Axiom resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A}, Type@{j}.
Axiom equiv_resize_hprop : forall `{PropResizing} (A : Type@{i}) `{IsHProp A},
    A <~> resize_hprop A.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := trunc_equiv A (equiv_resize_hprop A).

(** ** Impredicative propositional truncation. *)

(** We put it in a module so that it doesn't conflict with the HIT one
if that is also assumed. *)
Module Impredicative_Merely.
Section AssumePropResizing.
  Context `{PropResizing}.

  Definition merely (A : Type@{i}) : Type@{i}
    := forall P:Type@{j}, IsHProp P -> (A -> P) -> P.

  Definition trm {A} : A -> merely A
    := fun a P HP f => f a.

  Global Instance ishprop_merely `{Funext} (A : Type) : IsHProp (merely A).
  Proof.
    exact _.
  Defined.

  Definition merely_rec {A : Type@{i}} {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : merely A -> P
    := fun ma => (equiv_resize_hprop P)^-1
                 (ma (resize_hprop P) _ (equiv_resize_hprop P o f)).

  Definition functor_merely `{Funext} {A B : Type} (f : A -> B)
    : merely A -> merely B.
  Proof.
    srefine (merely_rec (trm o f)).
  Defined.

End AssumePropResizing.
End Impredicative_Merely.
