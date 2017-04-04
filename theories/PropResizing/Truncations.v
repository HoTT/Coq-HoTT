(* -*- mode: coq; mode: visual-line -*-  *)
(** * Impredicative truncations. *)

Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext HProp.
Require Import PropResizing.PropResizing.
Local Open Scope path_scope.

(* Be careful about [Import]ing this file!  It defines truncations
with the same name as those constructed with HITs.  Probably you want
to use those instead, if you are using HITs. *)

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
