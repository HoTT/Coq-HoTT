Require Import Basics.
Require Import WildCat.Core.


Declare Scope pointedcat_scope.
Local Open Scope pointedcat_scope.

(** A wild category is pointed if the initial and terminal object are the same. *)
Class IsPointedCat (A : Type) `{Is1Cat A} := {
  zero_object : A;
  isinitial_zero_object : IsInitial zero_object;
  isterminal_zero_object : IsTerminal zero_object;
}.

Global Existing Instance isinitial_zero_object.
Global Existing Instance isterminal_zero_object.

(** The zero morphism between objects [a] and [b] of a pointed category [A] is the unique morphism that factors throguh the zero object. *)
Definition zero_morphism {A : Type} `{IsPointedCat A} {a b : A} : a $-> b
  := (isinitial_zero_object b).1 $o (isterminal_zero_object a).1.

Notation "0" := zero_morphism : pointedcat_scope.

Section ZeroLaws.

  Context {A : Type} `{IsPointedCat A} {a b c : A}
    (f : a $-> b) (g : b $-> c).

  Local Arguments zero_morphism {_ _ _ _ _} _ _.

  Definition cat_zero_source (h : zero_object $-> a) : h $== 0
    := (isinitial_zero_object a).2 h
      $@ ((isinitial_zero_object a).2 0)^$.

  Definition cat_zero_target (h : a $-> zero_object) : h $== 0
    := (isterminal_zero_object a).2 h
      $@ ((isterminal_zero_object a).2 0)^$.

  Definition cat_zero_l : 0 $o f $== zero_morphism a c.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cat_postwhisker, (isterminal_zero_object a).2.
  Defined.

  Definition cat_zero_r : g $o 0 $== zero_morphism a c.
  Proof.
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_prewhisker, (isinitial_zero_object c).2.
  Defined.

End ZeroLaws.

