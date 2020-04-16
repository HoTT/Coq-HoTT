Require Import Basics.
Require Import WildCat.Core.


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

Section ZeroLaws.

  Context {A : Type} `{IsPointedCat A} {a b c : A}
    (f : a $-> b) (g : b $-> c).

  Definition cat_zero_source (h : zero_object $-> a) : h $== zero_morphism
    := (isinitial_zero_object a).2 h
      $@ ((isinitial_zero_object a).2 zero_morphism)^$.

  Definition cat_zero_target (h : a $-> zero_object) : h $== zero_morphism
    := (isterminal_zero_object a).2 h
      $@ ((isterminal_zero_object a).2 zero_morphism)^$.

  Local Arguments zero_morphism {_ _ _ _ _} _ _.

  Definition cat_zero_l : zero_morphism b c $o f $== zero_morphism a c.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cat_postwhisker, (isterminal_zero_object a).2.
  Defined.

  Definition cat_zero_r : g $o zero_morphism a b $== zero_morphism a c.
  Proof.
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_prewhisker, (isinitial_zero_object c).2.
  Defined.

End ZeroLaws.

