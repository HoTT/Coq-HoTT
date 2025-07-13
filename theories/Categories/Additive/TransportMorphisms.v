(** * Transport lemmas for morphisms in categories

    Lemmas for transporting morphisms along equality proofs, essential for
    proving preservation properties of functors.

    These lemmas are primarily used in AdditiveCategories.v to prove that
    additive functors preserve zero morphisms.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category.

Section TransportMorphisms.
  Context {C : PreCategory}.

  (** Transport distributes over composition. *)
  Lemma transport_compose_morphism {X Y Z W : object C} (p : X = W)
    (f : morphism C X Y) (g : morphism C Y Z)
    : transport (fun U => morphism C U Z) p (g o f)%morphism =
      (g o transport (fun U => morphism C U Y) p f)%morphism.
  Proof.
    destruct p; reflexivity.
  Qed.

  (** Composing transported morphisms along inverse paths. *)
  Lemma transport_compose_both_inverse {W X Y Z : object C} (p : W = X)
    (f : morphism C W Z) (g : morphism C Y W)
    : (transport (fun U : object C => morphism C U Z) p f o
       transport (fun U : object C => morphism C Y U) p g)%morphism =
      (f o g)%morphism.
  Proof.
    destruct p; reflexivity.
  Qed.

  (** Convert equations with transport to equations with inverse transport. *)
  Lemma transport_inverse_eq {A : Type} {P : A -> Type}
    {x y : A} (p : x = y) (u : P x) (v : P y)
    : transport P p u = v -> u = transport P p^ v.
  Proof.
    intro H.
    rewrite <- H.
    destruct p; reflexivity.
  Qed.

  (** Specialized version for morphisms. *)
  Lemma morphism_eq_transport_inverse {W X Y : object C} (p : W = X)
    (f : morphism C W Y) (g : morphism C X Y)
    : transport (fun Z => morphism C Z Y) p f = g ->
      f = transport (fun Z => morphism C Z Y) p^ g.
  Proof.
    intro H.
    rewrite <- H.
    destruct p; reflexivity.
  Qed.

End TransportMorphisms.
