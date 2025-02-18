Require Import Basics Types.Sigma Truncations.Core Modalities.Modality.

(** * Definition of a map by factoring through a surjection. *)

Section surjective_factor.
  Context `{Funext}. (* Can [Funext] be avoided? *)
  Context {A B C} `{IsHSet C} `(f : A -> C) `(g : A -> B) {Esurj : IsSurjection g}.
  Variable (Eg : forall x y, g x = g y -> f x = f y).

  (** We first define a (dependent) function from [B] to a type that we'll show is a proposition. *)
  Definition surjective_factor_aux : forall b : B, {c : C & forall a : A, b = g a -> c = f a}.
  Proof.
    apply (conn_map_elim _ g).
    - intro b. apply ishprop_sigma_disjoint.
      intros c1 c2.
      rapply (conn_map_elim _ g _ _ b).
      intros a E1 E2.
      path_via (f a).
    - intro a.
      exact (f a; Eg a).
  Defined.

  Definition surjective_factor : B -> C
    := fun b => (surjective_factor_aux b).1.

  Lemma surjective_factor_pr : surjective_factor o g == f.
  Proof.
    intros a.
    by apply (surjective_factor_aux (g a)).2.
  Defined.

End surjective_factor.
