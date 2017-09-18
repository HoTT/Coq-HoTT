Require Import
        HoTT.Types.Arrow
        HoTT.Types.Universe
        HoTT.Basics
        HoTT.HIT.Truncations
        HoTT.HIT.unique_choice.

(** Definition by factoring through a surjection. *)

Section surjective_factor.
  Context `{Funext}.
  Context {A B C} `{IsHSet C} `(f : A -> C) `(g : A -> B) {Esurj : IsSurjection g}.
  Variable (Eg : forall x y, g x = g y -> f x = f y).

  Lemma ishprop_surjective_factor_aux : forall b, IsHProp (exists c : C, forall a, g a = b -> f a = c).
  Proof.
    intros. apply Sigma.ishprop_sigma_disjoint.
    intros c1 c2 E1 E2.
    generalize (center _ (Esurj b));apply (Trunc_ind _).
    intros [a p];destruct p.
    path_via (f a).
  Qed.

  Definition surjective_factor_aux :=
    @TrM.RSU.conn_map_elim
      _ _ _ _ Esurj (fun b => exists c : C, forall a, g a = b -> f a = c)
      ishprop_surjective_factor_aux
      (fun a => exist (fun c => forall a, _ -> _ = c) (f a) (fun a' => Eg a' a)).

  Definition surjective_factor : B -> C
    := fun b => (surjective_factor_aux b).1.

  Lemma surjective_factor_pr : f == compose surjective_factor g.
  Proof.
    intros a.
    apply (surjective_factor_aux (g a)).2. trivial.
  Qed.

End surjective_factor.
