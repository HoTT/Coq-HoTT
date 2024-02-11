Require Import Basics Types Colimits.Pushout Colimits.Colimit_Pushout Colimits.Colimit_Pushout_Flattening.

(** * Flattening for pushouts *)

(** We derive flattening for pushouts using the flattening lemma for colimits. Most of the work has already been done. What is left is to transport the result along the appropriate equivalences. *)

Section Flattening.
  Context `{Univalence} {A B C} {f : A -> B} {g : A -> C}
    (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
    (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Definition pushout_flattening_fam : Pushout f g -> Type.
  Proof.
    nrefine (Pushout_rec Type B0 C0 _).
    cbn; intro x.
    snrapply path_universe.
    1: exact ((g0 x) o (f0 x)^-1).
    exact _.
  Defined.

  Definition pushout_flattening
    : Pushout (functor_sigma f f0) (functor_sigma g g0)
      <~> exists x, pushout_flattening_fam x.
  Proof.
    snrefine (_ oE equiv_pushout_PO). 
    snrefine (_ oE PO_flattening A0 B0 C0 f0 g0).
    symmetry.
    snrapply equiv_functor_sigma'.
    1: apply equiv_pushout_PO.
    intro x.
    apply equiv_path.
    nrapply Pushout_rec_PO_rec.
  Defined.

End Flattening.
