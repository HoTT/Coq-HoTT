Require Import Basics Types Colimits.Pushout Colimits.Colimit_Pushout Colimits.Colimit_Pushout_Flattening.

(** * Flattening for pushouts *)

(** We derrive flattening for pushouts using the flattening lemma for colimits. Most of the work has already been done, what is left is to transport the result along the appropriate equivalences. *)

Section Flattening.
  Context `{Univalence} {A B C} {f : A -> B} {g : A -> C}.

  Context (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Definition POCase_P : Pushout f g -> Type.
  Proof.
    nrefine (Pushout_rec Type B0 C0 _).
    cbn; intro x.
    snrapply path_universe.
    1: exact ((g0 x) oE (f0 x)^-1%equiv).
    exact _.
  Defined.

  Definition PO_flattening
    : Pushout (functor_sigma f f0) (functor_sigma g g0) <~> exists x, POCase_P x.
  Proof.
    snrefine (_ oE equiv_pushout_PO). 
    snrefine (_ oE PO_flattening A0 B0 C0 f0 g0).
    symmetry.
    snrapply equiv_functor_sigma'.
    1: apply equiv_pushout_PO.
    (** Proving that the type families are equivalent takes some work but is mostly trivial. We don't know how to transport over families of equivlences yet, so we use univalence to turn it into a transportation over a family of paths. *)
    snrapply Pushout_ind.
    1,2: hnf; reflexivity.
    intros a.
    hnf.
    lhs nrapply transport_idmap_ap.
    unshelve erewrite ap_homotopic.
    2: {
      intros w.
      rapply path_universe_uncurried.
      apply equiv_path_universe. }
    rewrite 2 transport_pp.
    rewrite transport_path_universe_uncurried.
    rewrite transport_path_universe_V.
    apply moveR_equiv_V.
    change (?x = path_universe_uncurried 1) with (x = path_universe equiv_idmap).
    rewrite path_universe_1.
    lhs nrapply (transport_idmap_ap _ _ _)^.
    rewrite transport_paths_FlFr.
    rewrite Pushout_rec_beta_pglue.
    rewrite concat_pp_p.
    apply moveR_Vp.
    rewrite concat_p1.
    rewrite ap_compose.
    rewrite Pushout_rec_beta_pglue.
    unfold popp'.
    simpl.
    rewrite 2 concat_1p.
    change(path_universe 1%equiv @
      ap (Colimit_Pushout_Flattening.POCase_P A0 B0 C0 f0 g0)
      (popp a) = path_universe (g0 a oE (f0 a)^-1)).
    rewrite PO_rec_beta_pp.
    rewrite path_universe_1.
    rewrite concat_1p.
    reflexivity.
  Defined.

End Flattening.
