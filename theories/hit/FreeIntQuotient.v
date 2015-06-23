(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import TruncType HProp HSet.
Require Import Spaces.Int.
Require Import hit.Coeq hit.Circle hit.Flattening hit.Connectedness hit.Truncations.
Import TrM.

Local Open Scope path_scope.

(** * Quotients by free actions of [Int] *)

(** We will show that if [Int] acts freely on a set, then the set-quotient of that action can be defined without a 0-truncation, giving it a universal property for mapping into all types. *)

Section FreeIntAction.

  Context `{Univalence}.
  Context (R : Type) `{IsHSet R}.

  (** A free action by [Int] is the same as a single autoequivalence [f] (the action of [1]) whose iterates are all pointwise distinct. *)
  Context (f : R <~> R)
          (f_free : forall (r : R) (n m : Int),
                      (iter_int f n r = iter_int f m r) -> (n = m)).

  (** We can then define the quotient to be the coequalizer of [f] and the identity map.  This gives it the desired universal property for all types; it remains to show that this definition gives a set. *)
  Let RmodZ := Coeq f idmap.

  (** Together, [R] and [f] define a fibration over [S1].  By the flattening lemma, its total space is equivalent to the quotient. *)
  Global Instance isset_RmodZ : IsHSet RmodZ.
  Proof.
    refine (trunc_equiv'
              { z : S1 & S1_rec Type R (path_universe f) z}
              (_ oE (@equiv_flattening _ Unit Unit idmap idmap
                                  (fun _ => R) (fun _ => f))^-1
              oE _));
    try exact _.
    - erapply equiv_adjointify.
      + refine (Wtil_rec _ _ _).
        * intros u r; exact (coeq r).
        * intros u r; cbn. exact ((cp r)^).
      + refine (Coeq_rec _ _ _).
        * exact (cct tt).
        * intros r; exact ((ppt tt r)^).
      + refine (Coeq_ind _ (fun a => 1) _); cbn; intros b.
        rewrite transport_paths_FlFr, concat_p1, ap_idmap.
        apply moveR_Vp; rewrite concat_p1.
        rewrite ap_compose.
        rewrite (Coeq_rec_beta_cp
                   (Wtil Unit Unit idmap idmap (unit_name R) (unit_name f))
                   (cct tt) (fun r => (ppt tt r)^) b).
        rewrite ap_V; symmetry.
        refine (inverse2
                  (Wtil_rec_beta_ppt
                     RmodZ (unit_name (fun r => coeq r))
                     (unit_name (fun r => (cp r)^)) tt b) @ inv_V _).
      + refine (Wtil_ind _ _ _); cbn.
        { intros [] ?; reflexivity. }
        intros [] r; cbn.
        rewrite transport_paths_FlFr, concat_p1, ap_idmap.
        apply moveR_Vp; rewrite concat_p1.
        rewrite ap_compose.
        refine (_ @ ap (ap _) (Wtil_rec_beta_ppt
                   RmodZ (unit_name (fun r => coeq r))
                   (unit_name (fun r => (cp r)^)) tt r)^).
        rewrite ap_V.
        rewrite (Coeq_rec_beta_cp
                   (Wtil Unit Unit idmap idmap (unit_name R) (unit_name f))
                   (cct tt) (fun r0 : R => (ppt tt r0)^) r).
        symmetry; apply inv_V.
    - refine (equiv_functor_sigma' 1 _); intros x.
      apply equiv_path.
      revert x; refine (S1_ind _ 1 _); cbn.
      rewrite transport_paths_FlFr, concat_p1.
      apply moveR_Vp; rewrite concat_p1.
      rewrite S1_rec_beta_loop.
      unfold loop.
      exact (Coeq_rec_beta_cp _ _ _ _).
    - intros xu yv.
      refine (trunc_equiv' (n := -1) _ (equiv_path_sigma _ xu yv)).
      destruct xu as [x u], yv as [y v]; cbn.
      apply hprop_allpath.
      intros [p r] [q s].
      set (P := S1_rec Type R (path_universe f)) in *.
      assert (forall z, IsHSet (P z)).
      { refine (S1_ind _ _ _).
        - exact _.
        - apply path_ishprop. }
      apply path_sigma_hprop; cbn.
      assert (t := r @ s^); clear r s.
      assert (xb := merely_path_is0connected S1 base x).
      assert (yb := merely_path_is0connected S1 base y).
      strip_truncations. destruct xb, yb.
      revert p q t.
      equiv_intro (equiv_loopS1_int^-1) n.
      equiv_intro (equiv_loopS1_int^-1) m.
      subst P.
      rewrite !S1_action_is_iter.
      intros p. apply ap.
      exact (f_free u n m p).
  Qed.

  (** TODO: Prove that this [RmodZ] is equivalent to the set-quotient of [R] by a suitably defined equivalence relation. *)

End FreeIntAction.
